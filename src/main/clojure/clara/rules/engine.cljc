(ns clara.rules.engine
  "This namespace is for internal use and may move in the future. Most users should use only the clara.rules namespace."
  (:require [clojure.reflect :as reflect]
            [clojure.core.reducers :as r]
            [schema.core :as s]
            [clojure.string :as string]
            [clara.rules.memory :as mem]
            [clara.rules.listener :as l]
            #?(:clj [clara.rules.platform :as platform]
               :cljs [clara.rules.platform :as platform :include-macros true])
            [clara.rules.update-cache.core :as uc]
            #?(:clj [clara.rules.update-cache.cancelling :as ca])))

;; The accumulator is a Rete extension to run an accumulation (such as sum, average, or similar operation)
;; over a collection of values passing through the Rete network. This object defines the behavior
;; of an accumulator. See the AccumulateNode for the actual node implementation in the network.
(defrecord Accumulator [initial-value retract-fn reduce-fn combine-fn convert-return-fn])

;; A Rete-style token, which contains two items:
;; * matches, a vector of [fact, node-id] tuples for the facts and corresponding nodes they matched.
;; NOTE:  It is important that this remains an indexed vector for memory optimizations as well as
;;        for correct conj behavior for new elements i.e. added to the end.
;; * bindings, a map of keyword-to-values for bound variables.
(defrecord Token [matches bindings])

;; A working memory element, containing a single fact and its corresponding bound variables.
(defrecord Element [fact bindings])

;; An activation for the given production and token.
(defrecord Activation [node token])

;; Token with no bindings, used as the root of beta nodes.
(def empty-token (->Token [] {}))

;; Record indicating the negation existing in the working memory.
;;
;; Determining if an object is an instance of a class is a primitive
;; JVM operation and is much more efficient than determining
;; if that object descends from a particular object through
;; Clojure's hierarchy as determined by the isa? function.
;; See Issue 239 for more details.
#?(:clj
    (do
      ;; A marker interface to identify internal facts.
      (definterface ISystemFact)
      (defrecord NegationResult [gen-rule-name ancestor-bindings]
        ISystemFact))

    :cljs
    (do
      (defrecord NegationResult [gen-rule-name ancestor-bindings])
      ;; Make NegationResult a "system type" so that NegationResult
      ;; facts are special-cased when matching productions. This serves
      ;; the same purpose as implementing the ISystemFact Java interface
      ;; on the Clojure version of NegationResult.
      ;; ClojureScript does not have definterface; if we experience performance
      ;; problems in ClojureScript similar to those on the JVM that are
      ;; described in issue 239 we can investigate a similar strategy in JavaScript.
      (derive NegationResult ::system-type)))

;; Schema for the structure returned by the components
;; function on the session protocol.
;; This is simply a comment rather than first-class schema
;; for now since it's unused for validation and created
;; undesired warnings as described at https://groups.google.com/forum/#!topic/prismatic-plumbing/o65PfJ4CUkI
(comment

  (def session-components-schema
    {:rulebase s/Any
     :memory s/Any
     :transport s/Any
     :listeners [s/Any]
     :get-alphas-fn s/Any}))

;; Returns a new session with the additional facts inserted.
(defprotocol ISession

  ;; Inserts facts.
  (insert [session facts])

  ;; Retracts facts.
  (retract [session facts])

  ;; Fires pending rules and returns a new session where they are in a fired state.
  ;;
  ;; Note that clara.rules/fire-rules, the public API for these methods, will handle
  ;; calling the two-arg fire-rules with an empty map itself, but we add handle it in the fire-rules implementation
  ;; as well in case anyone is directly calling the fire-rules protocol function or interface method on the LocalSession.
  ;; The two-argument version of fire-rules was added for issue 249.
  (fire-rules [session] [session opts])

  ;; Runs a query agains thte session.
  (query [session query params])

  ;; Returns the components of a session as defined in the session-components-schema
  (components [session]))

;; Left activation protocol for various types of beta nodes.
(defprotocol ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener])
  (left-retract [node join-bindings tokens memory transport listener])
  (description [node])
  (get-join-keys [node]))

;; Right activation protocol to insert new facts, connecting alpha nodes
;; and beta nodes.
(defprotocol IRightActivate
  (right-activate [node join-bindings elements memory transport listener])
  (right-retract [node join-bindings elements memory transport listener]))

;; Specialized right activation interface for accumulator nodes,
;; where the caller has the option of pre-reducing items
;; to reduce the data sent to the node. This would be useful
;; if the caller is not in the same memory space as the accumulator node itself.
(defprotocol IAccumRightActivate
  ;; Pre-reduces elements, returning a map of bindings to reduced elements.
  (pre-reduce [node elements])

  ;; Right-activate the node with items reduced in the above pre-reduce step.
  (right-activate-reduced [node join-bindings reduced  memory transport listener]))

(defprotocol IAccumInspect
  "This protocol is expected to be implemented on accumulator nodes in the rules network.
   It is not expected that users will implement this protocol, and most likely will not call
   the protocol function directly."
  (token->matching-elements [node memory token]
    "Takes a token that was previously propagated from the node, 
     or a token that is a descendant of such a token, and returns the facts in elements 
     matching the token propagated from the node.  During rules firing
     accumulators only propagate bindings created and the result binding
     downstream rather than all facts that were accumulated over, but there
     are use-cases in session inspection where we want to retrieve the individual facts.
    
     Example: [?min-temp <- (acc/min :temperature) :from [Temperature (= temperature ?loc)]]
              [?windspeed <- [WindSpeed (= location ?loc)]]
     
     Given a token propagated from the node for the WindSpeed condition 
     we could retrieve the Temperature facts from the matching location."))

;; The transport protocol for sending and retracting items between nodes.
(defprotocol ITransport
  (send-elements [transport memory listener nodes elements])
  (send-tokens [transport memory listener nodes tokens])
  (retract-elements [transport memory listener nodes elements])
  (retract-tokens [transport memory listener nodes tokens]))

(defn- propagate-items-to-nodes [transport memory listener nodes items propagate-fn]
  (doseq [node nodes
          :let [join-keys (get-join-keys node)]]

    (if (pos? (count join-keys))

      ;; Group by the join keys for the activation.
      (doseq [[join-bindings item-group] (platform/group-by-seq #(select-keys (:bindings %) join-keys) items)]
        (propagate-fn node
                      join-bindings
                      item-group
                      memory
                      transport
                      listener))

      ;; The node has no join keys, so just send everything at once
      ;; (if there is something to send.)
      (when (seq items)
        (propagate-fn node
                      {}
                      items
                      memory
                      transport
                      listener)))))

;; Simple, in-memory transport.
(deftype LocalTransport []
  ITransport
  (send-elements [transport memory listener nodes elements]
    (propagate-items-to-nodes transport memory listener nodes elements right-activate))

  (send-tokens [transport memory listener nodes tokens]
    (propagate-items-to-nodes transport memory listener nodes tokens left-activate))

  (retract-elements [transport memory listener nodes elements]
    (propagate-items-to-nodes transport memory listener nodes elements right-retract))

  (retract-tokens [transport memory listener nodes tokens]
    (propagate-items-to-nodes transport memory listener nodes tokens left-retract)))

;; Protocol for activation of Rete alpha nodes.
(defprotocol IAlphaActivate
  (alpha-activate [node facts memory transport listener])
  (alpha-retract [node facts memory transport listener]))

;; Protocol for getting the type (e.g. :production and :query) and name of a
;; terminal node.
(defprotocol ITerminalNode
  (terminal-node-type [this]))

;; Protocol for getting a node's condition expression.
(defprotocol IConditionNode
  (get-condition-description [this]))

(defn get-terminal-node-types
  [node]
  (->> node
       (tree-seq (comp seq :children) :children)
       (keep #(when (satisfies? ITerminalNode %)
                (terminal-node-type %)))
       (into (sorted-set))))

(defn get-conditions-and-rule-names
  "Returns a map from conditions to sets of rules."
  ([node]
   (if-let [condition (when (satisfies? IConditionNode node)
                           (get-condition-description node))]
     {condition (get-terminal-node-types node)}
     (->> node
         :children
         (map get-conditions-and-rule-names)
         (reduce (partial merge-with into) {})))))

;; Active session during rule execution.
(def ^:dynamic *current-session* nil)

;; Note that this can hold facts directly retracted and facts logically retracted
;; as a result of an external retraction or insertion.
;; The value is expected to be an atom holding such facts.
(def ^:dynamic *pending-external-retractions* nil)

;; The token that triggered a rule to fire.
(def ^:dynamic *rule-context* nil)

(defn ^:private external-retract-loop
  "Retract all facts, then group and retract all facts that must be logically retracted because of these
   retractions, and so forth, until logical consistency is reached.  When an external retraction causes multiple
  facts of the same type to be retracted in the same iteration of the loop this improves efficiency since they can be grouped.
  For example, if we have a rule that matches on FactA and inserts FactB, and then a later rule that accumulates on FactB,
  if we have multiple FactA external retractions it is more efficient to logically retract all the FactB instances at once to minimize the  number of times we must re-accumulate on FactB.
  This is similar to the function of the pending-updates in the fire-rules* loop."
  [get-alphas-fn memory transport listener]
  (loop []
    (let [retractions (deref *pending-external-retractions*)
          ;; We have already obtained a direct reference to the facts to be
          ;; retracted in this iteration of the loop outside the cache.  Now reset
          ;; the cache.  The retractions we execute may cause new retractions to be queued
          ;; up, in which case the loop will execute again.
          _ (reset! *pending-external-retractions* [])]
      (doseq [[alpha-roots fact-group] (get-alphas-fn retractions)
              root alpha-roots]
        (alpha-retract root fact-group memory transport listener))
      (when (-> *pending-external-retractions* deref not-empty)
        (recur)))))

(defn- flush-updates
  "Flush all pending updates in the current session. Returns true if there were
   some items to flush, false otherwise"
  [current-session]
  (letfn [(flush-all [current-session flushed-items?]
            (let [{:keys [rulebase transient-memory transport insertions get-alphas-fn listener]} current-session
                  pending-updates (-> current-session :pending-updates uc/get-updates-and-reset!)]

              (if (empty? pending-updates)
                flushed-items?
                (do
                  (doseq [partition pending-updates
                          :let [facts (mapcat :facts partition)]
                          [alpha-roots fact-group] (get-alphas-fn facts)
                          root alpha-roots]

                    (if (= :insert (:type (first partition)))
                      (alpha-activate root fact-group transient-memory transport listener)
                      (alpha-retract root fact-group transient-memory transport listener)))

                  ;; There may be new pending updates due to the flush just
                  ;; made.  So keep flushing until there are none left.  Items
                  ;; were flushed though, so flush-items? is now true.
                  (flush-all current-session true)))))]

    (flush-all current-session false)))

(defn insert-facts!
  "Place facts in a stateful cache to be inserted into the session
  immediately after the RHS of a rule fires."
  [facts unconditional]
  (if unconditional
    (swap! (:batched-unconditional-insertions *rule-context*) into facts)
    (swap! (:batched-logical-insertions *rule-context*) into facts)))

(defn rhs-retract-facts!
  "Place all facts retracted in the RHS in a buffer to be retracted after
   the eval'ed RHS function completes."
  [facts]
  (swap! (:batched-rhs-retractions *rule-context*) into facts))

(defn ^:private flush-rhs-retractions!
  "Retract all facts retracted in the RHS after the eval'ed RHS function completes.
  This should only be used for facts explicitly retracted in a RHS.
  It should not be used for retractions that occur as part of automatic truth maintenance."
  [facts]
  (let [{:keys [rulebase transient-memory transport insertions get-alphas-fn listener]} *current-session*
        {:keys [node token]} *rule-context*]
    ;; Update the count so the rule engine will know when we have normalized.
    (swap! insertions + (count facts))

    (when listener
      (l/retract-facts! listener node token facts))

    (doseq [[alpha-roots fact-group] (get-alphas-fn facts)
            root alpha-roots]

      (alpha-retract root fact-group transient-memory transport listener))))

(defn ^:private flush-insertions!
  "Perform the actual fact insertion, optionally making them unconditional.  This should only
   be called once per rule activation for logical insertions."
  [facts unconditional]
  (let [{:keys [rulebase transient-memory transport insertions get-alphas-fn listener]} *current-session*
        {:keys [node token]} *rule-context*]

    ;; Update the insertion count.
    (swap! insertions + (count facts))

    ;; Track this insertion in our transient memory so logical retractions will remove it.
    (if unconditional
      (l/insert-facts! listener node token facts)
      (do
        (mem/add-insertions! transient-memory node token facts)
        (l/insert-facts-logical! listener node token facts)))

    (-> *current-session* :pending-updates (uc/add-insertions! facts))))

(defn retract-facts!
  "Perform the fact retraction."
  [facts]
  (-> *current-session* :pending-updates (uc/add-retractions! facts)))

;; Record for the production node in the Rete network.
(defrecord ProductionNode [id production rhs]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]

    ;; Provide listeners information on all left-activate calls,
    ;; but we don't store these tokens in the beta-memory since the production-memory
    ;; and activation-memory collectively contain all information that ProductionNode
    ;; needs.  See https://github.com/cerner/clara-rules/issues/386
    (l/left-activate! listener node tokens)

    ;; Fire the rule if it's not a no-loop rule, or if the rule is not
    ;; active in the current context.
    (when (or (not (get-in production [:props :no-loop]))
              (not (= production (get-in *rule-context* [:node :production]))))

      (let [activations (platform/eager-for [token tokens]
                                            (->Activation node token))]

        (l/add-activations! listener node activations)

        ;; The production matched, so add the tokens to the activation list.
        (mem/add-activations! memory production activations))))

  (left-retract [node join-bindings tokens memory transport listener]

    ;; Provide listeners information on all left-retract calls for passivity,
    ;; but we don't store these tokens in the beta-memory since the production-memory
    ;; and activation-memory collectively contain all information that ProductionNode
    ;; needs.  See https://github.com/cerner/clara-rules/issues/386
    (l/left-retract! listener node tokens)

    ;; Remove pending activations triggered by the retracted tokens.
    (let [activations (platform/eager-for [token tokens]
                                          (->Activation node token))

          ;; We attempt to remove a pending activation for all tokens retracted, but our expectation
          ;; is that each token may remove a pending activation
          ;; or logical insertions from a previous rule activation but not both.
          ;; We first attempt to use each token to remove a pending activation but keep track of which
          ;; tokens were not used to remove an activation.
          [removed-activations unremoved-activations]
          (mem/remove-activations! memory production activations)

          _ (l/remove-activations! listener node removed-activations)

          unremoved-tokens (mapv :token unremoved-activations)

          ;; Now use each token that was not used to remove a pending activation to remove
          ;; the logical insertions from a previous activation if the truth maintenance system
          ;; has a matching previous activation.
          token-insertion-map (mem/remove-insertions! memory node unremoved-tokens)]

      (when-let [insertions (seq (apply concat (vals token-insertion-map)))]
        ;; If there is current session with rules firing, add these items to the queue
        ;; to be retracted so they occur in the same order as facts being inserted.
        (cond

          ;; Both logical retractions resulting from rule network activity and manual RHS retractions
          ;; expect *current-session* to be bound since both happen in the context of a fire-rules call.
          *current-session*
          ;; Retract facts that have become untrue, unless they became untrue
          ;; because of an activation of the current rule that is :no-loop
          (when (or (not (get-in production [:props :no-loop]))
                    (not (= production (get-in *rule-context* [:node :production]))))
            (do
              ;; Notify the listener of logical retractions.
              ;; Note that this notification happens immediately, while the
              ;; alpha-retract notification on matching alpha nodes will happen when the
              ;; retraction is actually removed from the buffer and executed in the rules network.
              (doseq [[token token-insertions] token-insertion-map]
                (l/retract-facts-logical! listener node token token-insertions))
              (retract-facts! insertions)))

          ;; Any session implementation is required to bind this during external retractions and insertions.
          *pending-external-retractions*
          (do
            (doseq [[token token-insertions] token-insertion-map]
              (l/retract-facts-logical! listener node token token-insertions))
            (swap! *pending-external-retractions* into insertions))

          :else
          (throw (ex-info (str "Attempting to retract from a ProductionNode when neither *current-session* nor "
                               "*pending-external-retractions* is bound is illegal.")
                          {:node node
                           :join-bindings join-bindings
                           :tokens tokens}))))))

  (get-join-keys [node] [])

  (description [node] "ProductionNode")

  ITerminalNode
  (terminal-node-type [this] [:production (:name production)]))

;; The QueryNode is a terminal node that stores the
;; state that can be queried by a rule user.
(defrecord QueryNode [id query param-keys]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    (l/left-activate! listener node tokens)
    (mem/add-tokens! memory node join-bindings tokens))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (mem/remove-tokens! memory node join-bindings tokens))

  (get-join-keys [node] param-keys)

  (description [node] (str "QueryNode -- " query))

  ITerminalNode
  (terminal-node-type [this] [:query (:name query)]))


(defn node-rule-names
  [child-type node]
  (->> node
       (tree-seq (comp seq :children) :children)
       (keep child-type)
       (map :name)
       (distinct)
       (sort)))

(defn- list-of-names
  "Returns formatted string with correctly pluralized header and
  list of names. Returns nil if no such node is found."
  [singular plural prefix names]
  (let [msg-for-unnamed (str "  An unnamed " singular ", provide names to your "
                             plural " if you want them to be identified here.")
        names-string (->> names
                          (sort)
                          (map #(if (nil? %) msg-for-unnamed %))
                          (map #(str prefix "  " %))
                          (string/join "\n"))]
    (if (pos? (count names))
      (str prefix plural ":\n" names-string "\n"))))


(defn- single-condition-message
  [condition-number [condition-definition terminals]]
  (let [productions (->> terminals
                         (filter (comp #{:production} first))
                         (map second))
        queries (->> terminals
                     (filter (comp #{:query} first))
                     (map second))
        production-section (list-of-names "rule" "rules" "   " productions)
        query-section (list-of-names "query" "queries" "   " queries)]
    (string/join
     [(str (inc condition-number) ". " condition-definition "\n")
      production-section
      query-section])))

(defn- throw-condition-exception
  "Adds a useful error message when executing a constraint node raises an exception."
  [{:keys [cause node fact env bindings] :as args}]
  (let [bindings-description (if (empty? bindings)
                               "with no bindings"
                               (str "with bindings\n  " bindings))
        facts-description (if (contains? args :fact)
                            (str "when processing fact\n " (pr-str fact))
                            "with no fact")
        message-header (string/join ["Condition exception raised.\n"
                                     (str facts-description "\n")
                                     (str bindings-description "\n")
                                     "Conditions:\n"])
        conditions-and-rules (get-conditions-and-rule-names node)
        condition-messages (->> conditions-and-rules
                                (map-indexed single-condition-message)
                                (string/join "\n"))
        message (str message-header "\n" condition-messages)]
    (throw (ex-info message
                    {:fact fact
                     :bindings bindings
                     :env env
                     :conditions-and-rules conditions-and-rules}
                    cause))))

(defn- alpha-node-matches
  [facts env activation node]
  (platform/eager-for [fact facts
                       :let [bindings (try (activation fact env)
                                           (catch #?(:clj Exception :cljs :default) e
                                               (throw-condition-exception {:cause e
                                                                           :node node
                                                                           :fact fact
                                                                           :env env})))]
                       :when bindings]           ; FIXME: add env.
                      [fact bindings]))

;; Record representing alpha nodes in the Rete network,
;; each of which evaluates a single condition and
;; propagates matches to its children.
(defrecord AlphaNode [id env children activation fact-type]

  IAlphaActivate
  (alpha-activate [node facts memory transport listener]
    (let [fact-binding-pairs (alpha-node-matches facts env activation node)]
      (l/alpha-activate! listener node (map first fact-binding-pairs))
      (send-elements
       transport
       memory
       listener
       children
       (platform/eager-for [[fact bindings] fact-binding-pairs]
                           (->Element fact bindings)))))

  (alpha-retract [node facts memory transport listener]
    (let [fact-binding-pairs (alpha-node-matches facts env activation node)]
      (l/alpha-retract! listener node (map first fact-binding-pairs))
      (retract-elements
        transport
        memory
        listener
        children
        (platform/eager-for [[fact bindings] fact-binding-pairs]
                            (->Element fact bindings))))))

(defrecord RootJoinNode [id condition children binding-keys]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    ;; This specialized root node doesn't need to deal with the
    ;; empty token, so do nothing.
    )

  (left-retract [node join-bindings tokens memory transport listener]
    ;; The empty token can't be retracted from the root node,
    ;; so do nothing.
    )

  (get-join-keys [node] binding-keys)

  (description [node] (str "RootJoinNode -- " (:text condition)))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]

    (l/right-activate! listener node elements)


    ;; Add elements to the working memory to support analysis tools.
    (mem/add-elements! memory node join-bindings elements)
    ;; Simply create tokens and send it downstream.
    (send-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [{:keys [fact bindings] :as element} elements]
                         (->Token [[fact (:id node)]] bindings))))

  (right-retract [node join-bindings elements memory transport listener]

    (l/right-retract! listener node elements)

    ;; Remove matching elements and send the retraction downstream.
    (retract-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [{:keys [fact bindings] :as element} (mem/remove-elements! memory node join-bindings elements)]
                         (->Token [[fact (:id node)]] bindings))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [type constraints]} condition]
      (into [type] constraints))))

;; Record for the join node, a type of beta node in the rete network. This node performs joins
;; between left and right activations, creating new tokens when joins match and sending them to
;; its descendents.
(defrecord HashJoinNode [id condition children binding-keys]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    ;; Add token to the node's working memory for future right activations.
    (mem/add-tokens! memory node join-bindings tokens)
    (l/left-activate! listener node tokens)
    (send-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [element (mem/get-elements memory node join-bindings)
                          token tokens
                          :let [fact (:fact element)
                                fact-binding (:bindings element)]]
                         (->Token (conj (:matches token) [fact id]) (conj fact-binding (:bindings token))))))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (retract-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [token (mem/remove-tokens! memory node join-bindings tokens)
                          element (mem/get-elements memory node join-bindings)
                          :let [fact (:fact element)
                                fact-bindings (:bindings element)]]
                         (->Token (conj (:matches token) [fact id]) (conj fact-bindings (:bindings token))))))

  (get-join-keys [node] binding-keys)

  (description [node] (str "JoinNode -- " (:text condition)))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]
    (mem/add-elements! memory node join-bindings elements)
    (l/right-activate! listener node elements)
    (send-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [token (mem/get-tokens memory node join-bindings)
                          {:keys [fact bindings] :as element} elements]
                         (->Token (conj (:matches token) [fact id]) (conj (:bindings token) bindings)))))

  (right-retract [node join-bindings elements memory transport listener]
    (l/right-retract! listener node elements)
    (retract-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [{:keys [fact bindings] :as element} (mem/remove-elements! memory node join-bindings elements)
                          token (mem/get-tokens memory node join-bindings)]
                         (->Token (conj (:matches token) [fact id]) (conj (:bindings token) bindings)))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [type constraints]} condition]
      (into [type] constraints))))

(defn- join-node-matches
  [node join-filter-fn token fact fact-bindings env]
  (let [beta-bindings (try (join-filter-fn token fact fact-bindings env)
                           (catch #?(:clj Exception :cljs :default) e
                               (throw-condition-exception {:cause e
                                                           :node node
                                                           :fact fact
                                                           :env env
                                                           :bindings (merge (:bindings token)
                                                                            fact-bindings)})))]
    beta-bindings))

(defrecord ExpressionJoinNode [id condition join-filter-fn children binding-keys]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    ;; Add token to the node's working memory for future right activations.
    (mem/add-tokens! memory node join-bindings tokens)
    (l/left-activate! listener node tokens)
    (send-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [element (mem/get-elements memory node join-bindings)
                          token tokens
                          :let [fact (:fact element)
                                fact-binding (:bindings element)
                                beta-bindings (join-node-matches node join-filter-fn token fact fact-binding (:env condition))]
                          :when beta-bindings]
                         (->Token (conj (:matches token) [fact id])
                                  (conj fact-binding (:bindings token) beta-bindings)))))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (retract-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [token (mem/remove-tokens! memory node join-bindings tokens)
                          element (mem/get-elements memory node join-bindings)
                          :let [fact (:fact element)
                                fact-bindings (:bindings element)
                                beta-bindings (join-node-matches node join-filter-fn token fact fact-bindings (:env condition))]
                          :when beta-bindings]
                         (->Token (conj (:matches token) [fact id])
                                  (conj fact-bindings (:bindings token) beta-bindings)))))

  (get-join-keys [node] binding-keys)

  (description [node] (str "JoinNode -- " (:text condition)))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]
    (mem/add-elements! memory node join-bindings elements)
    (l/right-activate! listener node elements)
    (send-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [token (mem/get-tokens memory node join-bindings)
                          {:keys [fact bindings] :as element} elements
                          :let [beta-bindings (join-node-matches node join-filter-fn token fact bindings (:env condition))]
                          :when beta-bindings]
                         (->Token (conj (:matches token) [fact id])
                                  (conj (:bindings token) bindings beta-bindings)))))

  (right-retract [node join-bindings elements memory transport listener]
    (l/right-retract! listener node elements)
    (retract-tokens
     transport
     memory
     listener
     children
     (platform/eager-for [{:keys [fact bindings] :as element} (mem/remove-elements! memory node join-bindings elements)
                          token (mem/get-tokens memory node join-bindings)
                          :let [beta-bindings (join-node-matches node join-filter-fn token fact bindings (:env condition))]
                          :when beta-bindings]
                         (->Token (conj (:matches token) [fact id])
                                  (conj (:bindings token) bindings beta-bindings)))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [type constraints original-constraints]} condition
          full-constraints (if (seq original-constraints)
                             original-constraints
                             constraints)]
      (into [type] full-constraints))))

;; The NegationNode is a beta node in the Rete network that simply
;; negates the incoming tokens from its ancestors. It sends tokens
;; to its descendent only if the negated condition or join fails (is false).
(defrecord NegationNode [id condition children binding-keys]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    ;; Add token to the node's working memory for future right activations.
    (l/left-activate! listener node tokens)
    (mem/add-tokens! memory node join-bindings tokens)
    (when (empty? (mem/get-elements memory node join-bindings))
      (send-tokens transport memory listener children tokens)))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (mem/remove-tokens! memory node join-bindings tokens)
    (when (empty? (mem/get-elements memory node join-bindings))
      (retract-tokens transport memory listener children tokens)))

  (get-join-keys [node] binding-keys)

  (description [node] (str "NegationNode -- " (:text condition)))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]
    ;; Immediately evaluate whether there are previous elements since mem/get-elements
    ;; returns a mutable list with a LocalMemory on the JVM currently.
    (let [previously-empty? (empty? (mem/get-elements memory node join-bindings))]
      (l/right-activate! listener node elements)
      (mem/add-elements! memory node join-bindings elements)
      ;; Retract tokens that matched the activation if no element matched the negation previously.
      ;; If an element matched the negation already then no elements were propagated and there is
      ;; nothing to retract.
      (when previously-empty?
        (retract-tokens transport memory listener children (mem/get-tokens memory node join-bindings)))))

  (right-retract [node join-bindings elements memory transport listener]
    (l/right-retract! listener node elements)
    (mem/remove-elements! memory node join-bindings elements)
    (when (empty? (mem/get-elements memory node join-bindings))
      (send-tokens transport memory listener children (mem/get-tokens memory node join-bindings))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [type constraints]} condition]
      [:not (into [type] constraints)])))

(defn- matches-some-facts?
  "Returns true if the given token matches one or more of the given elements."
  [node token elements join-filter-fn condition]
  (some (fn [{:keys [fact bindings]}]
          (join-node-matches node join-filter-fn token fact bindings (:env condition)))
        elements))

;; A specialization of the NegationNode that supports additional tests
;; that have to occur on the beta side of the network. The key difference between this and the simple
;; negation node is the join-filter-fn, which allows negation tests to
;; be applied with the parent token in context, rather than just a simple test of the non-existence
;; on the alpha side.
(defrecord NegationWithJoinFilterNode [id condition join-filter-fn children binding-keys]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    ;; Add token to the node's working memory for future right activations.
    (l/left-activate! listener node tokens)
    (mem/add-tokens! memory node join-bindings tokens)

    (send-tokens transport
                 memory
                 listener
                 children
                 (let [elements (mem/get-elements memory node join-bindings)]
                   (platform/eager-for [token tokens
                                        :when (not (matches-some-facts? node
                                                                        token
                                                                        elements
                                                                        join-filter-fn
                                                                        condition))]
                                       token))))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (mem/remove-tokens! memory node join-bindings tokens)
    (retract-tokens transport
                    memory
                    listener
                    children

                    ;; Retract only if it previously had no matches in the negation node,
                    ;; and therefore had an activation.
                    (let [elements (mem/get-elements memory node join-bindings)]
                      (platform/eager-for [token tokens                                  
                                           :when (not (matches-some-facts? node
                                                                           token
                                                                           elements
                                                                           join-filter-fn
                                                                           condition))]
                                          token))))

  (get-join-keys [node] binding-keys)

  (description [node] (str "NegationWithJoinFilterNode -- " (:text condition)))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]
    (l/right-activate! listener node elements)
    (let [previous-elements (mem/get-elements memory node join-bindings)]
      ;; Retract tokens that matched the activation, since they are no longer negated.
      (retract-tokens transport
                      memory
                      listener
                      children
                      (platform/eager-for [token (mem/get-tokens memory node join-bindings)

                                           ;; Retract downstream if the token now has matching elements and didn't before.
                                           ;; We check the new elements first in the expectation that the new elements will be
                                           ;; smaller than the previous elements most of the time
                                           ;; and that the time to check the elements will be proportional
                                           ;; to the number of elements.
                                           :when (and (matches-some-facts? node
                                                                           token
                                                                           elements
                                                                           join-filter-fn
                                                                           condition)
                                                      (not (matches-some-facts? node
                                                                                token
                                                                                previous-elements
                                                                                join-filter-fn
                                                                                condition)))]
                                          token))
      ;; Adding the elements will mutate the previous-elements since, on the JVM, the LocalMemory
      ;; currently returns a mutable List from get-elements after changes in issue 184.  We need to use the
      ;; new and old elements in the logic above as separate collections.  Therefore we need to delay updating the
      ;; memory with the new elements until after we are done with previous-elements.
      (mem/add-elements! memory node join-bindings elements)))

  (right-retract [node join-bindings elements memory transport listener]

    (l/right-retract! listener node elements)
    (mem/remove-elements! memory node join-bindings elements)

    (send-tokens transport
                 memory
                 listener
                 children
                 (let [remaining-elements (mem/get-elements memory node join-bindings)]
                   (platform/eager-for [token (mem/get-tokens memory node join-bindings)

                                        ;; Propagate tokens when some of the retracted facts joined
                                        ;; but none of the remaining facts do.
                                        :when (and (matches-some-facts? node
                                                                        token
                                                                        elements
                                                                        join-filter-fn
                                                                        condition)
                                                   (not (matches-some-facts? node
                                                                             token
                                                                             remaining-elements
                                                                             join-filter-fn
                                                                             condition)))]
                                       token))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [type constraints original-constraints]} condition
          full-constraints (if (seq original-constraints)
                             original-constraints
                             constraints)]
      [:not (into [type] full-constraints)])))

(defn- test-node-matches
  [node test-handler env token]
  (let [test-result (try
                      (test-handler token env)
                      (catch #?(:clj Exception :cljs :default) e
                        (throw-condition-exception {:cause e
                                                    :node node
                                                    :env env
                                                    :bindings (:bindings token)})))]
    test-result))

;; The test node represents a Rete extension in which an arbitrary test condition is run
;; against bindings from ancestor nodes. Since this node
;; performs no joins it does not accept right activations or retractions.
(defrecord TestNode [id env constraints test children]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    (l/left-activate! listener node tokens)
    (send-tokens
     transport
     memory
     listener
     children
     (platform/eager-for
      [token tokens
       :when (test-node-matches node test env token)]
      token)))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (retract-tokens transport memory listener children tokens))

  (get-join-keys [node] [])

  (description [node] (str "TestNode -- " (:text test)))

  IConditionNode
  (get-condition-description [this]
    (into [:test] constraints)))

(defn- do-accumulate
  "Runs the actual accumulation.  Returns the accumulated value."
  [accumulator facts]
  (r/reduce (:reduce-fn accumulator)
            (:initial-value accumulator)
            facts))

(defn- retract-accumulated
  "Helper function to retract an accumulated value."
  [node accum-condition accumulator result-binding token converted-result fact-bindings transport memory listener]
  (let [new-facts (conj (:matches token) [converted-result (:id node)])
        new-bindings (merge (:bindings token)
                            fact-bindings
                            (when result-binding
                              { result-binding
                                converted-result}))]

    (retract-tokens transport memory listener (:children node)
                    [(->Token new-facts new-bindings)])))

(defn- send-accumulated
  "Helper function to send the result of an accumulated value to the node's children."
  [node accum-condition accumulator result-binding token converted-result fact-bindings transport memory listener]
  (let [new-bindings (merge (:bindings token)
                            fact-bindings
                            (when result-binding
                              { result-binding
                               converted-result}))

        ;; This is to check that the produced accumulator result is
        ;; consistent with any variable from another rule condition
        ;; that has the same binding. If another condition binds something
        ;; to ?x, only the accumulator results that match that would propagate.
        ;; We can do this safely because previous states get retracted.
        previous-result (get (:bindings token) result-binding ::no-previous-result)]

    (when (or (= previous-result ::no-previous-result)
              (= previous-result converted-result))

      (send-tokens transport memory listener (:children node)
                   [(->Token (conj (:matches token) [converted-result (:id node)]) new-bindings)]))))

;; The AccumulateNode hosts Accumulators, a Rete extension described above, in the Rete network.
;; It behaves similarly to a JoinNode, but performs an accumulation function on the incoming
;; working-memory elements before sending a new token to its descendents.
(defrecord AccumulateNode [id accum-condition accumulator result-binding children binding-keys new-bindings]
  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]
    (l/left-activate! listener node tokens)
    (let [previous-results (mem/get-accum-reduced-all memory node join-bindings)
          convert-return-fn (:convert-return-fn accumulator)
          has-matches? (seq previous-results)
          initial-value (when-not has-matches?
                          (:initial-value accumulator))
          initial-converted (when (some? initial-value)
                              (convert-return-fn initial-value))]

      (mem/add-tokens! memory node join-bindings tokens)

      (cond
        ;; If there are previously accumulated results to propagate, use them.  If this is the
        ;; first time there are matching tokens, then the reduce will have to happen for the
        ;; first time.  However, this reduce operation is independent of the specific tokens
        ;; since the elements join to the tokens via pre-computed hash join bindings for this
        ;; node.  So only reduce once per binding grouped facts, for all tokens. This includes
        ;; all bindings, not just the join bindings.
        has-matches?
        (doseq [[fact-bindings [previous previous-reduced]] previous-results
                :let [first-reduce? (= ::not-reduced previous-reduced)
                      previous-reduced (if first-reduce?
                                         ;; Need to accumulate since this is the first time we have
                                         ;; tokens matching so we have not accumulated before.
                                         (do-accumulate accumulator previous)
                                         previous-reduced)
                      accum-reduced (when first-reduce?
                                      ^::accum-node [previous previous-reduced])
                      converted (when (some? previous-reduced)
                                  (convert-return-fn previous-reduced))]]

          ;; Newly accumulated results need to be added to memory.
          (when first-reduce?
            (l/add-accum-reduced! listener node join-bindings accum-reduced fact-bindings)
            (mem/add-accum-reduced! memory node join-bindings accum-reduced fact-bindings))

          (when (some? converted)
            (doseq [token tokens]
              (send-accumulated node accum-condition accumulator result-binding token converted fact-bindings
                                transport memory listener))))

        ;; There are no previously accumulated results, but we still may need to propagate things
        ;; such as a sum of zero items.
        ;; If an initial value is provided and the converted value is non-nil, we can propagate
        ;; the converted value as the accumulated item.
        (and (some? initial-converted)
             (empty? new-bindings))

        ;; Note that this is added to memory a single time for all matching tokens because the memory
        ;; location doesn't depend on bindings from individual tokens.

        (let [accum-reduced ^::accum-node [[] initial-value]]
          ;; The fact-bindings are normally a superset of the join-bindings.  We have no fact-bindings
          ;; that are not join-bindings in this case since we have verified that new-bindings is empty.
          ;; Therefore the join-bindings and fact-bindings are exactly equal.
          (l/add-accum-reduced! listener node join-bindings accum-reduced join-bindings)
          (mem/add-accum-reduced! memory node join-bindings accum-reduced join-bindings)

          ;; Send the created accumulated item to the children for each token.
          (doseq [token tokens]
            (send-accumulated node accum-condition accumulator result-binding token initial-converted {}
                              transport memory listener)))

        ;; Propagate nothing if the above conditions don't apply.
        :else
        nil)))

  (left-retract [node join-bindings tokens memory transport listener]
    (l/left-retract! listener node tokens)
    (doseq [:let [removed-tokens (mem/remove-tokens! memory node join-bindings tokens)
                  remaining-tokens (mem/get-tokens memory node join-bindings)

                  ;; Note:  Memory *must* be read here before the memory is potentially cleared in the
                  ;; following lines.
                  previous-results (mem/get-accum-reduced-all memory node join-bindings)

                  ;; If there are no new bindings created by the accumulator condition then
                  ;; a left-activation can create a new binding group in the accumulator memory.
                  ;; If this token is later removed without corresponding elements having been added,
                  ;; we remove the binding group from the accum memory.  Otherwise adding and then retracting
                  ;; tokens could force bindings to retained for the duration of the JVM, regardless of whether
                  ;; the backing facts were garbage collectable.  This would be a memory leak.
                  _ (when (and (empty? remaining-tokens)
                               (empty? new-bindings)
                               (let [current (mem/get-accum-reduced memory node join-bindings join-bindings)]
                                 (and
                                  ;; If there is nothing under these bindings already in the memory then there is no
                                  ;; need to take further action.
                                  (not= current ::mem/no-accum-reduced)
                                  ;; Check to see if there are elements under this binding group.
                                  ;; If elements are present we must keep the binding group regardless of the
                                  ;; presence or absence of tokens.
                                  (-> current first empty?))))
                      (mem/remove-accum-reduced! memory node join-bindings join-bindings))]
            ;; There is nothing to do if no tokens were removed.
            :when (seq removed-tokens)
            ;; Note that this will cause a Cartesian join between tokens and elements groups where the token
            ;; and element group share the same join bindings, but the element groups may have additional bindings
            ;; that come from their alpha nodes. Keep in mind that these element groups need elements to be created
            ;; and cannot come from initial values if they have bindings that are not shared with tokens.
            [fact-bindings [previous previous-reduced]] previous-results
            :let [;; If there were tokens before that are now removed, the value would have been accumulated already.
                  ;; This means there is no need to check for ::not-reduced here.
                  previous-converted (when (some? previous-reduced)
                                       ((:convert-return-fn accumulator) previous-reduced))]
            ;; A nil previous result should not have been propagated before.
            :when (some? previous-converted)
            token removed-tokens]
      (retract-accumulated node accum-condition accumulator result-binding token previous-converted fact-bindings
                           transport memory listener)))

  (get-join-keys [node] binding-keys)

  (description [node] (str "AccumulateNode -- " accumulator))

  IAccumRightActivate
  (pre-reduce [node elements]
    ;; Return a seq tuples with the form [binding-group facts-from-group-elements].
    (platform/eager-for [[bindings element-group] (platform/group-by-seq :bindings elements)]
                        [bindings (mapv :fact element-group)]))

  (right-activate-reduced [node join-bindings fact-seq memory transport listener]

    ;; Combine previously reduced items together, join to matching tokens, and emit child tokens.
    (doseq [:let [convert-return-fn (:convert-return-fn accumulator)
                  ;; Note that we want to iterate over all tokens with the desired join bindings later
                  ;; independently of the fact binding groups created by elements; that is, a token
                  ;; can join with multiple groups of fact bindings when the accumulator condition
                  ;; creates new bindings.
                  matched-tokens (mem/get-tokens memory node join-bindings)
                  has-matches? (seq matched-tokens)]
            [bindings facts] fact-seq
            :let [previous (mem/get-accum-reduced memory node join-bindings bindings)
                  has-previous? (not= ::mem/no-accum-reduced previous)
                  [previous previous-reduced] (if has-previous?
                                                previous
                                                [::mem/no-accum-reduced ::not-reduced])
                  combined (if has-previous?
                             (into previous facts)
                             facts)
                  combined-reduced
                  (cond
                    ;; Reduce all of the combined items for the first time if there are
                    ;; now matches, and nothing was reduced before.
                    (and has-matches?
                         (= ::not-reduced previous-reduced))
                    (do-accumulate accumulator combined)

                    ;; There are matches, a previous reduced value for the previous items and a
                    ;; :combine-fn is given.  Use the :combine-fn on both the previously reduced
                    ;; and the newly reduced results.
                    (and has-matches?
                         (:combine-fn accumulator))
                    ((:combine-fn accumulator) previous-reduced (do-accumulate accumulator facts))

                    ;; There are matches and there is a previous reduced value for the previous
                    ;; items.  So just add the new items to the accumulated value.
                    has-matches?
                    (do-accumulate (assoc accumulator :initial-value previous-reduced) facts)

                    ;; There are no matches right now.  So do not perform any accumulations.
                    ;; If there are never matches, time will be saved by never reducing.
                    :else
                    ::not-reduced)

                  converted (when (and (some? combined-reduced)
                                       (not= ::not-reduced combined-reduced))
                              (convert-return-fn combined-reduced))

                  previous-converted (when (and has-previous?
                                                (some? previous-reduced)
                                                (not= ::not-reduced previous-reduced))
                                       (convert-return-fn previous-reduced))

                  accum-reduced ^::accum-node [combined combined-reduced]]]

      ;; Add the combined results to memory.
      (l/add-accum-reduced! listener node join-bindings accum-reduced bindings)
      (mem/add-accum-reduced! memory node join-bindings accum-reduced bindings)

      (cond

        ;; Do nothing when the result was nil before and after.
        (and (nil? previous-converted)
             (nil? converted))
        nil

        (nil? converted)
        (doseq [token matched-tokens]
          (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings
                               transport memory listener))

        (nil? previous-converted)
        (doseq [token matched-tokens]
          (send-accumulated node accum-condition accumulator result-binding token converted bindings
                            transport memory listener))


        ;; If there are previous results, then propagate downstream if the new result differs from
        ;; the previous result.  If the new result is equal to the previous result don't do
        ;; anything.  Note that the memory has already been updated with the new combined value,
        ;; which may be needed if elements in memory changes later.
        (not= converted previous-converted)
        ;; There is no requirement that we doseq over all retractions then doseq over propagations; we could
        ;; just as easily doseq over tokens at the top level and retract and propagate for each token in turn.
        ;; In the absence of hard evidence either way, doing it this way is just an educated guess as to
        ;; which is likely to be more performant.
        (do
          (doseq [token matched-tokens]
            (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings
                                 transport memory listener))
          (doseq [token matched-tokens]
            (send-accumulated node accum-condition accumulator result-binding token converted bindings
                              transport memory listener))))))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]

    (l/right-activate! listener node elements)
    ;; Simple right-activate implementation simple defers to
    ;; accumulator-specific logic.
    (right-activate-reduced
     node
     join-bindings
     (pre-reduce node elements)
     memory
     transport
     listener))

  (right-retract [node join-bindings elements memory transport listener]

    (l/right-retract! listener node elements)

    (doseq [:let [convert-return-fn (:convert-return-fn accumulator)
                  ;; As in right-activate-reduced, a token can match with multiple groupings of elements
                  ;; by their bindings.
                  matched-tokens (mem/get-tokens memory node join-bindings)
                  has-matches? (seq matched-tokens)]
            [bindings elements] (platform/group-by-seq :bindings elements)

            :let [previous (mem/get-accum-reduced memory node join-bindings bindings)
                  has-previous? (not= ::mem/no-accum-reduced previous)
                  [previous previous-reduced] (if has-previous?
                                                previous
                                                ^::accum-node [::mem/no-accum-reduced ::not-reduced])]

            ;; No need to retract anything if there were no previous items.
            :when has-previous?

            ;; Compute the new version with the retracted information.
            :let [facts (mapv :fact elements)
                  [removed retracted] (mem/remove-first-of-each facts previous)
                  all-retracted? (empty? retracted)
                  ;; If there is a previous and matches, there would have been a
                  ;; propagated and accumulated value.  So there is something to
                  ;; retract and re-accumulated in place of.
                  ;; Otherwise, no reduce is needed right now.
                  retracted-reduced (if (and has-matches?
                                             (not all-retracted?))
                                      ;; Use the provided :retract-fn if one is provided.
                                      ;; Otherwise, just re-accumulate based on the
                                      ;; remaining items after retraction.
                                      (if-let [retract-fn (:retract-fn accumulator)]
                                        (r/reduce retract-fn previous-reduced removed)
                                        (do-accumulate accumulator retracted))
                                      ::not-reduced)

                  ;; It is possible that either the retracted or previous reduced are ::not-reduced
                  ;; at this point if there are no matching tokens.  has-matches? indicates this.  If
                  ;; this is the case, there are no converted values to calculate.  However, memory still
                  ;; will be updated since the facts left after this retraction still need to be stored
                  ;; for later possible activations.
                  retracted-converted (when (and (some? retracted-reduced)
                                                 (not= ::not-reduced retracted-reduced))
                                        (convert-return-fn retracted-reduced))
                  previous-converted (when (and (some? previous-reduced)
                                                (not= ::not-reduced previous-reduced))
                                       (convert-return-fn previous-reduced))]]

      (if all-retracted?
        (do
          ;; When everything has been retracted we need to remove the accumulated results from memory.
          (l/remove-accum-reduced! listener node join-bindings bindings)
          (mem/remove-accum-reduced! memory node join-bindings bindings)

          (doseq [:when (some? previous-converted)
                  token matched-tokens]
            ;; Retract the previous token.
            (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings
                                 transport memory listener))

          (let [initial-value (:initial-value accumulator)

                initial-converted (when initial-value
                                    (convert-return-fn initial-value))]

            (when (and (some? initial-converted)
                       (empty? new-bindings))

              (doseq [token matched-tokens]
                (l/add-accum-reduced! listener node join-bindings ^::accum-node [[] initial-value] join-bindings)
                (mem/add-accum-reduced! memory node join-bindings ^::accum-node [[] initial-value] join-bindings)
                (send-accumulated node accum-condition accumulator result-binding token initial-converted {}
                                  transport memory listener)))))
        (do
          ;; Add our newly retracted information to our node.
          (l/add-accum-reduced! listener node join-bindings ^::accum-node [retracted retracted-reduced] bindings)
          (mem/add-accum-reduced! memory node join-bindings ^::accum-node  [retracted retracted-reduced] bindings)

          (cond
            (and (nil? previous-converted)
                 (nil? retracted-converted))
            nil

            (nil? previous-converted)
            (doseq [token matched-tokens]
              (send-accumulated node accum-condition accumulator result-binding token retracted-converted bindings
                                transport memory listener))

            (nil? retracted-converted)
            (doseq [token matched-tokens]
              (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings
                                   transport memory listener))

            (not= retracted-converted previous-converted)
            ;; There is no requirement that we doseq over all retractions then doseq over propagations; we could
            ;; just as easily doseq over tokens at the top level and retract and propagate for each token in turn.
            ;; In the absence of hard evidence either way, doing it this way is just an educated guess as to
            ;; which is likely to be more performant.
            (do
              (doseq [token matched-tokens]
                (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings
                                     transport memory listener))
              (doseq [token matched-tokens]
                (send-accumulated node accum-condition accumulator result-binding token retracted-converted bindings
                                  transport memory listener))))))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [accumulator from]} accum-condition
          {:keys [type constraints]} from
          condition (into [type] constraints)
          result-symbol (symbol (name result-binding))]
      [result-symbol '<- accumulator :from condition]))

  IAccumInspect
  (token->matching-elements [this memory token]
    ;; Tokens are stored in the memory keyed on join bindings with previous nodes and new bindings
    ;; introduced in this node.  Each of these sets of bindings is known at the time of rule network
    ;; compilation.  It is expected that this function will receive tokens that were propagated from this
    ;; node to its children and may have had other bindings added in the process.  The bindings map entries
    ;; in the tokens created by descendants based on tokens propagated from ancestors are subsets of the bindings
    ;; in each ancestor.  Put differently, if token T1 is passed to a child that create a token T2 based on it
    ;; and passes it to its children, the following statement is true:
    ;; (= (select-keys (-> t1 :bindings keys) t2)
    ;;    (:bindings t1))
    ;; This being the case, we can use the downstream token to find out what binding key-value pairs were used
    ;; to create the token "stream" of which it is part.
    (let [join-bindings (-> token :bindings (select-keys (get-join-keys this)))
          fact-bindings (-> token :bindings (select-keys new-bindings))]
      (first (mem/get-accum-reduced memory this join-bindings (merge join-bindings fact-bindings))))))

(defn- filter-accum-facts
  "Run a filter on elements against a given token for constraints that are not simple hash joins."
  [node join-filter-fn token candidate-facts bindings condition]
  (filter #(join-node-matches node join-filter-fn token % bindings (:env condition)) candidate-facts))

;; A specialization of the AccumulateNode that supports additional tests
;; that have to occur on the beta side of the network. The key difference between this and the simple
;; accumulate node is the join-filter-fn, which accepts a token and a fact and filters out facts that
;; are not consistent with the given token.
(defrecord AccumulateWithJoinFilterNode [id accum-condition accumulator join-filter-fn
                                         result-binding children binding-keys new-bindings]

  ILeftActivate
  (left-activate [node join-bindings tokens memory transport listener]

    (l/left-activate! listener node tokens)

    ;; Facts that are candidates for matching the token are used in this accumulator node,
    ;; which must be filtered before running the accumulation.
    (let [convert-return-fn (:convert-return-fn accumulator)
          grouped-candidate-facts (mem/get-accum-reduced-all memory node join-bindings)]
      (mem/add-tokens! memory node join-bindings tokens)

      (cond

        (seq grouped-candidate-facts)
        (doseq [token tokens
                [fact-bindings candidate-facts] grouped-candidate-facts

                ;; Filter to items that match the incoming token, then apply the accumulator.
                :let [filtered-facts (filter-accum-facts node join-filter-fn token candidate-facts
                                                         fact-bindings accum-condition)]

                :when (or (seq filtered-facts)
                          ;; Even if there no filtered facts, if there are no new bindings we may
                          ;; have an initial value to propagate.
                          (and (some? (:initial-value accumulator))
                               (empty? new-bindings)))

                :let [accum-result (do-accumulate accumulator filtered-facts)
                      converted-result (when (some? accum-result)
                                         (convert-return-fn accum-result))]

                :when (some? converted-result)]

          (send-accumulated node accum-condition accumulator result-binding token
                            converted-result fact-bindings transport memory listener))

        ;; There are no previously accumulated results, but we still may need to propagate things
        ;; such as a sum of zero items.
        ;; If all variables in the accumulated item are bound and an initial
        ;; value is provided, we can propagate the initial value as the accumulated item.

        ;; We need to not propagate nil initial values, regardless of whether the convert-return-fn
        ;; makes them non-nil, in order to not break existing code; this is discussed more in the
        ;; right-activate-reduced implementation.
        (and (some? (:initial-value accumulator))
             (empty? new-bindings)) ; An initial value exists that we can propagate.
        (let [initial-value (:initial-value accumulator)
              ;; Note that we check the the :initial-value is non-nil above, which is why we
              ;; don't need (when initial-value (convert-return-fn initial-value)) here.
              converted-result (convert-return-fn initial-value)]

          (when (some? converted-result)
            ;; Send the created accumulated item to the children.
            (doseq [token tokens]
              (send-accumulated node accum-condition accumulator result-binding token
                                converted-result join-bindings transport memory listener))))

        ;; Propagate nothing if the above conditions don't apply.
        :default nil)))

  (left-retract [node join-bindings tokens memory transport listener]

    (l/left-retract! listener node tokens)

    (let [;; Even if the accumulator didn't propagate anything before we still need to remove the tokens
          ;; in case they would have otherwise been used in the future.
          tokens (mem/remove-tokens! memory node join-bindings tokens)
          convert-return-fn (:convert-return-fn accumulator)
          grouped-candidate-facts (mem/get-accum-reduced-all memory node join-bindings)]

      (cond

        (seq grouped-candidate-facts)
        (doseq [token tokens
                [fact-bindings candidate-facts] grouped-candidate-facts

                :let [filtered-facts (filter-accum-facts node join-filter-fn token candidate-facts
                                                         fact-bindings accum-condition)]

                :when (or (seq filtered-facts)
                          ;; Even if there no filtered facts, if there are no new bindings an initial value
                          ;; maybe have propagated, and if so we need to retract it.
                          (and (some? (:initial-value accumulator))
                               (empty? new-bindings)))

                :let [accum-result (do-accumulate accumulator filtered-facts)
                      retracted-converted (when (some? accum-result)
                                            (convert-return-fn accum-result))]

                ;; A nil retracted previous result should not have been propagated before.
                :when (some? retracted-converted)]

          (retract-accumulated node accum-condition accumulator result-binding token
                               retracted-converted fact-bindings transport memory listener))

        (and (some? (:initial-value accumulator))
             (empty? new-bindings))
        (let [initial-value (:initial-value accumulator)
              ;; Note that we check the the :initial-value is non-nil above, which is why we
              ;; don't need (when initial-value (convert-return-fn initial-value)) here.
              converted-result (convert-return-fn initial-value)]

          (when (some? converted-result)
            (doseq [token tokens]
              (retract-accumulated node accum-condition accumulator result-binding token
                                   converted-result join-bindings transport memory listener))))

        :else nil)))

  (get-join-keys [node] binding-keys)

  (description [node] (str "AccumulateWithBetaPredicateNode -- " accumulator))

  IAccumRightActivate
  (pre-reduce [node elements]
    ;; Return a map of bindings to the candidate facts that match them. This accumulator
    ;; depends on the values from parent facts, so we defer actually running the accumulator
    ;; until we have a token.
    (platform/eager-for [[bindings element-group] (platform/group-by-seq :bindings elements)]
                        [bindings (map :fact element-group)]))

  (right-activate-reduced [node join-bindings binding-candidates-seq memory transport listener]

    ;; Combine previously reduced items together, join to matching tokens,
    ;; and emit child tokens.
    (doseq [:let [convert-return-fn (:convert-return-fn accumulator)
                  matched-tokens (mem/get-tokens memory node join-bindings)]
            [bindings candidates] binding-candidates-seq
            :let [previous-candidates (mem/get-accum-reduced memory node join-bindings bindings)
                  previously-reduced? (not= ::mem/no-accum-reduced previous-candidates)
                  previous-candidates (when previously-reduced? previous-candidates)]]

      ;; Combine the newly reduced values with any previous items.  Ensure that new items are always added to the end so that
      ;; we have a consistent order for retracting results from accumulators such as acc/all whose results can be in any order.  Making this
      ;; ordering consistent allows us to skip the filter step on previous elements on right-activations.
      (let [combined-candidates (into []
                                      cat
                                      [previous-candidates candidates])]

        (l/add-accum-reduced! listener node join-bindings combined-candidates bindings)

        (mem/add-accum-reduced! memory node join-bindings combined-candidates bindings))

      (doseq [token matched-tokens

              :let [new-filtered-facts (filter-accum-facts node join-filter-fn token candidates
                                                           bindings accum-condition)]

              ;; If no new elements matched the token, we don't need to do anything for this token
              ;; since the final result is guaranteed to be the same.
              :when (seq new-filtered-facts)

              :let [previous-filtered-facts (filter-accum-facts node join-filter-fn token previous-candidates
                                                                bindings accum-condition)

                    previous-accum-result-init (cond
                                                 (seq previous-filtered-facts)
                                                 (do-accumulate accumulator previous-filtered-facts)

                                                 (and (-> accumulator :initial-value some?)
                                                      (empty? new-bindings))
                                                 (:initial-value accumulator)

                                                 ;; Allow direct determination later of whether there was a previous value
                                                 ;; as determined by the preceding cond conditions.
                                                 :else ::no-previous-value)

                    previous-accum-result (when (not= previous-accum-result-init ::no-previous-value)
                                            previous-accum-result-init)

                    ;; Since the new elements are added onto the end of the previous elements in the accum-memory
                    ;; accumulating using the new elements on top of the previous result is an accumulation in the same
                    ;; order as the elements are present in memory.  As a result, future accumulations on the contents of the accum memory
                    ;; prior to further modification of that memory will return the same result as here.  This is important since if we use
                    ;; something like acc/all to accumulate to and propagate [A B] if B is retracted we need to retract [A B] not [B A]; the latter won't
                    ;; actually retract anything, which would be invalid.
                    accum-result (let [accum-previous-init (if (not= previous-accum-result-init ::no-previous-value)
                                                             ;; If there was a previous result, use it as the initial value.
                                                             (assoc accumulator :initial-value previous-accum-result)
                                                             ;; If there was no previous result, use the default initial value.
                                                             ;; Note that if there is a non-nil initial value but there are new binding
                                                             ;; groups we consider there to have been no previous value, but we still want
                                                             ;; to use the actual initial value, not nil.
                                                             accumulator)]
                                   (do-accumulate accum-previous-init new-filtered-facts))

                    previous-converted (when (some? previous-accum-result)
                                         (convert-return-fn previous-accum-result))

                    new-converted (when (some? accum-result)
                                    (convert-return-fn accum-result))]]

        (cond

          ;; When both the new and previous result were nil do nothing.
          (and (nil? previous-converted)
               (nil? new-converted))
          nil

          (nil? new-converted)
          (retract-accumulated node accum-condition accumulator result-binding token
                               previous-converted bindings transport memory listener)

          (nil? previous-converted)
          (send-accumulated node accum-condition accumulator result-binding token new-converted bindings transport memory listener)

          (not= new-converted previous-converted)
          (do
            (retract-accumulated node accum-condition accumulator result-binding token
                                 previous-converted bindings transport memory listener)
            (send-accumulated node accum-condition accumulator result-binding token new-converted bindings transport memory listener))))))

  IRightActivate
  (right-activate [node join-bindings elements memory transport listener]

    (l/right-activate! listener node elements)

    ;; Simple right-activate implementation simple defers to
    ;; accumulator-specific logic.
    (right-activate-reduced
     node
     join-bindings
     (pre-reduce node elements)
     memory
     transport
     listener))

  (right-retract [node join-bindings elements memory transport listener]

    (l/right-retract! listener node elements)

    (doseq [:let [convert-return-fn (:convert-return-fn accumulator)
                  matched-tokens (mem/get-tokens memory node join-bindings)]
            [bindings elements] (platform/group-by-seq :bindings elements)
            :let [previous-candidates (mem/get-accum-reduced memory node join-bindings bindings)]

            ;; No need to retract anything if there was no previous item.
            :when (not= ::mem/no-accum-reduced previous-candidates)

            :let [facts (mapv :fact elements)
                  new-candidates (second (mem/remove-first-of-each facts previous-candidates))]]

      ;; Add the new candidates to our node.
      (l/add-accum-reduced! listener node join-bindings new-candidates bindings)
      (mem/add-accum-reduced! memory node join-bindings new-candidates bindings)

      (doseq [;; Get all of the previously matched tokens so we can retract and re-send them.
              token matched-tokens

              :let [previous-facts (filter-accum-facts node join-filter-fn token previous-candidates
                                                       bindings accum-condition)

                    new-facts (filter-accum-facts node join-filter-fn token new-candidates
                                                  bindings accum-condition)]

              ;; The previous matching elements are a superset of the matching elements after retraction.
              ;; Therefore, if the counts before and after are equal nothing retracted actually matched
              ;; and we don't need to do anything else here since the end result shouldn't change.
              :when (not= (count previous-facts)
                          (count new-facts))

              :let [;; We know from the check above that matching elements existed previously,
                    ;; since if there were no previous matching elements the count of matching
                    ;; elements before and after a right-retraction cannot be different.
                    previous-result (do-accumulate accumulator previous-facts)

                    ;; TODO: Can we use the retract-fn here if present to improve performance?  We'd also potentially
                    ;; avoid needing to filter facts twice above, since elements present both before and after retraction
                    ;; will given to the join-filter-fn twice (once when creating previous-facts and once when creating new-facts).
                    ;; Note that any future optimizations here must ensure that the result propagated here is equal to the result
                    ;; that will be recreated as the previous result in right activate, and that this can be dependent on the order
                    ;; of candidates in the memory, since, for example (acc/all) can return both [A B] and [B A] but these are not equal.

                    new-result (cond

                                 (seq new-facts)
                                 (do-accumulate accumulator new-facts)

                                 (and (-> accumulator :initial-value some?)
                                      (empty? new-bindings))
                                 (:initial-value accumulator)

                                 :else nil)

                    previous-converted (when (some? previous-result)
                                         (convert-return-fn previous-result))

                    new-converted (when (some? new-result)
                                    (convert-return-fn new-result))]]

        (cond

          ;; When both the previous and new results are nil do nothing.
          (and (nil? previous-converted)
               (nil? new-converted))
          nil

          (nil? new-converted)
          (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings transport memory listener)

          (nil? previous-converted)
          (send-accumulated node accum-condition accumulator result-binding token new-converted bindings transport memory listener)

          (not= previous-converted new-converted)
          (do
            (retract-accumulated node accum-condition accumulator result-binding token previous-converted bindings transport memory listener)
            (send-accumulated node accum-condition accumulator result-binding token new-converted bindings transport memory listener))))))

  IConditionNode
  (get-condition-description [this]
    (let [{:keys [accumulator from]} accum-condition
          {:keys [type constraints original-constraints]} from
          result-symbol (symbol (name result-binding))
          full-constraints (if (seq original-constraints)
                             original-constraints
                             constraints)
          condition (into [type] full-constraints)]
      [result-symbol '<- accumulator :from condition]))

  ;; The explanation of the implementation of token->matching-elements on AccumulateNode applies here as well.
  ;; Note that since we store all facts propagated from the alpha network to this condition in the accum memory,
  ;; regardless of whether they meet the join condition with upstream facts from the beta network, we rerun the
  ;; the join filter function.  Since the :matches are not used in the join filter function and the bindings in the
  ;; token will contain all bindings used in the "ancestor token" to join with these same facts, we can just pass the token
  ;; as-is to the join filter.
  IAccumInspect
  (token->matching-elements [this memory token]
    (let [join-bindings (-> token :bindings (select-keys (get-join-keys this)))
          fact-bindings (-> token :bindings (select-keys new-bindings))
          unfiltered-facts (mem/get-accum-reduced memory this join-bindings (merge join-bindings fact-bindings))]
      ;; The functionality to throw conditions with meaningful information assumes that all bindings in the token
      ;; are meaningful to the join, which is not the case here since the token passed is from a descendant of this node, not
      ;; this node.  The generated error message also wouldn't make much sense in the context of session inspection.
      ;; We could create specialized error handling here, but in reality most cases that cause errors here would also cause
      ;; errors at rule firing time so the benefit would be limited.  Nevertheless there would be some benefit and it is
      ;; possible that we will do it in the future..
      (filter (fn [fact] (join-filter-fn token fact fact-bindings {}))
              unfiltered-facts))))

;; This lives here as it is both close to the node that it represents, and is accessible to both clj and cljs
(def node-type->abbreviated-type
  "To minimize function name length and attempt to prevent issues with filename length we can use these abbreviations to
  shorten the node types. Used during compilation of the rules network."
  {"AlphaNode" "AN"
   "TestNode" "TN"
   "AccumulateNode" "AccN"
   "AccumulateWithJoinFilterNode" "AJFN"
   "ProductionNode" "PN"
   "NegationWithJoinFilterNode" "NJFN"
   "ExpressionJoinNode" "EJN"})

(defn variables-as-keywords
  "Returns symbols in the given s-expression that start with '?' as keywords"
  [expression]
  (into #{} (platform/eager-for [item (tree-seq coll? seq expression)
                                 :when (and (symbol? item)
                                            (= \? (first (name item))))]
                                (keyword item))))

(defn conj-rulebases
  "DEPRECATED. Simply concat sequences of rules and queries.

   Conjoin two rulebases, returning a new one with the same rules."
  [base1 base2]
  (concat base1 base2))

(defn fire-rules*
  "Fire rules for the given nodes."
  [rulebase nodes transient-memory transport listener get-alphas-fn update-cache]
  (binding [*current-session* {:rulebase rulebase
                               :transient-memory transient-memory
                               :transport transport
                               :insertions (atom 0)
                               :get-alphas-fn get-alphas-fn
                               :pending-updates update-cache
                               :listener listener}]

    (loop [next-group (mem/next-activation-group transient-memory)
           last-group nil]

      (if next-group

        (if (and last-group (not= last-group next-group))

          ;; We have changed groups, so flush the updates from the previous
          ;; group before continuing.
          (do
            (flush-updates *current-session*)
            (let [upcoming-group (mem/next-activation-group transient-memory)]
              (l/activation-group-transition! listener next-group upcoming-group)
              (recur upcoming-group next-group)))

          (do

            ;; If there are activations, fire them.
            (when-let [{:keys [node token] :as activation} (mem/pop-activation! transient-memory)]
              ;; Use vectors for the insertion caches so that within an insertion type
              ;; (unconditional or logical) all insertions are done in order after the into
              ;; calls in insert-facts!.  This shouldn't have a functional impact, since any ordering
              ;; should be valid, but makes traces less confusing to end users.  It also prevents any laziness
              ;; in the sequences.
              (let [batched-logical-insertions (atom [])
                    batched-unconditional-insertions (atom [])
                    batched-rhs-retractions (atom [])]
                (binding [*rule-context* {:token token
                                          :node node
                                          :batched-logical-insertions batched-logical-insertions
                                          :batched-unconditional-insertions batched-unconditional-insertions
                                          :batched-rhs-retractions batched-rhs-retractions}]

                  ;; Fire the rule itself.
                  (try
                    ((:rhs node) token (:env (:production node)))
                    ;; Don't do anything if a given insertion type has no corresponding
                    ;; facts to avoid complicating traces.  Note that since each no RHS's of
                    ;; downstream rules are fired here everything is governed by truth maintenance.
                    ;; Therefore, the reordering of retractions and insertions should have no impact
                    ;; assuming that the evaluation of rule conditions is pure, which is a general expectation
                    ;; of the rules engine.
                    ;;
                    ;; Bind the contents of the cache atoms after the RHS is fired since they are used twice
                    ;; below.  They will be dereferenced again if an exception is caught, but in the error
                    ;; case we aren't worried about performance.
                    (let [retrieved-unconditional-insertions @batched-unconditional-insertions
                          retrieved-logical-insertions @batched-logical-insertions
                          retrieved-rhs-retractions @batched-rhs-retractions]
                      (l/fire-activation! listener
                                          activation
                                          {:unconditional-insertions retrieved-unconditional-insertions
                                           :logical-insertions retrieved-logical-insertions
                                           :rhs-retractions retrieved-rhs-retractions})
                      (when-let [batched (seq retrieved-unconditional-insertions)]
                        (flush-insertions! batched true))
                      (when-let [batched (seq retrieved-logical-insertions)]
                        (flush-insertions! batched false))
                      (when-let [batched (seq retrieved-rhs-retractions)]
                        (flush-rhs-retractions! batched)))
                    (catch #?(:clj Exception :cljs :default) e

                           ;; If the rule fired an exception, help debugging by attaching
                           ;; details about the rule itself, cached insertions, and any listeners
                           ;; while propagating the cause.
                           (let [production (:production node)
                                 rule-name (:name production)
                                 rhs (:rhs production)]
                             (throw (ex-info (str "Exception in " (if rule-name rule-name (pr-str rhs))
                                                  " with bindings " (pr-str (:bindings token)))
                                             {:bindings (:bindings token)
                                              :name rule-name
                                              :rhs rhs
                                              :batched-logical-insertions @batched-logical-insertions
                                              :batched-unconditional-insertions @batched-unconditional-insertions
                                              :batched-rhs-retractions @batched-rhs-retractions
                                              :listeners (try
                                                           (let [p-listener (l/to-persistent! listener)]
                                                             (if (l/null-listener? p-listener)
                                                               []
                                                               (l/get-children p-listener)))
                                                           (catch #?(:clj Exception :cljs :default)
                                                               listener-exception
                                                             listener-exception))}
                                             e)))))

                  ;; Explicitly flush updates if we are in a no-loop rule, so the no-loop
                  ;; will be in context for child rules.
                  (when (some-> node :production :props :no-loop)
                    (flush-updates *current-session*)))))

            (recur (mem/next-activation-group transient-memory) next-group)))

        ;; There were no items to be activated, so flush any pending
        ;; updates and recur with a potential new activation group
        ;; since a flushed item may have triggered one.
        (when (flush-updates *current-session*)
          (let [upcoming-group (mem/next-activation-group transient-memory)]
            (l/activation-group-transition! listener next-group upcoming-group)
            (recur upcoming-group next-group)))))))

(deftype LocalSession [rulebase memory transport listener get-alphas-fn pending-operations]
  ISession
  (insert [session facts]

    (let [new-pending-operations (conj pending-operations (uc/->PendingUpdate :insertion
                                                                              ;; Preserve the behavior prior to https://github.com/cerner/clara-rules/issues/268
                                                                              ;; , particularly for the Java API, where the caller could freely mutate a
                                                                              ;; collection of facts after passing it to Clara for the constituent
                                                                              ;; facts to be inserted or retracted.  If the caller passes a persistent
                                                                              ;; Clojure collection don't do any additional work.
                                                                              (if (coll? facts)
                                                                                facts
                                                                                (into [] facts))))]

      (LocalSession. rulebase
                     memory
                     transport
                     listener
                     get-alphas-fn
                     new-pending-operations)))

  (retract [session facts]

    (let [new-pending-operations (conj pending-operations (uc/->PendingUpdate :retraction
                                                                              ;; As in insert above defend against facts being a mutable collection.
                                                                              (if (coll? facts)
                                                                                facts
                                                                                (into [] facts))))]

      (LocalSession. rulebase
                     memory
                     transport
                     listener
                     get-alphas-fn
                     new-pending-operations)))

  ;; Prior to issue 249 we only had a one-argument fire-rules method.  clara.rules/fire-rules will always call the two-argument method now
  ;; but we kept a one-argument version of the fire-rules in case anyone is calling the fire-rules protocol function or method on the session directly.
  (fire-rules [session] (fire-rules session {}))
  (fire-rules [session opts]

    (let [transient-memory (mem/to-transient memory)
          transient-listener (l/to-transient listener)]

      (if-not (:cancelling opts)
        ;; We originally performed insertions and retractions immediately after the insert and retract calls,
        ;; but this had the downside of making a pattern like "Retract facts, insert other facts, and fire the rules"
        ;; perform at least three transitions between a persistent and transient memory.  Delaying the actual execution
        ;; of the insertions and retractions until firing the rules allows us to cut this down to a single transition
        ;; between persistent and transient memory.  There is some cost to the runtime dispatch on operation types here,
        ;; but this is presumably less significant than the cost of memory transitions.
        ;;
        ;; We perform the insertions and retractions in the same order as they were applied to the session since
        ;; if a fact is not in the session, retracted, and then subsequently inserted it should be in the session at
        ;; the end.
        (do
          (doseq [{op-type :type facts :facts} pending-operations]

            (case op-type

              :insertion
              (do
                (l/insert-facts! transient-listener nil nil facts)

                (binding [*pending-external-retractions* (atom [])]
                  ;; Bind the external retractions cache so that any logical retractions as a result
                  ;; of these insertions can be cached and executed as a batch instead of eagerly realizing
                  ;; them.  An external insertion of a fact that matches
                  ;; a negation or accumulator condition can cause logical retractions.
                  (doseq [[alpha-roots fact-group] (get-alphas-fn facts)
                          root alpha-roots]
                    (alpha-activate root fact-group transient-memory transport transient-listener))
                  (external-retract-loop get-alphas-fn transient-memory transport transient-listener)))

              :retraction
              (do
                (l/retract-facts! transient-listener nil nil facts)

                (binding [*pending-external-retractions* (atom facts)]
                  (external-retract-loop get-alphas-fn transient-memory transport transient-listener)))))

          (fire-rules* rulebase
                       (:production-nodes rulebase)
                       transient-memory
                       transport
                       transient-listener
                       get-alphas-fn
                       (uc/get-ordered-update-cache)))

        #?(:cljs (throw (ex-info "The :cancelling option is not supported in ClojureScript"
                                 {:session session :opts opts}))

           :clj (let [insertions (sequence
                                  (comp (filter (fn [pending-op]
                                                  (= (:type pending-op)
                                                     :insertion)))
                                        (mapcat :facts))
                                  pending-operations)

                      retractions (sequence
                                   (comp (filter (fn [pending-op]
                                                   (= (:type pending-op)
                                                      :retraction)))
                                         (mapcat :facts))
                                   pending-operations)

                      update-cache (ca/get-cancelling-update-cache)]

                  (binding [*current-session* {:rulebase rulebase
                                               :transient-memory transient-memory
                                               :transport transport
                                               :insertions (atom 0)
                                               :get-alphas-fn get-alphas-fn
                                               :pending-updates update-cache
                                               :listener transient-listener}]

                    ;; Insertions should come before retractions so that if we insert and then retract the same
                    ;; fact that is not already in the session the end result will be that the session won't have that fact.
                    ;; If retractions came first then we'd first retract a fact that isn't in the session, which doesn't do anything,
                    ;; and then later we would insert the fact.
                    (doseq [[alpha-roots fact-group] (get-alphas-fn insertions)
                            root alpha-roots]
                      (alpha-activate root fact-group transient-memory transport transient-listener))

                    (doseq [[alpha-roots fact-group] (get-alphas-fn retractions)
                            root alpha-roots]
                      (alpha-retract root fact-group transient-memory transport transient-listener))

                    (fire-rules* rulebase
                                 (:production-nodes rulebase)
                                 transient-memory
                                 transport
                                 transient-listener
                                 get-alphas-fn
                                 ;; This continues to use the cancelling cache after the first batch of insertions and retractions.
                                 ;; If this is suboptimal for some workflows we can revisit this.
                                 update-cache)))))

      (LocalSession. rulebase
                     (mem/to-persistent! transient-memory)
                     transport
                     (l/to-persistent! transient-listener)
                     get-alphas-fn
                     [])))

  (query [session query params]
    (let [query-node (get-in rulebase [:query-nodes query])]
      (when (= nil query-node)
        (platform/throw-error (str "The query " query " is invalid or not included in the rule base.")))
      (when-not (= (into #{} (keys params)) ;; nil params should be equivalent to #{}
                   (:param-keys query-node))
        (platform/throw-error (str "The query " query " was not provided with the correct parameters, expected: "
                                   (:param-keys query-node) ", provided: " (set (keys params)))))

      (->> (mem/get-tokens memory query-node params)

           ;; Get the bindings for each token and filter generate symbols.
           (map (fn [{bindings :bindings}]

                  ;; Filter generated symbols. We check first since this is an uncommon flow.
                  (if (some #(re-find #"__gen" (name %)) (keys bindings))

                    (into {} (remove (fn [[k v]] (re-find #"__gen"  (name k)))
                                     bindings))
                    bindings))))))

  (components [session]
    {:rulebase rulebase
     :memory memory
     :transport transport
     :listeners (l/flatten-listener listener)
     :get-alphas-fn get-alphas-fn}))

(defn assemble
  "Assembles a session from the given components, which must be a map
   containing the following:

   :rulebase A recorec matching the clara.rules.compiler/Rulebase structure.
   :memory An implementation of the clara.rules.memory/IMemoryReader protocol
   :transport An implementation of the clara.rules.engine/ITransport protocol
   :listeners A vector of listeners implementing the clara.rules.listener/IPersistentListener protocol
   :get-alphas-fn The function used to return the alpha nodes for a fact of the given type."

  [{:keys [rulebase memory transport listeners get-alphas-fn]}]
  (LocalSession. rulebase
                 memory
                 transport
                 (if (> (count listeners) 0)
                   (l/delegating-listener listeners)
                   l/default-listener)
                 get-alphas-fn
                 []))

(defn with-listener
  "Return a new session with the listener added to the provided session,
   in addition to all listeners previously on the session."
  [session listener]
  (let [{:keys [listeners] :as components} (components session)]
    (assemble (assoc components
                     :listeners
                     (conj listeners
                           listener)))))

(defn remove-listeners
  "Return a new session with all listeners matching the predicate removed"
  [session pred]
  (let [{:keys [listeners] :as components} (components session)]
    (if (some pred listeners)
      (assemble (assoc components
                       :listeners
                       (into [] (remove pred) listeners)))
      session)))

(defn find-listeners
  "Return all listeners on the session matching the predicate."
  [session pred]
  (let [{:keys [listeners]} (components session)]
    (filterv pred listeners)))

(defn local-memory
  "Returns a local, in-process working memory."
  [rulebase transport activation-group-sort-fn activation-group-fn alphas-fn]
  (let [memory (mem/to-transient (mem/local-memory rulebase activation-group-sort-fn activation-group-fn alphas-fn))]
    (doseq [beta-node (:beta-roots rulebase)]
      (left-activate beta-node {} [empty-token] memory transport l/default-listener))
    (mem/to-persistent! memory)))

(defn options->activation-group-sort-fn
  "Given the map of options for a session, construct an activation group sorting
  function that takes into account the user-provided salience and internal salience.
  User-provided salience is considered first.  Under normal circumstances this function should
  only be called by Clara itself."
  [options]
  (let [user-activation-group-sort-fn (or (get options :activation-group-sort-fn)
                                          ;; Default to sort by descending numerical order.
                                          >)]

    ;; Compare user-provided salience first, using either the provided salience function or the default,
    ;; then use the internal salience if the former does not provide an ordering between the two salience values.
    (fn [salience1 salience2]
      (let [forward-result (user-activation-group-sort-fn (nth salience1 0)
                                                          (nth salience2 0))]
        (if (number? forward-result)
          (if (= 0 forward-result)
            (> (nth salience1 1)
               (nth salience2 1))

            forward-result)
          (let [backward-result (user-activation-group-sort-fn (nth salience2 0)
                                                               (nth salience1 0))
                forward-bool (boolean forward-result)
                backward-bool (boolean backward-result)]
            ;; Since we just use Clojure functions, for example >, equality may be implied
            ;; by returning false for comparisons in both directions rather than by returning 0.
            ;; Furthermore, ClojureScript will use truthiness semantics rather than requiring a
            ;; boolean (unlike Clojure), so we use the most permissive semantics between Clojure
            ;; and ClojureScript.
            (if (not= forward-bool backward-bool)
              forward-bool
              (> (nth salience1 1)
                 (nth salience2 1)))))))))

(def ^:private internal-salience-levels {:default 0
                                         ;; Extracted negations need to be prioritized over their original
                                         ;; rules since their original rule could fire before the extracted condition.
                                         ;; This is a problem if the original rule performs an unconditional insertion
                                         ;; or has other side effects not controlled by truth maintenance.
                                         :extracted-negation 1})

(defn options->activation-group-fn
  "Given a map of options for a session, construct a function that takes a production
  and returns the activation group to which it belongs, considering both user-provided
  and internal salience.  Under normal circumstances this function should only be called by
  Clara itself."
  [options]
  (let [rule-salience-fn (or (:activation-group-fn options)
                             (fn [production] (or (some-> production :props :salience)
                                                  0)))]

    (fn [production]
      [(rule-salience-fn production)
       (internal-salience-levels (or (some-> production :props :clara-rules/internal-salience)
                                     :default))])))
