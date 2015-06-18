(ns clara.macros
  "Forward-chaining rules for Clojure. The primary API is in this namespace"
  (:require [clara.rules.engine :as eng]
            [clara.rules.memory :as mem]
            [clara.rules.compiler :as com]
            [clara.rules.compiler.expressions :as expr] [clara.rules.compiler.helpers :as hlp] [clara.rules.compiler.trees :as trees]
            [clara.rules.dsl :as dsl]            
            [cljs.analyzer :as ana]
            [cljs.env :as env]
            [clojure.set :as s]))


;; Store production in cljs.env/*compiler* under ::productions seq?
(defn- add-production [name production]
  (swap! env/*compiler* assoc-in [::productions (hlp/cljs-ns) name] production))

(defn- get-productions-from-namespace 
  "Returns a map of names to productions in the given namespace."
  [namespace]
  ;; TODO: remove need for ugly eval by changing our quoting strategy.
  (let [productions (get-in @env/*compiler* [::productions namespace])]
    (map eval (vals productions))))

(defn- get-productions
  "Return the productions from the source"
  [source]
  (cond
   (symbol? source) (get-productions-from-namespace source)
   (coll? source) (seq source)
   :else (throw (IllegalArgumentException. "Unknown source value type passed to defsession"))))

(defmacro defrule 
  [name & body]
  (let [doc (if (string? (first body)) (first body) nil)
        body (if doc (rest body) body)
        properties (if (map? (first body)) (first body) nil)
        definition (if properties (rest body) body)
        {:keys [lhs rhs]} (dsl/split-lhs-rhs definition)

        production (cond-> (dsl/parse-rule* lhs rhs properties {})
                           name (assoc :name (str (clojure.core/name (hlp/cljs-ns)) "/" (clojure.core/name name)))
                           doc (assoc :doc doc))]
    (add-production name production)
    `(def ~name
       ~production)))

(defmacro defquery 
  [name & body]
  (let [doc (if (string? (first body)) (first body) nil)
        binding (if doc (second body) (first body))
        definition (if doc (drop 2 body) (rest body) )

        query (cond-> (dsl/parse-query* binding definition {})
                      name (assoc :name (str (clojure.core/name (hlp/cljs-ns)) "/" (clojure.core/name name)))
                      doc (assoc :doc doc))]
    (add-production name query)
    `(def ~name
       ~query)))

(defn- gen-beta-network
  "Generates the beta network from the beta tree. "
  ([beta-nodes
    parent-bindings]
     (vec
      (for [beta-node beta-nodes
            :let [{:keys [condition children id production query join-bindings]} beta-node

                  constraint-bindings (expr/variables-as-keywords (:constraints condition))

                  ;; Get all bindings from the parent, condition, and returned fact.
                  all-bindings (cond-> (s/union parent-bindings constraint-bindings)
                                       ;; Optional fact binding from a condition.
                                       (:fact-binding condition) (conj (:fact-binding condition))
                                       ;; Optional accumulator result.
                                       (:result-binding beta-node) (conj (:result-binding beta-node)))]]

        (case (:node-type beta-node)

          :join
          `(eng/->JoinNode
            ~id
            '~condition
            ~(gen-beta-network children all-bindings)
            ~join-bindings)

          :negation
          `(eng/->NegationNode
            ~id
            '~condition
            ~(gen-beta-network children all-bindings)
            ~join-bindings)
          
          :test
          `(eng/->TestNode
            ~id
            ~(com/compile-test (:constraints condition))
            ~(gen-beta-network children all-bindings))

          :accumulator
          `(eng/->AccumulateNode
            ~id
            {:accumulator '~(:accumulator beta-node)
             :from '~condition}
            ~(:accumulator beta-node)
            ~(:result-binding beta-node)
            ~(gen-beta-network children all-bindings)
            ~join-bindings)

          :production
          `(eng/->ProductionNode
           ~id
           '~production
           ~(com/compile-action all-bindings (:rhs production) (:env production)))

          :query
          `(eng/->QueryNode
           ~id
           '~query
           ~(:params query))
          )))))

(defn- compile-alpha-nodes
  [alpha-nodes]
  (vec
   (for [{:keys [condition beta-children env]} alpha-nodes
         :let [{:keys [type constraints fact-binding args]} condition]]

     {:type (hlp/effective-type type)
      :alpha-fn (com/compile-condition type (first args) constraints fact-binding env)
      :children (vec beta-children)
      })))

(defmacro defsession 
  "Creates a sesson given a list of sources and keyword-style options, which are typically ClojureScript namespaces.

  Each source is eval'ed at compile time, in Clojure (not ClojureScript.)

  If the eval result is a symbol, it is presumed to be a ClojureScript
  namespace, and all rules and queries defined in that namespace will
  be found and used.

  If the eval result is a collection, it is presumed to be a
  collection of productions. Note that although the collection must
  exist in the compiling Clojure runtime (since the eval happens at
  macro-expansion time), any expressions in the rule or query
  definitions will be executed in ClojureScript.

  Typical usage would be like this, with a session defined as a var:

(defsession my-session 'example.namespace)

That var contains an immutable session that then can be used as a starting point to create sessions with
caller-provided data. Since the session itself is immutable, it can be safely used from multiple threads
and will not be modified by callers. So a user might grab it, insert facts, and otherwise
use it as follows:

   (-> my-session
     (insert (->Temperature 23))
     (fire-rules))  
"
  [name & sources-and-options]
  (let [sources (take-while #(not (keyword? %)) sources-and-options)
        options (apply hash-map (drop-while #(not (keyword? %)) sources-and-options))
        ;; Eval to unquote ns symbols, and to eval exprs to look up
        ;; explicit rule sources
        sources (eval (vec sources))
        productions (vec (for [source sources
                               production (get-productions source)]
                           production))

        beta-tree (trees/to-beta-tree productions) 
        beta-network (gen-beta-network beta-tree #{})

        alpha-tree (trees/to-alpha-tree beta-tree)
        alpha-nodes (compile-alpha-nodes alpha-tree)]

    `(let [beta-network# ~beta-network
           alpha-nodes# ~alpha-nodes
           productions# '~productions
           options# ~options]
       (def ~name (clara.rules/assemble-session beta-network# alpha-nodes# productions# options#)))))
