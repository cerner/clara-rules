(ns clara.rules.compiler
  "This namespace is for internal use and may move in the future.
   This is the Clara rules compiler, translating raw data structures into compiled versions and functions.
   Most users should use only the clara.rules namespace."
  (:require [clojure.reflect :as reflect]
            [clojure.core.reducers :as r]
            [clojure.set :as s]
            [clara.rules.engine :as eng]
            [clara.rules.listener :as listener]
            [clara.rules.platform :as platform]
            [clojure.string :as string]
            [clojure.walk :as walk]
            [clara.rules.schema :as schema]
            [schema.core :as sc]
            [schema.macros :as sm])

  (:import [clara.rules.engine ProductionNode QueryNode HashJoinNode ExpressionJoinNode
            NegationNode TestNode AccumulateNode AlphaNode LocalTransport
            LocalSession Accumulator]
           [java.beans PropertyDescriptor]))

;; Protocol for loading rules from some arbitrary source.
(defprotocol IRuleSource
  (load-rules [source]))

;; These nodes exist in the beta network.
(def BetaNode (sc/either ProductionNode QueryNode HashJoinNode ExpressionJoinNode
                         NegationNode TestNode AccumulateNode))

;; A rulebase -- essentially an immutable Rete network with a collection of alpha and beta nodes and supporting structure.
(sc/defrecord Rulebase [;; Map of matched type to the alpha nodes that handle them.
                        alpha-roots :- {sc/Any [AlphaNode]}
                        ;; Root beta nodes (join, accumulate, etc.)
                        beta-roots :- [BetaNode]
                        ;; Productions in the rulebase.
                        productions :- [schema/Production]
                        ;; Production nodes.
                        production-nodes :- [ProductionNode]
                        ;; Map of queries to the nodes hosting them.
                        query-nodes :- {sc/Any QueryNode}
                        ;; May of id to one of the beta nodes (join, accumulate, etc)
                        id-to-node :- {sc/Num BetaNode}])

(def ^:private reflector
  "For some reason (bug?) the default reflector doesn't use the
   Clojure dynamic class loader, which prevents reflecting on
  `defrecords`.  Work around by supplying our own which does."
  (clojure.reflect.JavaReflector. (clojure.lang.RT/makeClassLoader)))

;; This technique borrowed from Prismatic's schema library.
(defn compiling-cljs?
  "Return true if we are currently generating cljs code.  Useful because cljx does not
         provide a hook for conditional macro expansion."
  []
  (boolean
   (when-let [n (find-ns 'cljs.analyzer)]
     (when-let [v (ns-resolve n '*cljs-file*)]

       ;; We perform this require only if we are compiling ClojureScript
       ;; so non-ClojureScript users do not need to pull in
       ;; that dependency.
       (require 'clara.macros)
       @v))))

(defn get-namespace-info
  "Get metadata about the given namespace."
  [namespace]
  (when-let [n (and (compiling-cljs?) (find-ns 'cljs.env))]
    (when-let [v (ns-resolve n '*compiler*)]
      (get-in @@v [ :cljs.analyzer/namespaces namespace]))))

(defn cljs-ns
  "Returns the ClojureScript namespace being compiled during Clojurescript compilation."
  []
  (if (compiling-cljs?)
    (-> 'cljs.analyzer (find-ns) (ns-resolve '*cljs-ns*) deref)
    nil))

(defn resolve-cljs-sym
  "Resolves a ClojureScript symbol in the given namespace."
  [ns-sym sym]
  (let [ns-info (get-namespace-info ns-sym)]
    (if (namespace sym)

      ;; Symbol qualified by a namespace, so look it up in the requires info.
      (if-let [source-ns (get-in ns-info [:requires (symbol (namespace sym))])]
        (symbol (name source-ns) (name sym))
        ;; Not in the requires block, so assume the qualified name is a refers and simply return the symbol.
        sym)

      ;; Symbol is unqualified, so check in the uses block.
      (if-let [source-ns (get-in ns-info [:uses sym])]
        (symbol (name source-ns) (name sym))

        ;; Symbol not found in eiher block, so attempt to retrieve it from
        ;; the current namespace.
        (if (get-in (get-namespace-info ns-sym) [:defs sym])
          (symbol (name ns-sym) (name sym))
          nil)))))

(defn- get-cljs-accessors
  "Returns accessors for ClojureScript. WARNING: this touches
  ClojureScript implementation details that may change."
  [sym]
  (let [resolved (resolve-cljs-sym (cljs-ns) sym)
        constructor (symbol (str "->" (name resolved)))
        namespace-info (get-namespace-info (symbol (namespace resolved)))
        constructor-info (get-in namespace-info [:defs constructor])]

    (if constructor-info
      (into {}
            (for [field (first (:method-params constructor-info))]
              [field (keyword (name field))]))
      [])))


(defn- get-field-accessors
  "Given a clojure.lang.IRecord subclass, returns a map of field name to a
   symbol representing the function used to access it."
  [cls]
  (into {}
        (for [field-name (clojure.lang.Reflector/invokeStaticMethod ^Class cls
                                                                    "getBasis"
                                                                    ^"[Ljava.lang.Object;" (make-array Object 0))]
          ;; Do not preserve the metadata on the field names returned from
          ;; IRecord.getBasis() since it may not be safe to eval this metadata
          ;; in other contexts.  This mostly applies to :tag metadata that may
          ;; be unqualified class names symbols at this point.
          [(with-meta field-name {}) (symbol (str ".-" field-name))])))

(defn- get-bean-accessors
  "Returns a map of bean property name to a symbol representing the function used to access it."
  [cls]
  (into {}
        ;; Iterate through the bean properties, returning tuples and the corresponding methods.
        (for [^PropertyDescriptor property (seq (.. java.beans.Introspector
                                                    (getBeanInfo cls)
                                                    (getPropertyDescriptors)))]

          [(symbol (string/replace (.. property (getName)) #"_" "-")) ; Replace underscore with idiomatic dash.
           (symbol (str "." (.. property (getReadMethod) (getName))))])))

(defn effective-type [type]
  (if (compiling-cljs?)
    type

    (if (symbol? type)
      (.loadClass (clojure.lang.RT/makeClassLoader) (name type))
      type)))

(defn get-fields
  "Returns a map of field name to a symbol representing the function used to access it."
  [type]
  (if (compiling-cljs?)

    ;; Get ClojureScript fields.
    (if (symbol? type)
      (get-cljs-accessors type)
      [])

    ;; Attempt to load the corresponding class for the type if it's a symbol.
    (let [type (effective-type type)]

      (cond
       (isa? type clojure.lang.IRecord) (get-field-accessors type)
       (class? type) (get-bean-accessors type) ; Treat unrecognized classes as beans.
       :default []))))

(defn- equality-expression? [expression]
  (let [qualify-when-sym #(when-let [resolved (and (symbol? %)
                                                   (resolve %))]
                            (and (var? resolved)
                                 (symbol (-> resolved meta :ns ns-name name)
                                         (-> resolved meta :name name))))
        op (first expression)]
    ;; Check for unqualified = or == to support original Clara unification
    ;; syntax where clojure.core/== was supposed to be excluded explicitly.
    (boolean (or (#{'= '== 'clojure.core/= 'clojure.core/==} op)
                 (#{'clojure.core/= 'clojure.core/==} (qualify-when-sym op))))))

(defn- compile-constraints [exp-seq assigment-set]
  (if (empty? exp-seq)
    `((deref ~'?__bindings__))
    (let [ [[cmp a b :as exp] & rest] exp-seq
           compiled-rest (compile-constraints rest assigment-set)
           eq-expr? (equality-expression? exp)
           a-in-assigment (and eq-expr? (and (symbol? a) (assigment-set (keyword a))))
           b-in-assigment (and eq-expr? (and (symbol? b) (assigment-set (keyword b))))]
      (cond
       a-in-assigment
       (if b-in-assigment
         `((let [a-exist# (contains? (deref ~'?__bindings__) ~(keyword a))
                 b-exist# (contains? (deref ~'?__bindings__) ~(keyword b))]
             (when (and (not a-exist#) (not b-exist#)) (throw (Throwable. "Binding undefine variables")))
             (when (not a-exist#) (swap! ~'?__bindings__ assoc ~(keyword a) ((deref ~'?__bindings__) ~(keyword b))))
             (when (not b-exist#) (swap! ~'?__bindings__ assoc ~(keyword b) ((deref ~'?__bindings__) ~(keyword a))))
             (if (or (not a-exist#) (not b-exist#) (= ((deref ~'?__bindings__) ~(keyword a)) ((deref ~'?__bindings__) ~(keyword b))))
               (do ~@compiled-rest)
               nil)))
         (cons `(swap! ~'?__bindings__ assoc ~(keyword a) ~b) compiled-rest))
       b-in-assigment
       (cons `(swap! ~'?__bindings__ assoc ~(keyword b) ~a) compiled-rest)
       ;; not a unification
       :else
       (list (list 'if exp (cons 'do compiled-rest) nil))))))

(defn flatten-expression
  "Flattens expression as clojure.core/flatten does, except will flatten
   anything that is a collection rather than specifically sequential."
  [expression]
  (filter (complement coll?)
          (tree-seq coll? seq expression)))

(defn variables-as-keywords
  "Returns symbols in the given s-expression that start with '?' as keywords"
  [expression]
  (into #{} (for [item (flatten-expression expression)
                  :when (and (symbol? item)
                             (= \? (first (name item))))]
              (keyword  item))))

(defn- add-meta
  "Helper function to add metadata."
  [fact-symbol fact-type]
  (if (class? fact-type)
    (vary-meta fact-symbol assoc :tag (symbol (.getName ^Class fact-type)))
    fact-symbol))

(defn compile-condition
  "Returns a function definition that can be used in alpha nodes to test the condition."
  [type destructured-fact constraints result-binding env]
  (let [;; Get a map of fieldnames to access function symbols.
        accessors (get-fields type)

        binding-keys (variables-as-keywords constraints)
        ;; The assignments should use the argument destructuring if provided, or default to accessors otherwise.
        assignments (if destructured-fact
                      ;; Simply destructure the fact if arguments are provided.
                      [destructured-fact '?__fact__]
                      ;; No argument provided, so use our default destructuring logic.
                      (concat '(this ?__fact__)
                              (mapcat (fn [[name accessor]]
                                        [name (list accessor '?__fact__)])
                                      accessors)))

        ;; The destructured environment, if any
        destructured-env (if (> (count env) 0)
                           {:keys (mapv #(symbol (name %)) (keys env))}
                           '?__env__)

        ;; Initial bindings used in the return of the compiled condition expresion.
        initial-bindings (if result-binding {result-binding '?__fact__}  {})]

    `(fn [~(add-meta '?__fact__ type)
          ~destructured-env] ;; TODO: add destructured environment parameter...
       (let [~@assignments
             ~'?__bindings__ (atom ~initial-bindings)]
         (do ~@(compile-constraints constraints (set binding-keys)))))))

;; FIXME: add env...
(defn compile-test [tests]
  (let [binding-keys (variables-as-keywords tests)
        assignments (mapcat #(list (symbol (name %)) (list 'get-in '?__token__ [:bindings %])) binding-keys)]

    `(fn [~'?__token__]
      (let [~@assignments]
        (and ~@tests)))))

(defn compile-action
  "Compile the right-hand-side action of a rule, returning a function to execute it."
  [binding-keys rhs env]
  (let [assignments (mapcat #(list (symbol (name %)) (list 'get-in '?__token__ [:bindings %])) binding-keys)

        ;; The destructured environment, if any.
        destructured-env (if (> (count env) 0)
                           {:keys (mapv #(symbol (name %)) (keys env))}
                           '?__env__)]
    `(fn [~'?__token__  ~destructured-env]
       (let [~@assignments]
         ~rhs))))

(defn compile-accum
  "Used to create accumulators that take the environment into account."
  [accum env]
  (let [destructured-env
        (if (> (count env) 0)
          {:keys (mapv #(symbol (name %)) (keys env))}
          '?__env__)]
    `(fn [~destructured-env]
       ~accum)))

(defn compile-join-filter
  "Compiles to a predicate function that ensures the given items can be unified. Returns a ready-to-eval
   function that accepts a token, a fact, and an environment, and returns truthy if the given fact satisfies
   the criteria."
  [{:keys [type constraints args] :as unification-condition} env]
  (let [accessors (get-fields type)

        binding-keys (variables-as-keywords constraints)

        destructured-env (if (> (count env) 0)
                           {:keys (mapv #(symbol (name %)) (keys env))}
                           '?__env__)

        destructured-fact (first args)

        fact-assignments (if destructured-fact
                           ;; Simply destructure the fact if arguments are provided.
                           [destructured-fact '?__fact__]
                           ;; No argument provided, so use our default destructuring logic.
                           (concat '(this ?__fact__)
                                   (mapcat (fn [[name accessor]]
                                             [name (list accessor '?__fact__)])
                                           accessors)))

        token-assignments (mapcat #(list (symbol (name %)) (list 'get-in '?__token__ [:bindings %])) binding-keys)

        assignments (concat
                     fact-assignments
                     token-assignments)]

    `(fn [~'?__token__
         ~(add-meta '?__fact__ type)
          ~destructured-env]
       (let [~@assignments
             ~'?__bindings__ (atom {})]
         (do ~@(compile-constraints constraints (set binding-keys)))))))

(defn- expr-type [expression]
  (if (map? expression)
    :condition
    (first expression)))

(defn- cartesian-join [lists lst]
  (if (seq lists)
    (let [[h & t] lists
          c (cartesian-join t lst)]
      (mapcat
       (fn [l]
         (map #(conj % l) c))
       h))
    [lst]))

(defn to-dnf
  "Convert a lhs expression to disjunctive normal form."
  [expression]

  ;; Always validate the expression schema, as this is only done at compile time.
  (sc/validate schema/Condition expression)
  (condp = (expr-type expression)
    ;; Individual conditions can return unchanged.
    :condition
    expression

    :test
    expression

    :exists
    expression

    ;; Apply de Morgan's law to push negation nodes to the leaves.
    :not
    (let [children (rest expression)
          child (first children)]

      (when (not= 1 (count children))
        (throw (RuntimeException. "Negation must have only one child.")))

      (condp = (expr-type child)

        ;; If the child is a single condition, simply return the ast.
        :condition expression

        :test expression

        :exists expression

        ;; DeMorgan's law converting conjunction to negated disjuctions.
        :and (to-dnf (into [:or] (for [grandchild (rest child)] [:not grandchild])))

        ;; DeMorgan's law converting disjuction to negated conjuctions.
        :or  (to-dnf (into [:and] (for [grandchild (rest child)] [:not grandchild])))))

    ;; For all others, recursively process the children.
    (let [children (map to-dnf (rest expression))
          ;; Get all conjunctions, which will not conain any disjunctions since they were processed above.
          conjunctions (filter #(#{:and :condition :not} (expr-type %)) children)]

      ;; If there is only one child, the and or or operator can simply be eliminated.
      (if (= 1 (count children))
        (first children)

        (condp = (expr-type expression)

          :and
          (let [disjunctions (map rest (filter #(= :or (expr-type %)) children))
                ;; Merge all child conjunctions into a single conjunction.
                combine-conjunctions (fn [children]
                                       (into [:and]
                                             (apply concat
                                                    (for [child children]
                                                      (if (= :and (expr-type child))
                                                        (rest child)
                                                        [child])))))]
            (if (empty? disjunctions)
              (combine-conjunctions children)
              (into [:or]
                    (for [c (cartesian-join disjunctions conjunctions)]
                      (combine-conjunctions c)))))
          :or
          ;; Merge all child disjunctions into a single disjunction.
          (let [disjunctions (mapcat rest (filter #(#{:or} (expr-type %)) children))]
            (into [:or] (concat disjunctions conjunctions))))))))

(defn- non-equality-unification? [expression]
  "Returns true if the given expression does a non-equality unification against a variable,
   indicating it can't be solved by simple unification."
  (let [found-complex (atom false)
        process-form (fn [form]
                       (when (and (seq? form)
                                  (not (equality-expression? form))
                                  (some (fn [sym] (and (symbol? sym)
                                                      (.startsWith (name sym) "?")))
                                        (flatten-expression form)))

                         (reset! found-complex true))

                       form)]

    ;; Walk the expression to find use of a symbol that can't be solved by equality-based unificaiton.
    (doall (walk/postwalk process-form expression))

    @found-complex))

(defn condition-type
  "Returns the type of a single condition that has been transformed
   to disjunctive normal form. The types are: :negation, :accumulator, :test, :exists, and :join"
  [condition]
  (let [is-negation (= :not (first condition))
        is-exists (= :exists (first condition))
        accumulator (:accumulator condition)
        result-binding (:result-binding condition) ; Get the optional result binding used by accumulators.
        condition (cond
                   is-negation (second condition)
                   accumulator (:from condition)
                   :default condition)
        node-type (cond
                   is-negation :negation
                   is-exists :exists
                   accumulator :accumulator
                   (:type condition) :join
                   :else :test)]

    node-type))

(defn- add-to-beta-tree
  "Adds a sequence of conditions and the corresponding production to the beta tree."
  [beta-nodes
   [[condition env] & more]
   bindings
   production]
  (let [node-type (condition-type condition)
        accumulator (:accumulator condition)
        result-binding (:result-binding condition) ; Get the optional result binding used by accumulators.
        condition (cond
                   (= :negation node-type) (second condition)
                   accumulator (:from condition)
                   :default condition)

        ;; Get the non-equality unifications so we can handle them
        join-filter-expressions (if (and (or (= :accumulator node-type)
                                             (= :negation node-type)
                                             (= :join node-type))
                                         (some non-equality-unification? (:constraints condition)))

                                    (assoc condition :constraints (filterv non-equality-unification? (:constraints condition)))

                                    nil)

        ;; Remove instances of non-equality constraints from accumulator
        ;; and negation nodes, since those are handled with specialized node implementations.
        condition (if (and (or (= :accumulator node-type)
                               (= :negation node-type)
                               (= :join node-type))
                           (some non-equality-unification? (:constraints condition)))

                    (assoc condition
                      :constraints (into [] (remove non-equality-unification? (:constraints condition)))
                      :original-constraints (:constraints condition))

                    condition)

        ;; For the sibling beta nodes, find a match for the candidate.
        matching-node (first (for [beta-node beta-nodes
                                   :when (and (= condition (:condition beta-node))
                                              (= node-type (:node-type beta-node))
                                              (= env (:env beta-node))
                                              (= result-binding (:result-binding beta-node))
                                              (= accumulator (:accumulator beta-node)))]
                               beta-node))

        other-nodes (remove #(= matching-node %) beta-nodes)
        cond-bindings (variables-as-keywords (:constraints condition))

        ;; Create either the rule or query node, as appropriate.
        production-node (if (:rhs production)
                          {:node-type :production
                           :production production}
                          {:node-type :query
                           :query production})]


    (vec
     (conj
      other-nodes
      (if condition
        ;; There are more conditions, so recurse.
        (if matching-node
          (assoc matching-node
            :children
            (add-to-beta-tree (:children matching-node)
                              more
                              (cond-> (s/union bindings cond-bindings)
                                      result-binding (conj result-binding)
                                      (:fact-binding condition) (conj (:fact-binding condition)))
                              production))

          (cond->
           {:node-type node-type
            :condition condition
            :children (add-to-beta-tree []
                                        more
                                        (cond-> (s/union bindings cond-bindings)
                                                result-binding (conj result-binding)
                                                (:fact-binding condition) (conj (:fact-binding condition)))
                                        production)
            :env (or env {})}

           ;; Add the join bindings to join, accumulator or negation nodes.
           (#{:join :negation :accumulator} node-type) (assoc :join-bindings (s/intersection bindings cond-bindings))

           accumulator (assoc :accumulator accumulator)

           result-binding (assoc :result-binding result-binding)

           join-filter-expressions (assoc :join-filter-expressions join-filter-expressions)))

        ;; There are no more conditions, so add our query or rule.
        (if matching-node
          (update-in matching-node [:children] conj production-node)
          production-node))))))

(defn- gen-compare
  "Generic compare function for arbitrary Clojure data structures.
   The only guarantee is the ordering of items will be consistent
   between invocations."
  [left right]
  (cond

   ;; Handle the nil cases first to ensure nil-safety.
   (and (nil? left) (nil? right))
   0

   (nil? left)
   -1

   (nil? right)
   1

   ;; Ignore functions for our comparison purposes,
   ;; since we won't distinguish rules by them.
   (and (fn? left) (fn? right))
   0

   ;; If the types differ, compare based on their names.
   (not= (type left)
         (type right))
   (compare (.getName ^Class (type left))
            (.getName ^Class (type right)))

   ;; Compare items in a sequence until we find a difference.
   (sequential? left)
   (loop [left-seq left
          right-seq right]

     (if (and (seq left-seq) (seq right-seq))

       ;; Both sequences have content, so compare them and recur if necessary.
       (let [result (gen-compare (first left-seq) (first right-seq)) ]
         (if (not= 0 result)
           result
           (recur (rest left-seq) (rest right-seq))))

       ;; At least one sequence is empty.
       (cond

        (seq left-seq) 1
        (seq right-seq) -1
        :default 0)))

   ;; Covert maps to sequences sorted by keys and compare those sequences.
   (map? left)
   (let [kv-sort-fn (fn [[key1 _] [key2 _]] (gen-compare key1 key2))
         left-kvs (sort kv-sort-fn (seq left))
         right-kvs (sort kv-sort-fn (seq right))  ]

     (gen-compare left-kvs right-kvs))

   ;; The content is comparable and not a sequence, so simply compare them.
   (instance? Comparable left)
   (compare left right)

   ;; Unknown items are just treated as equal for our purposes,
   ;; since we can't define an ordering.
   :default 0
   ))

(defn- is-variable?
  "Returns true if the given expression is a variable (a symbol prefixed by ?)"
  [expr]
  (and (symbol? expr)
       (.startsWith (name expr) "?")))

(defn- extract-exists
  "Converts :exists operations into an accumulator to detect
   the presence of a fact and a test to check that count is
   greater than zero.

   It may be possible to replace this conversion with a specialized
   ExtractNode in the future, but this transformation is simple
   and meets the functional needs."
  [conditions]
  (for [condition conditions
        expanded (if (= :exists (condition-type condition))
                   ;; This is an :exists condition, so expand it
                   ;; into an accumulator and a test.
                   (let [exists-count (gensym "?__gen__")]
                       [{:accumulator '(clara.rules.accumulators/count)
                         :from (second condition)
                         :result-binding (keyword exists-count)}
                        {:constraints [(list '> exists-count 0)]}])

                   ;; This is not an :exists condition, so do not change it.
                   [condition])]

    expanded))

(defn- classify-variables
  "Classifies the variables found in the given contraints into 'bound' vs 'free'
   variables.  Bound variables are those that are found in a valid
   equality-based, top-level binding form.  All other variables encountered are
   considered free.  Returns a tuple of the form
   [bound-variables free-variables]
   where bound-variables and free-variables are the sets of bound and free
   variables found in the constraints respectively."
  [constraints]
  (reduce (fn [[bound-variables free-variables] constraint]
            ;; Only top-level constraint forms can introduce new variable bindings.
            ;; If the top-level constraint is an equality expression, add the
            ;; bound variables to the set of bound variables.
            (if (and (seq? constraint) (equality-expression? constraint))
              [(->> (rest constraint)
                    (filterv is-variable?)
                    (into bound-variables))
               ;; Any other variables in a nested form are now considered "free".
               (->> (rest constraint)
                    ;; We already have checked this level symbols for bound variables.
                    (remove symbol?)
                    flatten-expression
                    (filterv is-variable?)
                    (into free-variables))]

              ;; Binding forms are not supported nested within other forms, so
              ;; any variables that occur now are considered "free" variables.
              [bound-variables
               (->> (flatten-expression constraint)
                    (filterv is-variable?)
                    (into free-variables))]))
          [#{} #{}]
          constraints))

(defn- sort-conditions
  "Performs a topologic sort of conditions to ensure variables needed by
   child conditions are bound."
  [conditions]

  ;; Get the bound and unbound variables for all conditions.
  (let [classified-conditions
        (for [condition conditions
              :let [constraints (condp = (condition-type condition)
                                  :accumulator (get-in condition [:from :constraints])
                                  :negation (:constraints (second condition))
                                  (:constraints condition))

                    [bound-variables unbound-variables] (classify-variables constraints)]]
          {:bound (cond-> bound-variables
                    (:fact-binding condition) (conj (symbol (name (:fact-binding condition))))
                    (:result-binding condition) (conj (symbol (name (:result-binding condition)))))

           :unbound unbound-variables
           :condition condition
           :is-accumulator (= :accumulator (condition-type condition))})]

    (loop [sorted-conditions []
           bound-variables #{}
           remaining-conditions classified-conditions]

      (if (empty? remaining-conditions)
        ;; No more conditions to sort, so return the raw conditions
        ;; in sorted order.
        (map :condition sorted-conditions)

        ;; Unsatisfied conditions remain, so find ones we can satisfy.
        (let [satisfied? (fn [classified-condition]
                           (clojure.set/subset? (:unbound classified-condition)
                                                bound-variables))

              ;; Find non-accumulator conditions that are satisfied. We defer
              ;; accumulators until later in the rete network because they
              ;; may fire a default value if all needed bindings earlier
              ;; in the network are satisfied.
              satisfied-non-accum? (fn [classified-condition]
                                     (and (not (:is-accumulator classified-condition))
                                          (clojure.set/subset? (:unbound classified-condition)
                                                               bound-variables)))

              has-satisfied-non-accum (some satisfied-non-accum? remaining-conditions)

              newly-satisfied (if has-satisfied-non-accum
                                (filter satisfied-non-accum? remaining-conditions)
                                (filter satisfied? remaining-conditions))

              still-unsatisfied (if has-satisfied-non-accum
                                  (remove satisfied-non-accum? remaining-conditions)
                                  (remove satisfied? remaining-conditions))

              updated-bindings (apply clojure.set/union bound-variables
                                      (map :bound newly-satisfied))]

          ;; If no existing variables can be satisfied then the production is invalid.
          (when (empty? newly-satisfied)

            ;; Get the subset of variables that cannot be satisfied.
            (let [unsatisfiable (clojure.set/difference
                                 (apply clojure.set/union (map :unbound still-unsatisfied))
                                 bound-variables)]
              (throw (ex-info (str "Using variable that is not previously bound. This can happen "
                                   "when an expression uses a previously unbound variable, "
                                   "or if a variable is referenced in a nested part of a parent "
                                   "expression, such as (or (= ?my-expression my-field) ...). " \newline
                                   "Unbound variables: "
                                   unsatisfiable)
                              {:variables unsatisfiable}))))

          (recur (into sorted-conditions newly-satisfied)
                 updated-bindings
                 still-unsatisfied))))))

(defn- get-conds
  "Returns a sequence of [condition environment] tuples and their corresponding productions."
  [production]

  (let [lhs-expression (into [:and] (:lhs production)) ; Add implied and.
        expression  (to-dnf lhs-expression)
        disjunctions (if (= :or (first expression))
                       (rest expression)
                       [expression])]

    ;; Now we've split the production into one ore more disjunctions that
    ;; can be processed independently. Commonality between disjunctions will
    ;; be merged when building the Rete network.
    (for [disjunction disjunctions

          :let [conditions (if (and (vector? disjunction)
                                    (= :and (first disjunction)))
                             (rest disjunction)
                             [disjunction])

                ;; Convert exists operators to accumulator and a test.
                conditions (extract-exists conditions)

                sorted-conditions (sort-conditions conditions)

                ;; Attach the conditions environment. TODO: narrow environment to those used?
                conditions-with-env (for [condition sorted-conditions]
                                      [condition (:env production)])]]

      [conditions-with-env production])))


(sc/defn to-beta-tree :- [schema/BetaNode]
  "Convert a sequence of rules and/or queries into a beta tree. Returns each root."
  [productions :- [schema/Production]]
  (let [conditions (mapcat get-conds productions)

        raw-roots (reduce
                   (fn [beta-roots [conditions production]]
                    (add-to-beta-tree beta-roots conditions #{} production))
                   []
                   conditions)

        nodes (for [root raw-roots
                    node (tree-seq :children :children root)]
                node)

        ;; Sort nodes so the same id is assigned consistently,
        ;; then map the to corresponding ids.
        nodes-to-id (zipmap
                     (sort gen-compare nodes)
                     (range))

        ;; Anonymous function to walk the nodes and
        ;; assign identifiers to them.
        assign-ids-fn (fn assign-ids [node]
                        (if (:children node)
                          (merge node
                                 {:id (nodes-to-id node)
                                  :children (map assign-ids (:children node))})
                          (assoc node :id (nodes-to-id node))))]

    ;; Assign IDs to the roots and return them.
    (map assign-ids-fn raw-roots)))

(sc/defn to-alpha-tree :- [schema/AlphaNode]
  "Returns a sequence of [condition-fn, [node-ids]] tuples to represent the alpha side of the network."
  [beta-roots :- [schema/BetaNode]]

  ;; Create a sequence of tuples of conditions + env to beta node ids.
  (let [condition-to-node-ids (for [root beta-roots
                                    node (tree-seq :children :children root)
                                    :when (:condition node)]
                                [[(:condition node) (:env node)] (:id node)])

        ;; Merge common conditions together.
        condition-to-node-map (reduce
                               (fn [node-map [[condition env] node-id]]

                                 ;; Can't use simple update-in because we need to ensure
                                 ;; the value is a vector, not a list.
                                 (if (get node-map [condition env])
                                   (update-in node-map [[condition env]] conj node-id)
                                   (assoc node-map [condition env] [node-id])))
                               {}
                               condition-to-node-ids)]

    ;; Compile conditions into functions.
    (vec
     (for [[[condition env] node-ids] condition-to-node-map
           :when (:type condition) ; Exclude test conditions.
           ]

       (cond-> {:condition condition
                :beta-children (distinct node-ids)}
               env (assoc :env env))))))

(sc/defn compile-alpha-nodes :- [{:type sc/Any
                                  :alpha-fn sc/Any ;; TODO: is a function...
                                  (sc/optional-key :env) {sc/Keyword sc/Any}
                                  :children [sc/Num]}]
  [alpha-nodes :- [schema/AlphaNode]]
  (for [{:keys [condition beta-children env]} alpha-nodes
        :let [{:keys [type constraints fact-binding args]} condition
              cmeta (meta condition)]]

    (cond-> {:type (effective-type type)
             :alpha-fn (binding [*file* (or (:file cmeta) *file*)]
                         (eval (with-meta
                                 (compile-condition
                                  type (first args) constraints
                                  fact-binding env)
                                 (meta condition))))
             :children beta-children}
            env (assoc :env env))))

(sc/defn compile-beta-tree
  "Compile the beta tree to the nodes used at runtime."
  [beta-nodes  :- [schema/BetaNode]]
  (let [;; A local, memoized function that ensures that the same expression of
        ;; a given node :id is only compiled into a single function.
        ;; This prevents redundant compilation and avoids having a Rete node
        ;; :id that has had its expressions compiled into different
        ;; compiled functions.
        compile-expr (memoize (fn [id expr] (eval expr)))
        
        compile-beta-tree
        (fn compile-beta-tree [beta-nodes parent-bindings is-root]
          (vec
           (for [beta-node beta-nodes
                 :let [{:keys [condition children id production query join-bindings]} beta-node

                       ;; If the condition is symbol, attempt to resolve the clas it belongs to.
                       condition (if (symbol? condition)
                                   (.loadClass (clojure.lang.RT/makeClassLoader) (name condition))
                                   condition)

                       constraint-bindings (variables-as-keywords (:constraints condition))

                       ;; Get all bindings from the parent, condition, and returned fact.
                       all-bindings (cond-> (s/union parent-bindings constraint-bindings)
                                      ;; Optional fact binding from a condition.
                                      (:fact-binding condition) (conj (:fact-binding condition))
                                      ;; Optional accumulator result.
                                      (:result-binding beta-node) (conj (:result-binding beta-node)))]]

             (case (:node-type beta-node)

               :join
               ;; Use an specialized root node for efficiency in this case.
               (if is-root
                 (eng/->RootJoinNode
                  id
                  condition
                  (compile-beta-tree children all-bindings false)
                  join-bindings)
                 ;; If the join operation includes arbitrary expressions
                 ;; that can't expressed as a hash join, we must use the expressions
                 (if (:join-filter-expressions beta-node)
                   (eng/->ExpressionJoinNode
                    id
                    condition
                    (compile-expr id
                                  (compile-join-filter (:join-filter-expressions beta-node) (:env beta-node)))
                    (compile-beta-tree children all-bindings false)
                    join-bindings)
                   (eng/->HashJoinNode
                    id
                    condition
                    (compile-beta-tree children all-bindings false)
                    join-bindings)))

               :negation
               ;; Check to see if the negation includes an
               ;; expression that must be joined to the incoming token
               ;; and use the appropriate node type.
               (if (:join-filter-expressions beta-node)

                 (eng/->NegationWithJoinFilterNode
                  id
                  condition
                  (compile-expr id
                                (compile-join-filter (:join-filter-expressions beta-node) (:env beta-node)))
                  (compile-beta-tree children all-bindings false)
                  join-bindings)

                 (eng/->NegationNode
                  id
                  condition
                  (compile-beta-tree children all-bindings false)
                  join-bindings))

               :test
               (eng/->TestNode
                id
                (compile-expr id
                              (compile-test (:constraints condition)))
                (compile-beta-tree children all-bindings false))

               :accumulator
               ;; We create an accumulator that accepts the environment for the beta node
               ;; into its context, hence the function with the given environment.
               (let [compiled-node (compile-expr id
                                                 (compile-accum (:accumulator beta-node) (:env beta-node)))
                     compiled-accum (compiled-node (:env beta-node))]

                 ;; Ensure the compiled accumulator has the expected structure
                 (when (not (instance? Accumulator compiled-accum))
                   (throw (IllegalArgumentException. (str (:accumulator beta-node) " is not a valid accumulator."))))

                 ;; If a non-equality unification is in place, compile the predicate and use
                 ;; the specialized accumulate node.

                 (if (:join-filter-expressions beta-node)

                   (eng/->AccumulateWithJoinFilterNode
                    id
                    ;; Create an accumulator structure for use when examining the node or the tokens
                    ;; it produces.
                    {:accumulator (:accumulator beta-node)
                     ;; Include the original filter expressions in the constraints for inspection tooling.
                     :from (update-in condition [:constraints]
                                      into (-> beta-node :join-filter-expressions :constraints))}
                    compiled-accum
                    (compile-expr id
                                  (compile-join-filter (:join-filter-expressions beta-node) (:env beta-node)))
                    (:result-binding beta-node)
                    (compile-beta-tree children all-bindings false)
                    join-bindings)

                   ;; All unification is based on equality, so just use the simple accumulate node.
                   (eng/->AccumulateNode
                    id
                    ;; Create an accumulator structure for use when examining the node or the tokens
                    ;; it produces.
                    {:accumulator (:accumulator beta-node)
                     :from condition}
                    compiled-accum
                    (:result-binding beta-node)
                    (compile-beta-tree children all-bindings false)
                    join-bindings)))

               :production
               (eng/->ProductionNode
                id
                production
                (binding [*file* (:file (meta (:rhs production)))]
                  (compile-expr id
                                (with-meta (compile-action all-bindings
                                                           (:rhs production)
                                                           (:env production))
                                  (meta (:rhs production))))))

               :query
               (eng/->QueryNode
                id
                query
                (:params query))))))]
    ;; Start compilation.
    (compile-beta-tree beta-nodes #{} true)))

(sc/defn build-network
  "Constructs the network from compiled beta tree and condition functions."
  [beta-roots alpha-fns productions]

  (let [beta-nodes (for [root beta-roots
                         node (tree-seq :children :children root)]
                     node)

        production-nodes (for [node beta-nodes
                               :when (= ProductionNode (type node))]
                           node)

        query-nodes (for [node beta-nodes
                          :when (= QueryNode (type node))]
                      node)

        query-map (into {} (for [query-node query-nodes

                                 ;; Queries can be looked up by reference or by name;
                                 entry [[(:query query-node) query-node]
                                        [(:name (:query query-node)) query-node]]]
                             entry))

        ;; Map of node ids to beta nodes.
        id-to-node (into {} (for [node beta-nodes]
                                 [(:id node) node]))

        ;; type, alpha node tuples.
        alpha-nodes (for [{:keys [type alpha-fn children env]} alpha-fns
                          :let [beta-children (map id-to-node children)]]
                      [type (eng/->AlphaNode env beta-children alpha-fn)])

        ;; Merge the alpha nodes into a multi-map
        alpha-map (reduce
                   (fn [alpha-map [type alpha-node]]
                     (update-in alpha-map [type] conj alpha-node))
                   {}
                   alpha-nodes)]

    (strict-map->Rulebase
     {:alpha-roots alpha-map
      :beta-roots beta-roots
      :productions productions
      :production-nodes production-nodes
      :query-nodes query-map
      :id-to-node id-to-node})))

(defn- create-get-alphas-fn
  "Returns a function that given a sequence of facts,
  returns a map associating alpha nodes with the facts they accept."
  [fact-type-fn ancestors-fn merged-rules]

  ;; We preserve a map of fact types to alpha nodes for efficiency,
  ;; effectively memoizing this operation.
  (let [alpha-map (atom {})]
    (fn [facts]
      (for [[fact-type facts] (platform/tuned-group-by fact-type-fn facts)]

        (if-let [alpha-nodes (get @alpha-map fact-type)]

          ;; If the matching alpha nodes are cached, simply return them.
          [alpha-nodes facts]

          ;; The alpha nodes weren't cached for the type, so get them now.
          (let [ancestors (conj (ancestors-fn fact-type) fact-type)

                ;; Get all alpha nodes for all ancestors.
                new-nodes (distinct
                           (reduce
                            (fn [coll ancestor]
                              (concat
                               coll
                               (get-in merged-rules [:alpha-roots ancestor])))
                            []
                            ancestors))]

            (swap! alpha-map assoc fact-type new-nodes)
            [new-nodes facts]))))))


;; Cache of sessions for fast reloading.
(def ^:private session-cache (atom {}))

(defn clear-session-cache!
  "Clears the cache of reusable Clara sessions, so any subsequent sessions
   will be re-compiled from the rule definitions. This is intended for use
   by tooling or specialized needs; most users can simply specify the :cache false
   option when creating sessions."
  []
  (reset! session-cache {}))

(sc/defn mk-session*
  "Compile the rules into a rete network and return the given session."
  [productions :- [schema/Production]
   options :- {sc/Keyword sc/Any}]
  (let [beta-struct (to-beta-tree productions)
        beta-tree (compile-beta-tree beta-struct)
        alpha-nodes (compile-alpha-nodes (to-alpha-tree beta-struct))
        rulebase (build-network beta-tree alpha-nodes productions)
        transport (LocalTransport.)

        ;; The fact-type uses Clojure's type function unless overridden.
        fact-type-fn (get options :fact-type-fn type)

        ;; The ancestors for a logical type uses Clojure's ancestors function unless overridden.
        ancestors-fn (get options :ancestors-fn ancestors)

        ;; Default sort by higher to lower salience.
        activation-group-sort-fn (get options :activation-group-sort-fn >)

        ;; Activation groups use salience, with zero
        ;; as the default value.
        activation-group-fn (get options
                                 :activation-group-fn
                                 (fn [production]
                                   (or (some-> production :props :salience)
                                       0)))

        ;; Create a function that groups a sequence of facts by the collection
        ;; of alpha nodes they target.
        ;; We cache an alpha-map for facts of a given type to avoid computing
        ;; them for every fact entered.
        get-alphas-fn (create-get-alphas-fn fact-type-fn ancestors-fn rulebase)]

    (eng/assemble {:rulebase rulebase
                   :memory (eng/local-memory rulebase transport activation-group-sort-fn activation-group-fn get-alphas-fn)
                   :transport transport
                   :listeners (get options :listeners  [])
                   :get-alphas-fn get-alphas-fn})))

(defn mk-session
  "Creates a new session using the given rule source. Thew resulting session
   is immutable, and can be used with insert, retract, fire-rules, and query functions."
  ([sources-and-options]

     ;; If an equivalent session has been created, simply reuse it.
     ;; This essentially memoizes this function unless the caller disables caching.
     (if-let [session (get @session-cache [sources-and-options])]
       session

       ;; Separate sources and options, then load them.
       (let [sources (take-while (complement keyword?) sources-and-options)
             options (apply hash-map (drop-while (complement keyword?) sources-and-options))
             productions (mapcat
                          #(if (satisfies? IRuleSource %)
                             (load-rules %)
                             %)
                          sources) ; Load rules from the source, or just use the input as a seq.
             session (mk-session* productions options)]

         ;; Cache the session unless instructed not to.
         (when (get options :cache true)
           (swap! session-cache assoc [sources-and-options] session))

         ;; Return the session.
         session))))
