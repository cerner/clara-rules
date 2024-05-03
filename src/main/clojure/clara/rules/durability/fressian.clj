(ns clara.rules.durability.fressian
  "A default Fressian-based implementation of d/ISessionSerializer.

   Note!  Currently this only supports the clara.rules.memory.PersistentLocalMemory implementation
          of memory."
  (:require [clara.rules.durability :as d]
            [clara.rules.memory :as mem]
            [clara.rules.engine :as eng]
            [clara.rules.compiler :as com]
            [clara.rules.platform :as pform]
            [schema.core :as s]
            [clojure.data.fressian :as fres]
            [clojure.java.io :as jio]
            [clojure.main :as cm])
  (:import [clara.rules.durability
            MemIdx
            InternalMemIdx]
           [clara.rules.memory
            RuleOrderedActivation]
           [clara.rules.engine
            Token
            Element
            ProductionNode
            QueryNode
            AlphaNode
            RootJoinNode
            HashJoinNode
            ExpressionJoinNode
            NegationNode
            NegationWithJoinFilterNode
            TestNode
            AccumulateNode
            AccumulateWithJoinFilterNode]
           [org.fressian
            StreamingWriter
            Writer
            Reader
            FressianWriter
            FressianReader]
           [org.fressian.handlers
            WriteHandler
            ReadHandler]
           [java.util
            ArrayList
            IdentityHashMap
            Map
            WeakHashMap]
           [java.io
            InputStream
            OutputStream]))

;; Use this map to cache the symbol for the map->RecordNameHere
;; factory function created for every Clojure record to improve
;; serialization performance.
;; See https://github.com/cerner/clara-rules/issues/245 for more extensive discussion.
(def ^:private ^Map class->factory-fn-sym (java.util.Collections/synchronizedMap
                                           (WeakHashMap.)))

(defn record-map-constructor-name
  "Return the 'map->' prefix, factory constructor function for a Clojure record."
  [rec]
  (let [klass (class rec)]
    (if-let [cached-sym (.get class->factory-fn-sym klass)]
      cached-sym
      (let [class-name (.getName ^Class klass)
            idx (.lastIndexOf class-name (int \.))
            ns-nom (.substring class-name 0 idx)
            nom (.substring class-name (inc idx))
            factory-fn-sym (symbol (str (cm/demunge ns-nom)
                                        "/map->"
                                        (cm/demunge nom)))]
        (.put class->factory-fn-sym klass factory-fn-sym)
        factory-fn-sym))))

(defn write-map
  "Writes a map as Fressian with the tag 'map' and all keys cached."
  [^Writer w m]
  (.writeTag w "map" 1)
  (.beginClosedList ^StreamingWriter w)
  (reduce-kv
   (fn [^Writer w k v]
     (.writeObject w k true)
     (.writeObject w v))
   w
   m)
  (.endList ^StreamingWriter w))

(defn write-with-meta
  "Writes the object to the writer under the given tag.  If the record has metadata, the metadata
   will also be written.  read-with-meta will associated this metadata back with the object
   when reading."
  ([w tag o]
   (write-with-meta w tag o (fn [^Writer w o] (.writeList w o))))
  ([^Writer w tag o write-fn]
   (let [m (meta o)]
     (do
       (.writeTag w tag 2)
       (write-fn w o)
       (if m
         (.writeObject w m)
         (.writeNull w))))))

(defn- read-meta [^Reader rdr]
  (some->> rdr
           .readObject
           (into {})))

(defn read-with-meta
  "Reads an object from the reader that was written via write-with-meta.  If the object was written
   with metadata the metadata will be associated on the object returned."
  [^Reader rdr build-fn]
  (let [o (build-fn (.readObject rdr))
        m (read-meta rdr)]
    (cond-> o
      m (with-meta m))))

(defn write-record
  "Same as write-with-meta, but with Clojure record support.  The type of the record will
   be preserved."
  [^Writer w tag rec]
  (let [m (meta rec)]
    (.writeTag w tag 3)
    (.writeObject w (record-map-constructor-name rec) true)
    (write-map w rec)
    (if m
      (.writeObject w m)
      (.writeNull w))))

(defn read-record
  "Same as read-with-meta, but with Clojure record support.  The type of the record will
   be preserved."
  ([^Reader rdr]
   (read-record rdr nil))
  ([^Reader rdr add-fn]
   (let [try-resolve #(if-let [resolved (resolve %)]
                        resolved
                        (throw (ex-info (str "Unable to resolve fact type symbol: '" % "'")
                                        {:unresolvable-symbol %})))
         builder (-> (.readObject rdr) try-resolve deref)
         build-map (.readObject rdr)
         m (read-meta rdr)]
     (cond-> (builder build-map)
       m (with-meta m)
       add-fn add-fn))))

(defn- create-cached-node-handler
  ([clazz
    tag
    tag-for-cached]
   {:class clazz
    :writer (reify WriteHandler
              (write [_ w o]
                (let [node-id (:id o)]
                  (if (@(.get d/node-id->node-cache) node-id)
                    (do
                      (.writeTag w tag-for-cached 1)
                      (.writeInt w node-id))
                    (do
                      (d/cache-node o)
                      (write-record w tag o))))))
    :readers {tag-for-cached
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (d/node-id->node (.readObject rdr))))
              tag
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (-> rdr
                      read-record
                      d/cache-node)))}})
  ([clazz
    tag
    tag-for-cached
    remove-node-expr-fn
    add-node-expr-fn]
   {:class clazz
    :writer (reify WriteHandler
              (write [_ w o]
                (let [node-id (:id o)]
                  (if (@(.get d/node-id->node-cache) node-id)
                    (do
                      (.writeTag w tag-for-cached 1)
                      (.writeInt w node-id))
                    (do
                      (d/cache-node o)
                      (write-record w tag (remove-node-expr-fn o)))))))
    :readers {tag-for-cached
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (d/node-id->node (.readObject rdr))))
              tag
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (-> rdr
                      (read-record add-node-expr-fn)
                      d/cache-node)))}}))

(defn- create-identity-based-handler
  [clazz
   tag
   write-fn
   read-fn]
  (let [indexed-tag (str tag "-idx")]
    ;; Write an object a single time per object reference to that object.  The object is then "cached"
    ;; with the IdentityHashMap `d/clj-struct-holder`.  If another reference to this object instance
    ;; is encountered later, only the "index" of the object in the map will be written.
    {:class clazz
     :writer (reify WriteHandler
               (write [_ w o]
                 (if-let [idx (d/clj-struct->idx o)]
                   (do
                     (.writeTag w indexed-tag 1)
                     (.writeInt w idx))
                   (do
                     ;; We are writing all nested objects prior to adding the original object to the cache here as
                     ;; this will be the order that will occur on read, ie, the reader will have traverse to the bottom
                     ;; of the struct before rebuilding the object.
                     (write-fn w tag o)
                     (d/clj-struct-holder-add-fact-idx! o)))))
     ;; When reading the first time a reference to an object instance is found, the entire object will
     ;; need to be constructed.  It is then put into indexed cache.  If more references to this object
     ;; instance are encountered later, they will be in the form of a numeric index into this cache.
     ;; This is guaranteed by the semantics of the corresponding WriteHandler.
     :readers {indexed-tag
               (reify ReadHandler
                 (read [_ rdr _ _]
                   (d/clj-struct-idx->obj (.readInt rdr))))
               tag
               (reify ReadHandler
                 (read [_ rdr _ _]
                   (-> rdr
                       read-fn
                       d/clj-struct-holder-add-obj!)))}}))

(def handlers
  "A structure tying together the custom Fressian write and read handlers used
   by FressianSessionSerializer's."
  {"java/class"
   {:class Class
    :writer (reify WriteHandler
              (write [_ w c]
                (.writeTag w "java/class" 1)
                (.writeObject w (symbol (.getName ^Class c)) true)))
    :readers {"java/class"
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (resolve (.readObject rdr))))}}

   "clj/set"
   (create-identity-based-handler
     clojure.lang.APersistentSet
     "clj/set"
     write-with-meta
     (fn clj-set-reader [rdr] (read-with-meta rdr set)))

   "clj/vector"
   (create-identity-based-handler
     clojure.lang.APersistentVector
     "clj/vector"
     write-with-meta
     (fn clj-vec-reader [rdr] (read-with-meta rdr vec)))

   "clj/list"
   (create-identity-based-handler
     clojure.lang.PersistentList
     "clj/list"
     write-with-meta
     (fn clj-list-reader [rdr] (read-with-meta rdr #(apply list %))))

   "clj/emptylist"
   ;; Not using the identity based handler as this will always be identical anyway
   ;; then meta data will be added in the reader
   {:class clojure.lang.PersistentList$EmptyList
    :writer (reify WriteHandler
              (write [_ w o]
                (let [m (meta o)]
                  (do
                    (.writeTag w "clj/emptylist" 1)
                    (if m
                      (.writeObject w m)
                      (.writeNull w))))))
    :readers {"clj/emptylist"
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (let [m (read-meta rdr)]
                    (cond-> '()
                            m (with-meta m)))))}}

   "clj/aseq"
   (create-identity-based-handler
     clojure.lang.ASeq
     "clj/aseq"
     write-with-meta
     (fn clj-seq-reader [rdr] (read-with-meta rdr sequence)))

   "clj/lazyseq"
   (create-identity-based-handler
     clojure.lang.LazySeq
     "clj/lazyseq"
     write-with-meta
     (fn clj-lazy-seq-reader [rdr] (read-with-meta rdr sequence)))

   "clj/map"
   (create-identity-based-handler
     clojure.lang.APersistentMap
     "clj/map"
     (fn clj-map-writer [wtr tag m] (write-with-meta wtr tag m write-map))
     (fn clj-map-reader [rdr] (read-with-meta rdr #(into {} %))))

   "clj/treeset"
   (create-identity-based-handler
     clojure.lang.PersistentTreeSet
     "clj/treeset"
     (fn clj-treeset-writer [^Writer wtr tag s]
       (let [cname (d/sorted-comparator-name s)]
         (.writeTag wtr tag 3)
         (if cname
           (.writeObject wtr cname true)
           (.writeNull wtr))
         ;; Preserve metadata.
         (if-let [m (meta s)]
           (.writeObject wtr m)
           (.writeNull wtr))
         (.writeList wtr s)))
     (fn clj-treeset-reader [^Reader rdr]
       (let [c (some-> rdr .readObject resolve deref)
             m (.readObject rdr)
             s (-> (.readObject rdr)
                   (d/seq->sorted-set c))]
         (if m
           (with-meta s m)
           s))))

   "clj/treemap"
   (create-identity-based-handler
     clojure.lang.PersistentTreeMap
     "clj/treemap"
     (fn clj-treemap-writer [^Writer wtr tag o]
       (let [cname (d/sorted-comparator-name o)]
         (.writeTag wtr tag 3)
         (if cname
           (.writeObject wtr cname true)
           (.writeNull wtr))
         ;; Preserve metadata.
         (if-let [m (meta o)]
           (.writeObject wtr m)
           (.writeNull wtr))
         (write-map wtr o)))
     (fn clj-treemap-reader [^Reader rdr]
       (let [c (some-> rdr .readObject resolve deref)
             m (.readObject rdr)
             s (d/seq->sorted-map (.readObject rdr) c)]
         (if m
           (with-meta s m)
           s))))

   "clj/mapentry"
   (create-identity-based-handler
     clojure.lang.MapEntry
     "clj/mapentry"
     (fn clj-mapentry-writer [^Writer wtr tag o]
       (.writeTag wtr tag 2)
       (.writeObject wtr (key o) true)
       (.writeObject wtr (val o)))
     (fn clj-mapentry-reader [^Reader rdr]
       (d/create-map-entry (.readObject rdr)
                           (.readObject rdr))))

   ;; Have to redefine both Symbol and IRecord to support metadata as well
   ;; as identity-based caching for the IRecord case.

   "clj/sym"
   (create-identity-based-handler
     clojure.lang.Symbol
     "clj/sym"
     (fn clj-sym-writer [^Writer wtr tag o]
       ;; Mostly copied from private fres/write-named, except the metadata part.
       (.writeTag wtr tag 3)
       (.writeObject wtr (namespace o) true)
       (.writeObject wtr (name o) true)
       (if-let [m (meta o)]
         (.writeObject wtr m)
         (.writeNull wtr)))
     (fn clj-sym-reader [^Reader rdr]
       (let [s (symbol (.readObject rdr) (.readObject rdr))
             m (read-meta rdr)]
         (cond-> s
                 m (with-meta m)))))

   "clj/record"
   (create-identity-based-handler
     clojure.lang.IRecord
     "clj/record"
     write-record
     read-record)

   "clara/productionnode"
   (create-cached-node-handler ProductionNode
                               "clara/productionnode"
                               "clara/productionnodeid"
                               #(assoc % :rhs nil)
                               d/add-rhs-fn)

   "clara/querynode"
   (create-cached-node-handler QueryNode
                               "clara/querynode"
                               "clara/querynodeid")

   "clara/alphanode"
   (create-cached-node-handler AlphaNode
                               "clara/alphanodeid"
                               "clara/alphanode"
                               #(assoc % :activation nil)
                               d/add-alpha-fn)

   "clara/rootjoinnode"
   (create-cached-node-handler RootJoinNode
                               "clara/rootjoinnode"
                               "clara/rootjoinnodeid")

   "clara/hashjoinnode"
   (create-cached-node-handler HashJoinNode
                               "clara/hashjoinnode"
                               "clara/hashjoinnodeid")

   "clara/exprjoinnode"
   (create-cached-node-handler ExpressionJoinNode
                               "clara/exprjoinnode"
                               "clara/exprjoinnodeid"
                               #(assoc % :join-filter-fn nil)
                               d/add-join-filter-fn)

   "clara/negationnode"
   (create-cached-node-handler NegationNode
                               "clara/negationnode"
                               "clara/negationnodeid")

   "clara/negationwjoinnode"
   (create-cached-node-handler NegationWithJoinFilterNode
                               "clara/negationwjoinnode"
                               "clara/negationwjoinnodeid"
                               #(assoc % :join-filter-fn nil)
                               d/add-join-filter-fn)

   "clara/testnode"
   (create-cached-node-handler TestNode
                               "clara/testnode"
                               "clara/testnodeid"
                               #(assoc % :test nil)
                               d/add-test-fn)

   "clara/accumnode"
   (create-cached-node-handler AccumulateNode
                               "clara/accumnode"
                               "clara/accumnodeid"
                               #(assoc % :accumulator nil)
                               d/add-accumulator)

   "clara/accumwjoinnode"
   (create-cached-node-handler AccumulateWithJoinFilterNode
                               "clara/accumwjoinnode"
                               "clara/accumwjoinnodeid"
                               #(assoc % :accumulator nil :join-filter-fn nil)
                               (comp d/add-accumulator d/add-join-filter-fn))

   "clara/ruleorderactivation"
   {:class RuleOrderedActivation
    :writer (reify WriteHandler
              (write [_ w c]
                (.writeTag w "clara/ruleorderactivation" 4)
                (.writeObject w (.-node-id ^RuleOrderedActivation c) true)
                (.writeObject w (.-token ^RuleOrderedActivation c))
                (.writeObject w (.-activation ^RuleOrderedActivation c))
                (.writeInt w (.-rule-load-order ^RuleOrderedActivation c))))
    :readers {"clara/ruleorderactivation"
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (mem/->RuleOrderedActivation (.readObject rdr)
                                               (.readObject rdr)
                                               (.readObject rdr)
                                               (.readObject rdr)
                                               false)))}}

   "clara/memidx"
   {:class MemIdx
    :writer (reify WriteHandler
              (write [_ w c]
                (.writeTag w "clara/memidx" 1)
                (.writeInt w (:idx c))))
    :readers {"clara/memidx"
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (d/find-mem-idx (.readObject rdr))))}}

   "clara/internalmemidx"
   {:class InternalMemIdx
    :writer (reify WriteHandler
              (write [_ w c]
                (.writeTag w "clara/internalmemidx" 1)
                (.writeInt w (:idx c))))
    :readers {"clara/internalmemidx"
              (reify ReadHandler
                (read [_ rdr tag component-count]
                  (d/find-internal-idx (.readObject rdr))))}}})

(def write-handlers
  "All Fressian write handlers used by FressianSessionSerializer's."
  (into fres/clojure-write-handlers
        (map (fn [[tag {clazz :class wtr :writer}]]
               [clazz {tag wtr}]))
        handlers))

(def read-handlers
  "All Fressian read handlers used by FressianSessionSerializer's."
    (->> handlers
       vals
       (into fres/clojure-read-handlers
             (mapcat :readers))))

(def write-handler-lookup
  (-> write-handlers
      fres/associative-lookup
      fres/inheritance-lookup))

(def read-handler-lookup
  (fres/associative-lookup read-handlers))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Session serializer.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord FressianSessionSerializer [in-stream out-stream]
  d/ISessionSerializer
  (serialize [_ session opts]
    (let [{:keys [rulebase memory]} (eng/components session)
          node-expr-fn-lookup (:node-expr-fn-lookup rulebase)
          remove-node-fns (fn [expr-lookup]
                            (zipmap (keys expr-lookup)
                                    (mapv second (vals expr-lookup))))
          rulebase (assoc rulebase
                          :activation-group-sort-fn nil
                          :activation-group-fn nil
                          :get-alphas-fn nil
                          :node-expr-fn-lookup nil)
          record-holder (IdentityHashMap.)
          do-serialize
          (fn [sources]
            (with-open [^FressianWriter wtr
                        (fres/create-writer out-stream :handlers write-handler-lookup)]
              (pform/thread-local-binding [d/node-id->node-cache (volatile! {})
                                           d/clj-struct-holder record-holder]
                                          (doseq [s sources] (fres/write-object wtr s)))))]
      
      ;; In this case there is nothing to do with memory, so just serialize immediately.
      (if (:rulebase-only? opts)
        ;; node-expr-fn-lookup is a map with a structure of:
        ;; {[Int Keyword] [IFn {Keyword Any}]}
        ;; as fns are not serializable, we must remove them and alter the structure of the map to be
        ;; {[Int Keyword] {Keyword Any}}
        ;; during deserialization the compilation-context({Keyword Any}), which contains the unevaluated form,
        ;; can be used to reconstruct the original map.
        (do-serialize [(remove-node-fns node-expr-fn-lookup) rulebase])
        
        ;; Otherwise memory needs to have facts extracted to return.
        (let [{:keys [memory indexed-facts internal-indexed-facts]} (d/indexed-session-memory-state memory)
              sources (if (:with-rulebase? opts)
                        [(remove-node-fns node-expr-fn-lookup) rulebase internal-indexed-facts memory]
                        [internal-indexed-facts memory])]
          
          (do-serialize sources)
          
          ;; Return the facts needing to be serialized still.
          indexed-facts))))
  
  (deserialize [_ mem-facts opts]

    (with-open [^FressianReader rdr (fres/create-reader in-stream :handlers read-handler-lookup)]
      (let [{:keys [rulebase-only? base-rulebase forms-per-eval]} opts
            
            record-holder (ArrayList.)
            ;; The rulebase should either be given from the base-session or found in
            ;; the restored session-state.
            maybe-base-rulebase (when (and (not rulebase-only?) base-rulebase)
                                  base-rulebase)

            forms-per-eval (or forms-per-eval com/forms-per-eval-default)

            reconstruct-expressions (fn [expr-lookup]
                                      ;; Rebuilding the expr-lookup map from the serialized map:
                                      ;; {[Int Keyword] {Keyword Any}} -> {[Int Keyword] [SExpr {Keyword Any}]}
                                      (into {}
                                            (for [[node-key compilation-ctx] expr-lookup]
                                              [node-key [(-> compilation-ctx (get (nth node-key 1)))
                                                         compilation-ctx]])))

            rulebase (if maybe-base-rulebase
                       maybe-base-rulebase
                       (let [without-opts-rulebase
                             (pform/thread-local-binding [d/node-id->node-cache (volatile! {})
                                                          d/clj-struct-holder record-holder]
                                                         (pform/thread-local-binding [d/node-fn-cache (-> (fres/read-object rdr)
                                                                                                          reconstruct-expressions
                                                                                                          (com/compile-exprs forms-per-eval))]
                                                                                     (assoc (fres/read-object rdr)
                                                                                       :node-expr-fn-lookup
                                                                                       (.get d/node-fn-cache))))]
                         (d/rulebase->rulebase-with-opts without-opts-rulebase opts)))]
        
        (if rulebase-only?
          rulebase
          (d/assemble-restored-session rulebase
                                       (pform/thread-local-binding [d/clj-struct-holder record-holder
                                                                    d/mem-facts mem-facts]
                                                                   ;; internal memory contains facts provided by mem-facts
                                                                   ;; thus mem-facts must be bound before the call to read
                                                                   ;; the internal memory
                                                                   (pform/thread-local-binding [d/mem-internal (fres/read-object rdr)]
                                                                                               (fres/read-object rdr)))
                                       opts))))))

(s/defn create-session-serializer
  "Creates an instance of FressianSessionSerializer which implements d/ISessionSerializer by using
   Fressian serialization for the session structures.
   
   In the one arity case, takes either an input stream or an output stream.  This arity is intended for
   creating a Fressian serializer instance that will only be used for serialization or deserialization,
   but not both.  e.g. This is often convenient if serialization and deserialization are not done from
   the same process.  If it is to be used for serialization, then the stream given should be an output
   stream.  If it is to be used for deserialization, then the stream to be given should be an
   input stream.

   In the two arity case, takes an input stream and an output stream.  These will be used for
   deserialization and serialization within the created Fressian serializer instance, respectively.

   Note!  Currently this only supports the clara.rules.memory.PersistentLocalMemory implementation
          of memory."
  ([in-or-out-stream :- (s/pred (some-fn #(instance? InputStream %)
                                         #(instance? OutputStream %))
                                "java.io.InputStream or java.io.OutputStream")]
   (if (instance? InputStream in-or-out-stream)
     (create-session-serializer in-or-out-stream nil)
     (create-session-serializer nil in-or-out-stream)))

  ([in-stream :- (s/maybe InputStream)
    out-stream :- (s/maybe OutputStream)]
   (->FressianSessionSerializer in-stream out-stream)))
