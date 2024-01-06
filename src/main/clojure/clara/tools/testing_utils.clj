(ns clara.tools.testing-utils
  "Internal utilities for testing clara-rules and derivative projects.  These should be considered experimental
  right now from the perspective of consumers of clara-rules, although it is possible that this namespace 
  will be made part of the public API once its functionality has proven robust and reliable.  The focus, however,
  is functionality needed to test the rules engine itself."
  (:require [clara.rules.update-cache.core :as uc]
            [clara.rules.update-cache.cancelling :as ca]
            [clara.rules.compiler :as com]
            [clara.rules.dsl :as dsl]
            [clojure.test :refer [is]]
            [clara.rules.platform :as platform]))

(defmacro def-rules-test
  "This macro allows creation of rules, queries, and sessions from arbitrary combinations of rules
  and queries in a setup map without the necessity of creating a namespace or defining a session
  using defsession in both Clojure and ClojureScript.  The first argument is the name of the test, 
  and the second argument is a map with entries :rules, :queries, and :sessions.  For example usage see
  clara.test-testing-utils.  Note that sessions currently can only contain rules and queries defined
  in the setup map; supporting other rule sources such as namespaces and defrule/defquery may be possible
  in the future.

  Namespaces consuming this macro are expected to require clara.rules and either clojure.test or cljs.test.
  Unfortunately, at this time we can't add inline requires for these namespace with the macroexpanded code in
  ClojureScript; see https://anmonteiro.com/2016/10/clojurescript-require-outside-ns/ for some discussion on the 
  subject.  However, the test namespaces consuming this will in all likelihood have these dependencies anyway
  so this probably isn't a significant shortcoming of this macro."
  [name params & forms]
  (let [sym->rule (->> params
                       :rules
                       (partition 2)
                       (into {}
                             (map (fn [[rule-name [lhs rhs props]]]
                                    [rule-name (assoc (dsl/parse-rule* lhs rhs props {}) :name (str rule-name))]))))

        sym->query (->> params
                        :queries
                        (partition 2)
                        (into {}
                              (map (fn [[query-name [params lhs]]]
                                     [query-name (assoc (dsl/parse-query* params lhs {}) :name (str query-name))]))))

        production-syms->productions (fn [p-syms]
                                       (map (fn [s]
                                              (or (get sym->rule s)
                                                  (get sym->query s)))
                                            p-syms))

        session-syms->session-forms (->> params
                                         :sessions
                                         (partition 3)
                                         (into []
                                               (comp (map (fn [[session-name production-syms session-opts]]
                                                            [session-name (production-syms->productions production-syms) session-opts]))
                                                     (map (fn [[session-name productions session-opts]]
                                                            [session-name `(com/mk-session ~(into [(vec productions)]
                                                                                                  cat
                                                                                                  session-opts))]))
                                                     cat)))

        test-form `(clojure.test/deftest
                     ~name
                     (let [~@session-syms->session-forms
                           ~@(sequence cat sym->query)
                           ~@(sequence cat sym->rule)]
                       ~@forms))]
    test-form))

(defn opts-fixture
  ;; For operations other than replace-facts uc/get-ordered-update-cache is currently
  ;; always used.  This fixture ensures that CancellingUpdateCache and Parallel Matching is tested for a wide
  ;; variety of different cases rather than a few cases cases specific to it.
  [f]
  (f)
  (with-redefs [uc/get-ordered-update-cache ca/get-cancelling-update-cache]
    (f)))

(defn join-filter-equals
  "Intended to be a test function that is the same as equals, but is not visible to Clara as such
  and thus forces usage of join filters instead of hash joins"
  [& args]
  (apply = args))

(def side-effect-holder (atom nil))

(defn side-effect-holder-fixture
  "Fixture to reset the side effect holder to nil both before and after tests.
  This should be used as a :each fixture."
  [t]
  (reset! side-effect-holder nil)
  (t)
  (reset! side-effect-holder nil))

(defn time-execution
  [func]
  (let [start (System/currentTimeMillis)
        _ (func)
        stop (System/currentTimeMillis)]
    (- stop start)))

(defn execute-tests
  [func iterations]
  (let [execution-times (for [_ (range iterations)]
                          (time-execution func))
        sum #(reduce + %)
        mean (/ (sum execution-times) iterations)
        std (->
             (into []
                   (comp
                    (map #(- % mean))
                    (map #(Math/pow (double %) 2.0)))
                   execution-times)
             sum
             (/ iterations)
             Math/sqrt)]
    {:std (double std)
     :mean (double mean)}))

(defn run-performance-test
  "Created as a rudimentary alternative to criterium, due to assumptions made during benchmarking. Specifically, that
  criterium attempts to reach a steady state of compiled and loaded classes. This fundamentally doesn't work when the
  metrics needed rely on compilation or evaluation."
  [form]
  (let [{:keys [description func iterations mean-assertion verbose]} form
        {:keys [std mean]} (execute-tests func iterations)]
    (when verbose
      (println (str \newline "Running Performance tests for:"))
      (println description)
      (println "==========================================")
      (println (str "Mean: " mean "ms"))
      (println (str "Standard Deviation: " std "ms" \newline)))
    (is (mean-assertion mean)
        (str "Actual mean value: " mean))
    {:mean mean
     :std std}))

(defn ex-data-search
  ([^Exception e edata]
   (ex-data-search e nil edata))
  ([^Exception e emsg edata]
   (loop [non-matches []
          e e]
     (cond
       ;; Found match.
       (and (= edata
               (select-keys (ex-data e)
                            (keys edata)))
            (or (= emsg
                   (.getMessage e))
                (nil? emsg)))
       :success

       ;; Keep searching, record any non-matching ex-data.
       (.getCause e)
       (recur (if-let [ed (ex-data e)]
                (conj non-matches {(.getMessage e) ed})
                non-matches)
              (.getCause e))

       ;; Can't find a match.
       :else
       non-matches))))

(defn get-all-ex-data
  "Walk a Throwable chain and return a sequence of all data maps
  from any ExceptionInfo instances in that chain."
  [e]
  (let [get-ex-chain (fn get-ex-chain [e]
                       (if-let [cause (.getCause e)]
                         (conj (get-ex-chain cause) e)
                         [e]))]

    (map ex-data
         (filter (partial instance? clojure.lang.IExceptionInfo)
                 (get-ex-chain e)))))

(defmacro assert-ex-data
  ([expected-ex-data form]
   `(assert-ex-data nil ~expected-ex-data ~form))
  ([expected-ex-message expected-ex-data form]
   `(try
      ~form
      (is false
          (str "Exception expected to be thrown when evaluating: " \newline
               '~form))
      (catch Exception e#
        (let [res# (ex-data-search e# ~expected-ex-message ~expected-ex-data)]
          (is (= :success res#)
              (str "Exception msg found: " \newline
                   e# \newline
                   "Non matches found: " \newline
                   res#)))))))

(defn ex-data-maps
  "Given a throwable/exception/error `t`, return all `ex-data` maps from the stack trace cause chain in 
  the order they occur traversing the chain from this `t` through the rest of the call stack."
  [t]
  (let [append-self (fn append-self
                      [prior t1]
                      (if t1
                        (append-self (conj prior t1) (.getCause ^Throwable t1))
                        prior))
        throwables  (append-self [] t)]
    (into []
          (comp (map ex-data))
          throwables)))
