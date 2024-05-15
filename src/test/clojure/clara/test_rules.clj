(ns clara.test-rules
  (:require [clara.sample-ruleset :as sample]
            [clara.other-ruleset :as other]
            [clara.rules.test-rules-data :as rules-data]
            [clara.rules :refer :all]
            [clojure.test :refer :all]
            [clara.rules.testfacts :refer :all]
            [clara.rules.engine :as eng]
            [clara.rules.compiler :as com]
            [clara.rules.accumulators :as acc]
            [clara.rules.dsl :as dsl]
            [clara.tools.tracing :as t]
            [clojure.set :as s]
            [clojure.edn :as edn]
            [clojure.walk :as walk]
            [clara.sample-ruleset-seq :as srs]
            [clara.order-ruleset :as order-rules]
            [schema.test]
            [schema.core :as sc]
            [clara.tools.testing-utils :as tu :refer [assert-ex-data]])
  (:import [clara.rules.testfacts Temperature WindSpeed Cold Hot TemperatureHistory
            ColdAndWindy LousyWeather First Second Third Fourth FlexibleFields]
           [clara.rules.engine
            ISession
            ISystemFact]
           [java.util TimeZone]
           [clara.tools.tracing
            PersistentTracingListener]
           [java.util
            List
            LinkedList
            ArrayList]))

(use-fixtures :once schema.test/validate-schemas tu/opts-fixture)

;; Shared dynamic var to hold stateful constructs used by rules.  Rules cannot
;; use the environmental in their test body in their RHS, so we need a var that
;; is resolvable in this test namespace.
(def ^:dynamic *side-effect-holder* nil)

(defn- has-fact? [token fact]
  (some #{fact} (map first (:matches token))))

#_{:clj-kondo/ignore [:unresolved-symbol]}
(deftest test-malformed-binding
  ;; Test binding with no value.
  (try
    (mk-session [(dsl/parse-rule [[Temperature (= ?t)]]
                                 (println "Placeholder."))])
    (catch Exception e
      (is (= [:?t] (:variables (ex-data e)))))))

(defn identity-retract
  "Retract function that does nothing for testing purposes."
  [state retracted]
  state)

(defn average-value
  "Test accumulator that returns the average of a field"
  [field]
  (accumulate
   :initial-value [0 0]
   :reduce-fn (fn [[value count] item]
                [(+ value (field item)) (inc count)])
   :combine-fn (fn [[value1 count1] [value2 count2]]
                 [(+ value1 value2) (+ count1 count2)])
   :retract-fn identity-retract
   :convert-return-fn (fn [[value count]] (if (= 0 count)
                                            nil
                                            (/ value count)))))

(deftest test-negation-with-complex-retractions
  (let [;; Non-blocked rule, where "blocked" means there is a
        ;; negated condition "guard".
        first-to-second (dsl/parse-rule [[First]]

                                        (insert! (->Second)))

        ;; Single blocked rule.
        blocked-first-to-fourth-third (dsl/parse-rule [[:not [Second]]
                                                       [First]]

                                                      (insert! (->Fourth)
                                                               (->Third)))

        ;; Double blocked rule.
        double-blocked-fourth (dsl/parse-query [] [[:not [Second]]
                                                   [:not [Third]]
                                                   [?fourth <- Fourth]])

        ;; Just to ensure the query can be matched sometimes.
        session-with-results (-> (mk-session [first-to-second
                                              blocked-first-to-fourth-third
                                              double-blocked-fourth]
                                             :cache false)
                                 (insert (->Fourth))
                                 fire-rules)

        ;; Let the rules engine perform rule activations in any order.
        session-no-salience (-> (mk-session [first-to-second
                                             blocked-first-to-fourth-third
                                             double-blocked-fourth]
                                            :cache false)
                                (insert (->First))
                                (insert (->Fourth))
                                fire-rules)

        ;; The simplest path is to evaluate the rule activations starting with
        ;; non-blocked -> blocked -> double blocked.
        session-best-order-salience (-> (mk-session [(assoc first-to-second :props {:salience 2})
                                                     (assoc blocked-first-to-fourth-third :props {:salience 1})
                                                     double-blocked-fourth]
                                                    :cache false)
                                        (insert (->First))
                                        (insert (->Fourth))
                                        fire-rules)

        ;; The most taxing path on the TMS is to evaluate the rule activations starting with
        ;; double blocked -> blocked -> non-blocked.
        session-worst-order-salience (-> (mk-session [(assoc first-to-second :props {:salience -2})
                                                      (assoc blocked-first-to-fourth-third :props {:salience -1})
                                                      double-blocked-fourth]
                                                     :cache false)
                                         (insert (->First))
                                         (insert (->Fourth))
                                         fire-rules)]

    (is (= #{{:?fourth (->Fourth)}}
           (set (query session-with-results double-blocked-fourth))))

    ;; All of these should return the same thing - :salience shouldn't
    ;; affect outcomes for logical inserts.

    (is (empty? (query session-no-salience double-blocked-fourth)))
    (is (empty? (query session-best-order-salience double-blocked-fourth)))
    (is (empty? (query session-worst-order-salience double-blocked-fourth)))))

(deftest test-accum-result-in-negation
  (let [all-temps-are-max (dsl/parse-query
                           []
                           [[?t <- (acc/max :temperature) :from [Temperature]]
                            [:not [Temperature (< temperature ?t)]]
                            ])

        session (mk-session [all-temps-are-max])]

    (is (empty?
         (-> session
             (insert (->Temperature 50 "MCI"))
             (insert (->Temperature 40 "MCI"))
             fire-rules
             (query all-temps-are-max))))

    (is (= [{:?t 50}]
           (-> session
               (insert (->Temperature 50 "MCI"))
               (insert (->Temperature 50 "MCI"))
               fire-rules
               (query all-temps-are-max))))))

(deftest test-external-activation-of-negation-condition-triggering-retraction
  (let [not-hot (dsl/parse-rule [[:not [Hot]]]
                                (insert! (->LousyWeather)))

        transitive-consequence (dsl/parse-rule [[LousyWeather]]
                                               (insert! (->First)))

        lousy-weather-query (dsl/parse-query [] [[LousyWeather]])

        first-query (dsl/parse-query [] [[First]])

        empty-session-fired (fire-rules
                             (mk-session [not-hot lousy-weather-query
                                          transitive-consequence first-query]
                                         :cache false))

        session-with-hot (-> empty-session-fired
                             (insert (->Hot 100))
                             fire-rules)]

    (is (= (query empty-session-fired lousy-weather-query)
           (query empty-session-fired first-query)
           [{}])
        "Sanity test that the rules fire without the negation condition.")

    (is (and (empty? (query session-with-hot lousy-weather-query))
             (empty? (query session-with-hot first-query)))
        (str "Validate that when the negation condition is directly activated "
             "from an external operation that logical insertions from the rule are retracted, "
             "both direct insertions from the rule and ones from downstream rules."))))

(deftest test-retraction-of-join
  (let [same-wind-and-temp (dsl/parse-query [] [[Temperature (= ?t temperature)]
                                                (WindSpeed (= ?t windspeed))])

        session (-> (mk-session [same-wind-and-temp])
                    (insert (->Temperature 10 "MCI"))
                    (insert (->WindSpeed 10 "MCI"))
                    fire-rules)

        retracted-session (-> session
                              (retract (->Temperature 10 "MCI"))
                              fire-rules)]

    ;; Ensure expected join occurred.
    (is (= #{{:?t 10}}
           (set (query session same-wind-and-temp))))

    ;; Ensure item was removed as viewed by the query.

    (is (= #{}
           (set (query retracted-session same-wind-and-temp))))))

(deftest test-negation-of-changing-result-from-accumulator-in-fire-rules
  (let [min-temp-rule (dsl/parse-rule [[?c <- (acc/min :temperature :returns-fact true) :from [ColdAndWindy]]]
                                      (insert! (->Cold (:temperature ?c)))
                                      {:salience 5})

        ;; Force successive matching and retraction of the negation condition within the fire-rules loop.
        no-join-negation (dsl/parse-rule [[:not [Cold]]]
                                         (insert! (->Hot 100))
                                         {:salience 6})

        complex-join-negation (dsl/parse-rule [[Temperature (= ?t temperature)]
                                               [:not [Cold (< temperature ?t)]]]
                                              (insert! (->Hot 100))
                                              {:salience 6})

        ;; Give the two rules producing a ColdAndWindy fact different salience so that we will switch
        ;; salience groups between them.  When we switch, the higher-salience rules accumulating on ColdAndWindy
        ;; and the negation that uses the Cold produced from the minimum ColdAndWindy will fire first before moving
        ;; on to second-cold from first-cold.
        first-cold (dsl/parse-rule [[First]]
                                   (insert! (->ColdAndWindy 20 20))
                                   {:salience -1})

        second-cold (dsl/parse-rule [[Second]]
                                    (insert! (->ColdAndWindy 10 10))
                                    {:salience -2})

        hot-query (dsl/parse-query [] [[Hot]])

        invariant-productions [min-temp-rule first-cold second-cold hot-query]]

    (doseq [[empty-session join-type] [[(mk-session (conj invariant-productions no-join-negation)
                                                    :cache false)
                                        "no join"]
                                       [(mk-session (conj invariant-productions complex-join-negation)
                                                    :cache false)
                                        "complex join"]]]

      (is (empty? (-> empty-session
                      (insert (->First) (->Second))
                      fire-rules
                      (query hot-query)))
          (str "No Hot should exist in the session for join type: " join-type)))))

(deftest test-simple-disjunction
  (let [or-query (dsl/parse-query [] [[:or [Temperature (< temperature 20) (= ?t temperature)]
                                       [WindSpeed (> windspeed 30) (= ?w windspeed)]]])

        session (mk-session [or-query])

        cold-session (-> session
                         (insert (->Temperature 15 "MCI"))
                         fire-rules)
        windy-session (-> session
                          (insert (->WindSpeed 50 "MCI"))
                          fire-rules)]

    (is (= #{{:?t 15}}
           (set (query cold-session or-query))))

    (is (= #{{:?w 50}}
           (set (query windy-session or-query))))))

(deftest test-disjunction-with-nested-and


  (let [really-cold-or-cold-and-windy
        (dsl/parse-query [] [[:or [Temperature (< temperature 0) (= ?t temperature)]
                                  [:and [Temperature (< temperature 20) (= ?t temperature)]
                                        [WindSpeed (> windspeed 30) (= ?w windspeed)]]]])

        rulebase [really-cold-or-cold-and-windy]

        cold-session (-> (mk-session rulebase)
                         (insert (->Temperature -10 "MCI"))
                         fire-rules)

        windy-session (-> (mk-session rulebase)
                          (insert (->Temperature 15 "MCI"))
                          (insert (->WindSpeed 50 "MCI"))
                          fire-rules)]

    (is (= #{{:?t -10}}
           (set (query cold-session really-cold-or-cold-and-windy))))

    (is (= #{{:?w 50 :?t 15}}
           (set (query windy-session really-cold-or-cold-and-windy))))))

(deftest test-multi-conditions-with-nested-conjunction-inside-disjunction

  (let [find-conditions (dsl/parse-query []
                                         [[?tmp <- Temperature (= ?t temperature)
                                           (= ?loc location)]
                                          [:or
                                           [:and
                                            [?w <- WindSpeed (= ?loc location)]
                                            [?c <- Cold (= ?t temperature)]]
                                           [?cw <- ColdAndWindy (= ?t temperature) (> windspeed 50)]]])
        temp (->Temperature 10 "MCI")
        cold (->Cold 10)
        wind-speed (->WindSpeed 50 "MCI")
        cold-and-windy (->ColdAndWindy 10 80)

        res (-> (mk-session [find-conditions]
                            :cache true)
                (insert temp
                        cold
                        wind-speed
                        cold-and-windy)
                fire-rules
                (query find-conditions)
                set)]

    (is (= #{{:?tmp temp
              :?t 10
              :?loc "MCI"
              :?w wind-speed
              :?c cold}
             {:?tmp temp
              :?t 10
              :?loc "MCI"
              :?cw cold-and-windy}}
           res))))

(deftest test-expression-to-dnf

  ;; Test simple condition.
  (is (= {:type Temperature :constraints []}
         (com/to-dnf {:type Temperature :constraints []})))

  ;; Test single-item conjunction removes unnecessary operator.
  (is (=  {:type Temperature :constraints []}
          (com/to-dnf [:and {:type Temperature :constraints []}])))

  ;; Test multi-item conjunction.
  (is (= [:and
          {:type Temperature :constraints ['(> 2 1)]}
          {:type Temperature :constraints ['(> 3 2)]}
          {:type Temperature :constraints ['(> 4 3)]}]
         (com/to-dnf
          [:and
           {:type Temperature :constraints ['(> 2 1)]}
           {:type Temperature :constraints ['(> 3 2)]}
           {:type Temperature :constraints ['(> 4 3)]}])))

  ;; Test simple disjunction.
  (is  (= [:or
           {:type Temperature :constraints ['(> 2 1)]}
           {:type Temperature :constraints ['(> 3 2)]}
           {:type Temperature :constraints ['(> 4 3)]}]
         (com/to-dnf
          [:or
           {:type Temperature :constraints ['(> 2 1)]}
           {:type Temperature :constraints ['(> 3 2)]}
           {:type Temperature :constraints ['(> 4 3)]}])))


  ;; Test simple disjunction with nested conjunction.
  (is (= [:or
          {:type Temperature :constraints ['(> 2 1)]}
          [:and
           {:type Temperature :constraints ['(> 3 2)]}
           {:type Temperature :constraints ['(> 4 3)]}]]
         (com/to-dnf
          [:or
           {:type Temperature :constraints ['(> 2 1)]}
           [:and
            {:type Temperature :constraints ['(> 3 2)]}
            {:type Temperature :constraints ['(> 4 3)]}]])))

  ;; Test disjunction nested inside of consecutive conjunctions.
  (is (= [:or
          [:and
           {:constraints ['(> 4 3)] :type Temperature}
           {:constraints ['(> 3 2)] :type Temperature}
           {:constraints ['(> 2 1)] :type Temperature}]
          [:and
           {:constraints ['(> 5 4)] :type Temperature}
           {:constraints ['(> 3 2)] :type Temperature}
           {:constraints ['(> 2 1)] :type Temperature}]]
         (com/to-dnf
          [:and
           {:type Temperature :constraints ['(> 2 1)]}
           [:and
            {:type Temperature :constraints ['(> 3 2)]}
            [:or
             {:type Temperature :constraints ['(> 4 3)]}
             {:type Temperature :constraints ['(> 5 4)]}]]])))

  ;; Test simple distribution of a nested or expression.
  (is (= [:or
          [:and
           {:type Temperature :constraints ['(> 2 1)]}
           {:type Temperature :constraints ['(> 4 3)]}]
          [:and
           {:type Temperature :constraints ['(> 3 2)]}
           {:type Temperature :constraints ['(> 4 3)]}]]
         (com/to-dnf
          [:and
           [:or
            {:type Temperature :constraints ['(> 2 1)]}
            {:type Temperature :constraints ['(> 3 2)]}]
           {:type Temperature :constraints ['(> 4 3)]}])))

  ;; Test push negation to edges.
  (is (= [:and
          [:not {:type Temperature :constraints ['(> 2 1)]}]
          [:not {:type Temperature :constraints ['(> 3 2)]}]
          [:not {:type Temperature :constraints ['(> 4 3)]}]]
         (com/to-dnf
          [:not
           [:or
            {:type Temperature :constraints ['(> 2 1)]}
            {:type Temperature :constraints ['(> 3 2)]}
            {:type Temperature :constraints ['(> 4 3)]}]])))

  ;; Remove unnecessary and.
  (is (= [:and
          [:not {:type Temperature :constraints ['(> 2 1)]}]
          [:not {:type Temperature :constraints ['(> 3 2)]}]
          [:not {:type Temperature :constraints ['(> 4 3)]}]]
         (com/to-dnf
          [:and
           [:not
            [:or
             {:type Temperature :constraints ['(> 2 1)]}
             {:type Temperature :constraints ['(> 3 2)]}
             {:type Temperature :constraints ['(> 4 3)]}]]])))

  (is (= [:or
            {:type Temperature :constraints ['(> 2 1)]}
            [:and
             {:type Temperature :constraints ['(> 3 2)]}
             {:type Temperature :constraints ['(> 4 3)]}]]

         (com/to-dnf
          [:and
           [:or
            {:type Temperature :constraints ['(> 2 1)]}
            [:and
             {:type Temperature :constraints ['(> 3 2)]}
             {:type Temperature :constraints ['(> 4 3)]}]]])))

  ;; Test push negation to edges.
  (is (= [:or
          [:not {:type Temperature :constraints ['(> 2 1)]}]
          [:not {:type Temperature :constraints ['(> 3 2)]}]
          [:not {:type Temperature :constraints ['(> 4 3)]}]]
         (com/to-dnf
          [:not
           [:and
            {:type Temperature :constraints ['(> 2 1)]}
            {:type Temperature :constraints ['(> 3 2)]}
            {:type Temperature :constraints ['(> 4 3)]}]])))

  ;; Test simple identity disjunction.
  (is (= [:or
          [:not {:type Temperature :constraints ['(> 2 1)]}]
          [:not {:type Temperature :constraints ['(> 3 2)]}]]
         (com/to-dnf
          [:or
           [:not {:type Temperature :constraints ['(> 2 1)]}]
           [:not {:type Temperature :constraints ['(> 3 2)]}]])))

  ;; Test distribution over multiple and expressions.
  (is (= [:or
          [:and
           {:type Temperature :constraints ['(> 2 1)]}
           {:type Temperature :constraints ['(> 5 4)]}
           {:type Temperature :constraints ['(> 6 5)]}]
          [:and
           {:type Temperature :constraints ['(> 3 2)]}
           {:type Temperature :constraints ['(> 5 4)]}
           {:type Temperature :constraints ['(> 6 5)]}]
          [:and
           {:type Temperature :constraints ['(> 4 3)]}
           {:type Temperature :constraints ['(> 5 4)]}
           {:type Temperature :constraints ['(> 6 5)]}]]
         (com/to-dnf
          [:and
           [:or
            {:type Temperature :constraints ['(> 2 1)]}
            {:type Temperature :constraints ['(> 3 2)]}
            {:type Temperature :constraints ['(> 4 3)]}]
           {:type Temperature :constraints ['(> 5 4)]}
           {:type Temperature :constraints ['(> 6 5)]}]))))

(def simple-defrule-side-effect (atom nil))
(def other-defrule-side-effect (atom nil))

(defrule test-rule
  [Temperature (< temperature 20)]
  =>
  (reset! other-defrule-side-effect ?__token__)
  (reset! simple-defrule-side-effect ?__token__))

(deftest test-simple-defrule
  (let [session (-> (mk-session [test-rule])
                    (insert (->Temperature 10 "MCI")))]

    (fire-rules session)

    (is (has-fact? @simple-defrule-side-effect (->Temperature 10 "MCI")))
    (is (has-fact? @other-defrule-side-effect (->Temperature 10 "MCI")))))

(defquery cold-query
  [:?l]
  [Temperature (< temperature 50)
               (= ?t temperature)
               (= ?l location)])

(defquery hot-query
  [?l]
  [Temperature (>= temperature 50)
               (= ?t temperature)
               (= ?l location)])

(deftest test-defquery
  (let [session (-> (mk-session [cold-query hot-query])
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 20 "MCI")) ; Test multiple items in result.
                    (insert (->Temperature 10 "ORD"))
                    (insert (->Temperature 35 "BOS"))
                    (insert (->Temperature 80 "BOS"))
                    fire-rules)]

    ;; Query by location.

    (testing "query by location with :?keyword params"
      (is (= #{{:?l "BOS" :?t 35}}
             (set (query session cold-query :?l "BOS"))))

      (is (= #{{:?l "BOS" :?t 80}}
             (set (query session hot-query :?l "BOS"))))

      (is (= #{{:?l "MCI" :?t 15} {:?l "MCI" :?t 20}}
             (set (query session cold-query :?l "MCI"))))

      (is (= #{{:?l "ORD" :?t 10}}
             (set (query session cold-query :?l "ORD")))))

    (testing "query by location with '?symbol params"
      (is (= #{{:?l "BOS" :?t 35}}
             (set (query session cold-query '?l "BOS"))))

      (is (= #{{:?l "BOS" :?t 80}}
             (set (query session hot-query '?l "BOS"))))

      (is (= #{{:?l "MCI" :?t 15} {:?l "MCI" :?t 20}}
             (set (query session cold-query '?l "MCI"))))

      (is (= #{{:?l "ORD" :?t 10}}
             (set (query session cold-query '?l "ORD")))))))

(deftest test-rules-from-ns
  ;; Validate that rules behave identically when loaded from vars that contain a single
  ;; rule or query or when loaded from a var with appropriate metadata that contains
  ;; a sequence of rules and/or queries.
  (doseq [rules-ns ['clara.sample-ruleset
                    'clara.sample-ruleset-seq]]
    (is (= #{{:?loc "MCI"} {:?loc "BOS"}}
           (set (-> (mk-session rules-ns)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 22 "BOS"))
                    (insert (->Temperature 50 "SFO"))
                    fire-rules
                    (query sample/freezing-locations))))
        (str "Freezing locations not found using rules namespace " rules-ns))

    (let [session (-> (mk-session rules-ns)
                      (insert (->Temperature 15 "MCI"))
                      (insert (->WindSpeed 45 "MCI"))
                      (fire-rules))]

      (is (= #{{:?fact (->ColdAndWindy 15 45)}}
             (set
              (query session sample/find-cold-and-windy)))
          (str "Expected ColdAndWindy fact not found using rules namespace " rules-ns)))))

(deftest test-rules-from-multi-namespaces
  (doseq [sample-ruleset-ns ['clara.sample-ruleset
                             'clara.sample-ruleset-seq]]
    (let [session (-> (mk-session sample-ruleset-ns 'clara.other-ruleset)
                      (insert (->Temperature 15 "MCI"))
                      (insert (->Temperature 10 "BOS"))
                      (insert (->Temperature 50 "SFO"))
                      (insert (->Temperature -10 "CHI"))
                      fire-rules)]

      (is (= #{{:?loc "MCI"} {:?loc "BOS"} {:?loc "CHI"}}
             (set (query session sample/freezing-locations)))
          (str "Failed to find freezing locations using sample-ruleset namespace " sample-ruleset-ns))

      (is (= #{{:?loc "CHI"}}
             (set (query session other/subzero-locations)))
          (str "Failed to find expected subzero location using sample-ruleset namespace " sample-ruleset-ns)))))

(deftest test-transitive-rule
  (doseq [sample-ruleset-ns ['clara.sample-ruleset
                             'clara.sample-ruleset-seq]]
    (is (= #{{:?fact (->LousyWeather)}}
           (set (-> (mk-session sample-ruleset-ns 'clara.other-ruleset)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->WindSpeed 45 "MCI"))
                    (fire-rules)
                    (query sample/find-lousy-weather))))
       (str "Failed to find LousyWeather using sample-ruleset namespace " sample-ruleset-ns))))

(deftest test-mark-as-fired
  (let [rule-output (atom nil)
        cold-rule (dsl/parse-rule [[Temperature (< temperature 20)]]
                                  (reset! rule-output ?__token__) )

        session (-> (mk-session [cold-rule])
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

    (is (has-fact? @rule-output (->Temperature 10 "MCI")))

    ;; Reset the side effect then re-fire the rules
    ;; to ensure the same one isn't fired twice.
    (reset! rule-output nil)
    (fire-rules session)
    (is (= nil @rule-output))

    ;; Retract and re-add the item to yield a new execution of the rule.
    (-> session
        (retract (->Temperature 10 "MCI"))
        (insert (->Temperature 10 "MCI"))
        (fire-rules))

    (is (has-fact? @rule-output (->Temperature 10 "MCI")))))


(deftest test-chained-inference
  (let [item-query (dsl/parse-query [] [[?item <- Fourth]])

        session (-> (mk-session [(dsl/parse-rule [[Third]] (insert! (->Fourth)))
                                 (dsl/parse-rule [[First]] (insert! (->Second)))
                                 (dsl/parse-rule [[Second]] (insert! (->Third)))
                                 item-query])
                    (insert (->First))
                    (fire-rules))]

    ;; The query should identify all items that were inserted and matched the
    ;; expected criteria.
    (is (= #{{:?item (->Fourth)}}
           (set (query session item-query))))))

(deftest test-node-id-map
  (let [cold-rule (dsl/parse-rule [[Temperature (< temperature 20)]]
                                  (println "Placeholder"))
        windy-rule (dsl/parse-rule [[WindSpeed (> windspeed 25)]]
                                   (println "Placeholder"))

        rulebase  (.rulebase (mk-session [cold-rule windy-rule]))

        cold-rule2 (dsl/parse-rule [[Temperature (< temperature 20)]]
                                   (println "Placeholder"))
        windy-rule2 (dsl/parse-rule [[WindSpeed (> windspeed 25)]]
                                    (println "Placeholder"))

        rulebase2 (.rulebase (mk-session [cold-rule2 windy-rule2]))]

    ;; The keys should be consistent between maps since the rules are identical.
    (is (= (keys (:id-to-node rulebase))
           (keys (:id-to-node rulebase2))))

    ;; Ensure there are beta and production nodes as expected.
    ;; 2 alpha-nodes, 2 root-join nodes, and 2 production nodes
    (is (= 6 (count (:id-to-node rulebase))))))

(deftest test-simple-test
  (let [distinct-temps-query (dsl/parse-query [] [[Temperature (< temperature 20) (= ?t1 temperature)]
                                                  [Temperature (< temperature 20) (= ?t2 temperature)]
                                                  [:test (< ?t1 ?t2)]])

        session (-> (mk-session [distinct-temps-query])
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 80 "MCI"))
                    fire-rules)]

    ;; Finds two temperatures such that t1 is less than t2.
    (is (= #{ {:?t1 10, :?t2 15}}
           (set (query session distinct-temps-query))))))

(deftest test-test-in-negation

  (let [not-different-temps (dsl/parse-query
                             []
                             [[Temperature (= ?a location)]
                              [WindSpeed (= ?b location)]
                              [:not [:test (= ?a ?b)]]])

        session (mk-session [not-different-temps])]

    (is (empty? (-> session
                    (insert (->Temperature 10 "MCI")
                            (->WindSpeed 10 "MCI"))
                    fire-rules
                    (query not-different-temps))))

    (is (= [{:?a "MCI" :?b "ORD"}]
           (-> session
               (insert (->Temperature 10 "MCI")
                       (->WindSpeed 10 "ORD"))
               fire-rules
               (query not-different-temps))))))

(deftest test-empty-test-condition
  (let [exception-data {:line 123 :column 456}]
    (is (assert-ex-data
          exception-data
          (dsl/parse-query*
            []
            [[:test]]
            {}
            exception-data)))))

(deftest test-multi-insert-retract

  (is (= #{{:?loc "MCI"} {:?loc "BOS"}}
         (set (-> (mk-session 'clara.sample-ruleset)
                  (insert (->Temperature 15 "MCI"))
                  (insert (->Temperature 22 "BOS"))

                  ;; Insert a duplicate and then retract it.
                  (insert (->Temperature 22 "BOS"))
                  (retract (->Temperature 22 "BOS"))
                  (fire-rules)
                  (query sample/freezing-locations)))))

  ;; Normal retractions should still work.
  (is (= #{}
         (set (-> (mk-session 'clara.sample-ruleset)
                  (insert (->Temperature 15 "MCI"))
                  (insert (->Temperature 22 "BOS"))
                  (retract (->Temperature 22 "BOS") (->Temperature 15 "MCI"))
                  (fire-rules)
                  (query sample/freezing-locations)))))


  (let [session (-> (mk-session 'clara.sample-ruleset)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->WindSpeed 45 "MCI"))

                    ;; Insert a duplicate and then retract it.
                    (insert (->WindSpeed 45 "MCI"))
                    (retract (->WindSpeed 45 "MCI"))
                    (fire-rules))]

    (is (= #{{:?fact (->ColdAndWindy 15 45)}}
           (set
            (query session sample/find-cold-and-windy))))))

(deftest test-no-loop
  (let [reduce-temp (dsl/parse-rule [[?t <- Temperature (> temperature 0) (= ?v temperature)]]
                             (do
                               (retract! ?t)
                               (insert! (->Temperature (- ?v 1) "MCI")))
                             {:no-loop true})

        temp-query (dsl/parse-query [] [[Temperature (= ?t temperature)]])


        session (-> (mk-session [reduce-temp temp-query])
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

    ;; Only one reduced temperature should be present.
    (is (= [{:?t 9}] (query session temp-query)))))

;; Test to ensure :no-loop applies to retractions as well as activations of rules.
;; For https://github.com/cerner/clara-rules/issues/99
(deftest test-no-loop-retraction
  (let [counter (atom 0)
        looper (dsl/parse-rule [[:not [:marker]]]

                               (do
                                 ;; Safety net to avoid infinite loop if test fails.
                                 (swap! counter inc)
                                 (when (> @counter 1)
                                   (throw (ex-info "No loop counter should not activate more than once!" {})))

                                 (insert! ^{:type :marker} {:has-marker true}))

                               {:no-loop true})
        has-marker (dsl/parse-query [] [[?marker <- :marker]])]

    (is (= [{:?marker {:has-marker true}}]
           (-> (mk-session [looper has-marker])
               (fire-rules)
               (query has-marker))))))

(defrule reduce-temp-no-loop
  "Example rule to reduce temperature."
  {:no-loop true}
  [?t <- Temperature (= ?v temperature)]
  =>
  (do
    (retract! ?t)
    (insert-unconditional! (->Temperature (- ?v 1) "MCI"))))

(deftest test-no-temp

  (let [rule-output (atom nil)
        ;; Insert a new fact and ensure it exists.

        temp-query (dsl/parse-query [] [[Temperature (= ?t temperature)]])

        session (-> (mk-session [reduce-temp-no-loop temp-query])
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

    ;; Only one reduced temperature should be present.
    (is (= [{:?t 9}] (query session temp-query)))))


;; Test behavior discussed in https://github.com/cerner/clara-rules/issues/35
(deftest test-identical-facts
  (let [ident-query (dsl/parse-query [] [[?t1 <- Temperature (= ?loc location)]
                                         [?t2 <- Temperature (= ?loc location)]
                                         [:test (not (identical? ?t1 ?t2))]])

        temp (->Temperature 15 "MCI")
        temp2 (->Temperature 15 "MCI")

        session (-> (mk-session [ident-query])
                    (insert temp temp)
                    fire-rules)

        session-with-dups (-> (mk-session [ident-query])
                              (insert temp temp2)
                              fire-rules)]

    ;; The inserted facts are identical, so there cannot be a non-identicial match.
    (is (empty? (query session ident-query)))


    ;; Duplications should have two matches, since either fact can bind to either condition.
    (is (= [{:?t1 #clara.rules.testfacts.Temperature{:temperature 15, :location "MCI"}
             :?t2 #clara.rules.testfacts.Temperature{:temperature 15, :location "MCI"}
             :?loc  "MCI"}
            {:?t2 #clara.rules.testfacts.Temperature{:temperature 15, :location "MCI"}
             :?t1 #clara.rules.testfacts.Temperature{:temperature 15, :location "MCI"}
             :?loc "MCI"}]
           (query session-with-dups ident-query)))))


;; An EDN string for testing. This would normally be stored in an external file. The structure simply needs to be a
;; sequence of maps matching the clara.rules.schema/Production schema.
(def external-rules "[{:name \"cold-query\", :params #{:?l}, :lhs [{:type clara.rules.testfacts.Temperature, :constraints [(< temperature 50) (= ?t temperature) (= ?l location)]}]}]")

(deftest test-external-rules
  (let [session (-> (mk-session (edn/read-string external-rules))
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 20 "MCI")) ; Test multiple items in result.
                    (insert (->Temperature 10 "ORD"))
                    (insert (->Temperature 35 "BOS"))
                    (insert (->Temperature 80 "BOS"))
                    fire-rules)]

    ;; Query by location.
    (is (= #{{:?l "BOS" :?t 35}}
           (set (query session "cold-query" :?l "BOS"))))

    (is (= #{{:?l "MCI" :?t 15} {:?l "MCI" :?t 20}}
           (set (query session "cold-query" :?l "MCI"))))

    (is (= #{{:?l "ORD" :?t 10}}
           (set (query session "cold-query" :?l "ORD"))))))


(defsession my-session 'clara.sample-ruleset)

(deftest test-defsession

  (is (= #{{:?loc "MCI"} {:?loc "BOS"}}
       (set (-> my-session
                (insert (->Temperature 15 "MCI"))
                (insert (->Temperature 22 "BOS"))
                (insert (->Temperature 50 "SFO"))
                fire-rules
                (query sample/freezing-locations)))))

  (let [session (-> (mk-session 'clara.sample-ruleset)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->WindSpeed 45 "MCI"))
                    (fire-rules))]

    (is (= #{{:?fact (->ColdAndWindy 15 45)}}
           (set
            (query session sample/find-cold-and-windy))))))

;; Test for issue 46
(deftest test-different-return-type
  (let [q1 (dsl/parse-query [] [[?var1 <- (acc/count) :from [Temperature]]])
        q2 (dsl/parse-query [] [[?var2 <- (acc/count) :from [Temperature]]])

        session (-> (mk-session [q1 q2])
                    (insert (->Temperature 40 "MCI")
                            (->Temperature 50 "SFO"))
                    (fire-rules))]

    (is (= [{:?var1 2}] (query session q1)))
    (is (= [{:?var2 2}] (query session q2)))))

;; Test for overridding how type ancestors are determined.
(deftest test-override-ancestors
  (let [special-ancestor-query (dsl/parse-query [] [[?result <- :my-ancestor]])
        type-ancestor-query (dsl/parse-query [] [[?result <- Object]])

        session (-> (mk-session [special-ancestor-query type-ancestor-query] :ancestors-fn (fn [type] [:my-ancestor]))
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 80 "MCI"))
                    fire-rules)]

    ;; The special ancestor query should match everything since our trivial
    ;; ancestry function treats :my-ancestor as an ancestor of everything.
    (is (= #{{:?result (->Temperature 15 "MCI") }
             {:?result (->Temperature 10 "MCI") }
             {:?result (->Temperature 80 "MCI") }}
           (set (query session special-ancestor-query))))

    ;; There shouldn't be anything that matches our typical ancestor here.
    (is (empty? (query session type-ancestor-query)))))

(deftest test-shared-condition
  (let [cold-query (dsl/parse-query [] [[Temperature (< temperature 20) (= ?t temperature)]])
        cold-windy-query (dsl/parse-query [] [[Temperature (< temperature 20) (= ?t temperature)]
                                              [WindSpeed (> windspeed 25)]])

        beta-graph (com/to-beta-graph #{cold-query cold-windy-query} (let [x (atom 0)]
                                                                       (fn []
                                                                         (swap! x inc))))]

    ;; The above rules should share a root condition, so there are
    ;; only two distinct conditions in our network, plus the root node.
    (is (= 3 (count (:id-to-condition-node beta-graph))))))

(def external-type :temperature)

(def external-constant 20)

(defquery match-external
  []
  [external-type [{temp :value}] (< temp external-constant) (= ?t temp)])

(deftest test-match-external-type
  (let [session (-> (mk-session [match-external] :fact-type-fn :type)
                    (insert {:type :temperature :value 15 :location "MCI"}
                            {:type :temperature :value 10 :location "MCI"}
                            {:type :windspeed :value 5 :location "MCI"}
                            {:type :temperature :value 80 :location "MCI"})
                    fire-rules)]

    (is (= #{{:?t 15} {:?t 10}}
           (set (query session match-external))))))

(deftest test-extract-simple-test
  (let [distinct-temps-query (dsl/parse-query [] [[Temperature (< temperature 20)
                                                               (= ?t1 temperature)]

                                                  [Temperature (< temperature 20)
                                                               (= ?t2 temperature)
                                                   (< ?t1 temperature)]])

        session  (-> (mk-session [distinct-temps-query])
                     (insert (->Temperature 15 "MCI"))
                     (insert (->Temperature 10 "MCI"))
                     (insert (->Temperature 80 "MCI"))
                     fire-rules)]

    ;; Finds two temperatures such that t1 is less than t2.
    (is (= #{ {:?t1 10, :?t2 15}}
           (set (query session distinct-temps-query))))))

(deftest test-extract-nested-test
  (let [distinct-temps-query (dsl/parse-query [] [[Temperature (< temperature 20)
                                                               (= ?t1 temperature)]

                                                  [Temperature (< temperature 20)
                                                               (= ?t2 temperature)
                                                   (< (- ?t1 0) temperature)]])

        session  (-> (mk-session [distinct-temps-query])
                     (insert (->Temperature 15 "MCI"))
                     (insert (->Temperature 10 "MCI"))
                     (insert (->Temperature 80 "MCI"))
                     fire-rules)]

    ;; Finds two temperatures such that t1 is less than t2.
    (is (= #{ {:?t1 10, :?t2 15}}
           (set (query session distinct-temps-query))))))


;; External structure to ensure that salience works with defrule as well.
(def salience-rule-output (atom []))

(defrule salience-rule4
  {:salience -50}
  [Temperature]
  =>
  (swap! salience-rule-output conj -50))

(deftest test-salience
  (doseq [[sort-fn
           group-fn
           expected-order]

          [[:default-sort :default-group :forward-order]
           [:default-sort :salience-group :forward-order]
           [:default-sort :neg-salience-group :backward-order]

           [:numeric-greatest-sort :default-group :forward-order]
           [:numeric-greatest-sort :salience-group :forward-order]
           [:numeric-greatest-sort :neg-salience-group :backward-order]


           [:boolean-greatest-sort :default-group :forward-order]
           [:boolean-greatest-sort :salience-group :forward-order]
           [:boolean-greatest-sort :neg-salience-group :backward-order]


           [:numeric-least-sort :default-group :backward-order]
           [:numeric-least-sort :salience-group :backward-order]
           [:numeric-least-sort :neg-salience-group :forward-order]

           [:boolean-least-sort :default-group :backward-order]
           [:boolean-least-sort :salience-group :backward-order]
           [:boolean-least-sort :neg-salience-group :forward-order]]]

    (let [rule1 (assoc
                 (dsl/parse-rule [[Temperature]]
                                 (swap! salience-rule-output conj 100))
                 :props {:salience 100})

          rule2 (assoc
                 (dsl/parse-rule [[Temperature ]]
                                 (swap! salience-rule-output conj 50))
                 :props {:salience 50})

          rule3 (assoc
                 (dsl/parse-rule [[Temperature ]]
                                 (swap! salience-rule-output conj 0))
                 :props {:salience 0})

          numeric-greatest-sort (fn [x y]
                                  (cond
                                    (= x y) 0
                                    (> x y) -1
                                    :else 1))

          numeric-least-sort (fn [x y]
                               (numeric-greatest-sort y x))

          salience-group-fn (fn [production]
                              (or (some-> production :props :salience)
                                  0))

          neg-salience-group-fn (fn [p]
                                  (- (salience-group-fn p)))]

      ;; Ensure the rule output reflects the salience-defined order.
      ;; independently of the order of the rules.
      (dotimes [n 10]

        (reset! salience-rule-output [])

        (-> (com/mk-session [(shuffle [rule1 rule3 rule2 salience-rule4])
                             :cache false
                             :activation-group-sort-fn (condp = sort-fn
                                                         :default-sort nil
                                                         :numeric-greatest-sort numeric-greatest-sort
                                                         :numeric-least-sort numeric-least-sort
                                                         :boolean-greatest-sort  >
                                                         :boolean-least-sort <)
                             :activation-group-fn (condp = group-fn
                                                    :default-group nil
                                                    :salience-group salience-group-fn
                                                    :neg-salience-group neg-salience-group-fn)])
            (insert (->Temperature 10 "MCI"))
            (fire-rules))

        (let [test-fail-str
              (str "Failure with sort-fn: " sort-fn ", group-fn: " group-fn ", and expected order: " expected-order)]
          (condp = expected-order
            :forward-order
            (is (= [100 50 0 -50] @salience-rule-output)
                test-fail-str)

            :backward-order
            (is (= [-50 0 50 100] @salience-rule-output)
                test-fail-str)))))))

(deftest test-negation-with-extracted-test
    (let [colder-temp (dsl/parse-rule [[Temperature (= ?t temperature)]
                                       [:not [Cold (or (< temperature ?t)
                                                       (< temperature 0))]]]

                                    (insert! ^{:type :found-colder} {:found true}))

          find-colder (dsl/parse-query [] [[?f <- :found-colder]])

          session (-> (mk-session [colder-temp find-colder] :cache false))]

      ;; Test no token.
      (is (empty? (-> session
                      (insert (->Cold 11))
                      (fire-rules)
                      (query find-colder))))

      ;; Test simple insertion.
      (is (= [{:?f {:found true}}]
             (-> session
                 (insert (->Temperature 10 "MCI"))
                 (insert (->Cold 11))
                 (fire-rules)
                 (query find-colder))))

      ;; Test insertion with right-hand match first.
      (is (= [{:?f {:found true}}]
             (-> session
                 (insert (->Cold 11))
                 (insert (->Temperature 10 "MCI"))
                 (fire-rules)
                 (query find-colder))))

      ;; Test no fact matching not.
      (is (= [{:?f {:found true}}]
             (-> session
                 (insert (->Temperature 10 "MCI"))
                 (fire-rules)
                 (query find-colder))))

      ;; Test violate negation.
      (is (empty? (-> session
                      (insert (->Cold 9))
                      (insert (->Temperature 10 "MCI"))
                      (fire-rules)
                      (query find-colder))))

      ;; Test violate negation alternate order.
      (is (empty? (-> session
                      (insert (->Temperature 10 "MCI"))
                      (insert (->Cold 9))
                      (fire-rules)
                      (query find-colder))))

      ;; Test retract violation.
      (is (= [{:?f {:found true}}]
           (-> session
               (insert (->Cold 9))
               (insert (->Temperature 10 "MCI"))
               (fire-rules)
               (retract (->Cold 9))
               (fire-rules)
               (query find-colder))))

      ;; Test only partial retraction of violation,
      ;; ensuring the remaining violation holds.
      (is (empty? (-> session
                      (insert (->Cold 9))
                      (insert (->Cold 9))
                      (insert (->Temperature 10 "MCI"))
                      (fire-rules)
                      (retract (->Cold 9))
                      (fire-rules)
                      (query find-colder))))

      ;; Test violate negation after success.
      (is (empty? (-> session
                      (insert (->Cold 11))
                      (insert (->Temperature 10 "MCI"))
                      (fire-rules)
                      (insert (->Cold 9))
                      (fire-rules)
                      (query find-colder))))))

;; TODO: Move this once it succeeds with def-rules-test.  The def-rules-test macro may
;; be stripping the metadata somewhere.
(deftest ^{:doc "Ensuring that ProductionNodes compilation is separate per node in network.
                 See https://github.com/cerner/clara-rules/pull/145 for more context."}
  test-multiple-equiv-rhs-different-metadata
  (let [r1 (dsl/parse-rule [[?t <- Temperature]]
                           (insert! ^{:type :a} {:t ?t}))
        r2 (dsl/parse-rule [[?t <- Temperature]]
                           (insert! ^{:type :b} {:t ?t}))
        q1 (dsl/parse-query []
                            [[?a <- :a]])
        q2 (dsl/parse-query []
                            [[?b <- :b]])

        temp (->Temperature 60 "MCI")
        s (-> (mk-session [r1 r2 q1 q2])
              (insert temp)
              fire-rules)
        res1 (set (query s q1))
        res2 (set (query s q2))]

    (is (= #{{:?a {:t temp}}}
           res1))
    (is (= #{{:?b {:t temp}}}
           res2))))

(deftest test-accumulator-with-extracted-test
  (let [q1 (dsl/parse-query []
                            [[?res <- (acc/all) :from [Temperature (= ?t temperature)]]
                             [:test (and ?t (< ?t 10))]])

        q2 (dsl/parse-query []
                            [[?res <- (acc/all) :from [Temperature]]
                             [:test (not (empty? ?res))]])]

    (is (= [{:?res [(->Temperature 9 "MCI")] :?t 9}]
           (-> (mk-session [q1])
               (insert (->Temperature 9 "MCI"))
               (fire-rules)
               (query q1))))

    (is (= [{:?res [(->Temperature 9 "MCI")]}]
           (-> (mk-session [q2])
               (insert (->Temperature 9 "MCI"))
               (fire-rules)
               (query q2))))))

#_{:clj-kondo/ignore [:unresolved-symbol]}
(deftest test-unmatched-nested-binding
  ;; This should throw an exception because ?w may not be bound. There is no
  ;; ancestor of the constraint that includes ?w, so there isn't a consitent value
  ;; that can be associated with ?w, therefore we throw an exception when
  ;; compiling the rules.
  (let [same-wind-and-temp (dsl/parse-query []
                                            [[WindSpeed (or (= "MCI" location)
                                                            (= ?w windspeed))]])]

    (assert-ex-data {:variables #{'?w}}
                    (mk-session [same-wind-and-temp]))))

#_{:clj-kondo/ignore [:unresolved-symbol]}
(deftest test-unbound-bindings
  (let [accum-condition (dsl/parse-query []
                                         [[?ts <- (acc/all) :from [Temperature (and ?bogus (< ?bogus temperature))]]])
        negation-condition (dsl/parse-query []
                                        [[:not [WindSpeed (not= ?invalid location)]]])
        test-condition (dsl/parse-query []
                                    [[:test (< ?missing 10)]])
        multi-conditions (dsl/parse-query []
                                            [[Temperature (= ?temp temperature)
                                              (= ?loc location)]
                                             [Temperature (= ?loc location)
                                              (< ?temp temperature)]
                                             [Cold (< ?extra1 ?temp ?extra2)]])
        nested-conditions (dsl/parse-query []
                                           [[?t <- Temperature (= ?temp temperature)
                                              (= ?loc location)]
                                             [Cold (= ?temp temperature)
                                              ;; Demonstrating using an available :fact-binding
                                              (some? (:location ?t))
                                              (and (< ?unbound temperature 10))]])

        nested-accum-conditions (dsl/parse-query []
                                                 [[Temperature (= ?loc location)]
                                                  [?ts <- (acc/all) :from [Temperature (= ?loc location) (< ?invalid temperature)]]])
        bool-conditions (dsl/parse-query []
                                         [[?t <- Temperature (= ?temp temperature)
                                              (= ?loc location)]

                                          [:or
                                           [Cold (= ?temp temperature)
                                            (< temperature 10)]
                                           [WindSpeed (= ?loc location)
                                            (< windspeed 50)]
                                           [:not [WindSpeed (= ?loc location)
                                                  (< windspeed ?unbound)]]]])

        negation-equality-unbound (dsl/parse-query []
                                                   [[:not [Temperature (= ?unbound temperature)]]])]

    (assert-ex-data {:variables #{'?bogus}}
                    (mk-session [accum-condition]))

    (assert-ex-data {:variables #{'?invalid}}
                    (mk-session [negation-condition]))

    (assert-ex-data {:variables #{'?missing}}
                    (mk-session [test-condition]))

    (assert-ex-data {:variables #{'?extra1 '?extra2}}
                    (mk-session [multi-conditions]))

    (assert-ex-data {:variables #{'?unbound}}
                    (mk-session [nested-conditions]))

    (assert-ex-data {:variables #{'?invalid}}
                    (mk-session [nested-accum-conditions]))

    (assert-ex-data {:variables #{'?unbound}}
                    (mk-session [bool-conditions]))

    (assert-ex-data {:variables #{'?unbound}}
                    (mk-session [negation-equality-unbound]))))

;; Test for: https://github.com/cerner/clara-rules/issues/96
(deftest test-destructured-binding
  (let [rule-output-env (atom nil)
        rule {:name "clara.test-destructured-binding/test-destructured-binding"
              :env {:rule-output rule-output-env} ; Rule environment so we can check its output.
              :lhs '[{:args [[e a v]]
                     :type :foo
                     :constraints [(= e 1) (= v ?value)]}]
              :rhs '(reset! rule-output ?value)}]

    (-> (mk-session [rule] :fact-type-fn second)
        (insert [1 :foo 42])
        (fire-rules))

    (is (= 42 @rule-output-env))))

(deftest test-destructured-test-env-binding
  (let [rule-output-env (atom nil)
        rule {:name "clara.test-destructured-binding/test-destructured-test-env-binding"
              :env {:rule-output rule-output-env} ; Rule environment so we can check its output.
              :lhs '[{:args [[e a v]]
                      :type :foo
                      :constraints [(= e ?entity) (= v ?value)]}
                     {:constraints [(= ?entity 1) (reset! rule-output ?value)]}]
              :rhs '(inc 1)}]

    (-> (mk-session [rule] :fact-type-fn second)
        (insert [1 :foo 42])
        (fire-rules))

    (is (= 42 @rule-output-env))))

(deftest test-destructured-join-node-env-binding
  (let [rule-output-env (atom #{})
        rule {:name "clara.test-destructured-binding/test-destructured-test-env-binding"
              :env {:rule-output rule-output-env} ; Rule environment so we can check its output.
              :lhs '[{:args [[e a v]]
                      :type :foo
                      :constraints [(= e ?entity) (= v ?foo-value) (swap! rule-output conj ?foo-value)]}
                     {:accumulator (clara.rules.accumulators/all),
                      :from
                      {:args [[e a v]]
                       :type :bar
                       :constraints [(= e ?entity) (= v ?bar-value) (swap! rule-output conj ?bar-value)]},
                      :result-binding :?resp}]
              :rhs '(inc 1)}]
    (-> (mk-session [rule] :fact-type-fn second)
        (insert [1 :foo 42])
        (insert [1 :bar 43])
        (fire-rules))

    (is (= #{42 43} @rule-output-env))))

(def locals-shadowing-tester
  "Used to demonstrate local shadowing works in `test-explicit-rhs-map-can-use-ns-name-for-unqualified-symbols` below."
  :bad)

(deftest test-explicit-rhs-map-can-use-ns-name-for-unqualified-symbols
  (let [;; The :rhs form only makes sense within the scope of another
        ;; namespace - i.e. clara.sample-ruleset-seq.
        ;; Demonstrating this can work, independently of the Clara DSL.
        r1 {:ns-name 'clara.sample-ruleset-seq
            :name "r1"
            :lhs '[{:type :test
                    :constraints []}]
            :rhs '(clara.rules/insert! ^{:type :result}
                                       {:r :r1
                                        :v all-rules})}
        ;; However, rule structures are not required to specific a :ns-name if
        ;; they do not need them.  This would be safe if the :rhs form already
        ;; had qualified symbols used, which may typically be the case for
        ;; external tooling.
        r2 {:name "r2"
            :lhs '[{:type :test
                    :constraints []}]
            :rhs `(insert! ^{:type :result}
                           {:r :r2
                            :v locals-shadowing-tester})}
        q (dsl/parse-query [] [[?r <- :result]])]
    (is (= #{{:r :r1
              :v srs/all-rules}
             {:r :r2
              :v locals-shadowing-tester}}
           (set (map :?r
                     (-> (mk-session [r1 r2 q])
                         (insert ^{:type :test} {})
                         fire-rules
                         (query q))))))))

(deftest test-qualified-equals-for-fact-binding
  (let [get-accum-nodes #(->> %
                              .rulebase
                              :beta-roots
                              first
                              :children
                              (filter (partial instance? clara.rules.engine.AccumulateNode)))

        with-qualified-accum-nodes (get-accum-nodes
                                    (mk-session [(dsl/parse-query [] [[Temperature (= ?t temperature)]

                                                                      ;; Use fully-qualified = here.
                                                                      [?c <- (acc/all) :from [Cold (clojure.core/= temperature ?t)]]])]))

        without-qualified-accum-nodes (get-accum-nodes
                                       (mk-session [(dsl/parse-query [] [[Temperature (= ?t temperature)]

                                                                         ;; Use fully-qualified = here.
                                                                         [?c <- (acc/all) :from [Cold (= temperature ?t)]]])]))]

    (is (= (count with-qualified-accum-nodes)
           (count without-qualified-accum-nodes)))))

(deftest test-handle-exception
  (let [int-value (atom nil)
        to-int-rule (dsl/parse-rule [[?s <- String]]
                                    (try
                                      (reset! int-value (Integer/parseInt ?s))
                                      (catch NumberFormatException e
                                        (reset! int-value -1))))]

    ;; Test successful integer parse.
    (-> (mk-session [to-int-rule])
        (insert "100")
        (fire-rules))

    (is (= 100 @int-value))

    ;; Test failed integer parse.
    (-> (mk-session [to-int-rule])
        (insert "NotANumber")
        (fire-rules))

    (is (= -1 @int-value))))

(deftest test-condition-comparison-nil-safe
  (let [q (dsl/parse-query []
                           ;; Make two conditions that are very similar, but differ
                           ;; where a nil will be compared to something else.
                           [[(accumulate :retract-fn identity-retract :reduce-fn (fn [x y] nil)) :from [Temperature]]
                            [(accumulate :retract-fn identity-retract :reduce-fn (fn [x y] 10)) :from [Temperature]]])
        s (mk-session [q])]

    ;; Mostly just ensuring the rulebase was compiled successfully.
    (is (== 4 ;; 1 alpha-node, 2 accumulate nodes, and 1 query node
            (-> s
                .rulebase
                :id-to-node
                count)))))

(deftest test-rule-schema-accepts-seq-forms
  (let [list-constraint (list `= 'this "abc")
        cons-constraint (cons `= ['this "abc"])
        qlist {:lhs [{:fact-binding :?s
                      :type String
                      :constraints [list-constraint]}]
               :params #{}}
        qcons {:lhs [{:fact-binding :?s
                      :type String
                      :constraints [cons-constraint]}]
               :params #{}}

        ;; Do not allow the session caching since both rules above are
        ;; equivalent from a clj perspective.
        qlist-result (-> (mk-session [qlist] :cache false)
                         (insert "abc")
                         fire-rules
                         (query qlist)
                         set)
        qcons-result (-> (mk-session [qcons] :cache false)
                         (insert "abc")
                         fire-rules
                         (query qlist)
                         set)]
    (is (= #{{:?s "abc"}}
           qlist-result
           qcons-result))))

(deftest test-invalid-binding
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"line.*123.*column.*456"
       (dsl/parse-query*
        []
        [[:?b '<- [:or [String] [Integer]]]]
        {}
        {:line 123 :column 456}))))

(deftest test-throw-rhs

  (let [unnamed-rule (dsl/parse-rule [[Temperature (= ?x temperature)]]
                                     (throw (ex-info "Test exception" {})))

        named-rule (assoc unnamed-rule :name "test-rule-name")]

    (try
      (-> (mk-session [unnamed-rule])
          (insert (->Temperature 10 "MCI"))
          (fire-rules))
      (catch Exception e
        (is (= {:?x 10} (:bindings (ex-data e))))))

    (try
      (-> (mk-session [named-rule])
          (insert (->Temperature 10 "MCI"))
          (fire-rules))
      (catch Exception e

        (is (re-find #"test-rule-name" (.getMessage e)))
        (is (= {:?x 10} (:bindings (ex-data e))))
        (is (= "test-rule-name" (:name (ex-data e))))))))

(deftest test-retrieve-listeners-from-failed-rhs
  (let [r1 (dsl/parse-rule [[First]]
                           (insert! (->Second)))

        r2 (dsl/parse-rule [[Second]]
                           (throw (ex-info "Test exception" {})))

        run-session-traced (fn []
                             (-> (mk-session [r1 r2])
                                 (t/with-tracing)
                                 (insert (->First))
                                 (fire-rules)))

        run-session-untraced (fn []
                               (-> (mk-session [r1 r2])
                                   (insert (->First))
                                   (fire-rules)))

        listeners-from-trace (fn [e] (mapcat :listeners
                                             (tu/get-all-ex-data e)))]
    (try
      (run-session-traced)
      (is false "Running the rules in this test should cause an exception.")
      (catch Exception e
        (let [listeners (listeners-from-trace e)]
          (is (some (partial instance? PersistentTracingListener) listeners)
              "The listeners should be in the ex-data when a RHS throws an exception."))))
    (try
      (run-session-untraced)
      (is false "Running the rules in this test should cause an exception.")
      (catch Exception e
        (let [listeners (listeners-from-trace e)]
          (is (empty? listeners)
              "When there is only the null listener there should be no listeners in the ex-data"))))))

(deftest test-non-list-seq-form-used-for-non-eq-unification
  (let [non-list-constraint (cons '= '(this (identity ?t)))
        ;; Sanity check in case Clojure impl details change.
        _ (is (not (list? non-list-constraint))
              (str "Ensure test is using non-list seq to expose"
                   " any `list?` impl specific compiler issues"))
        q {:lhs [{:type clara.rules.testfacts.Temperature
                  :constraints []
                  :fact-binding :?t}
                 {:type clara.rules.testfacts.Temperature
                  :constraints [non-list-constraint]}]
           :params #{}}
        temp (->Temperature 1 "MCI")
        res (-> (mk-session [q] :cache false)
                (insert temp)
                fire-rules
                (query q)
                first)]
    (is (= {:?t temp}
           res))))

(deftest test-duplicate-rules
  (let [r (dsl/parse-rule [[Temperature (= ?t temperature)]]
                          (insert! (->Cold ?t)))
        q (dsl/parse-query []
                           [[?c <- Cold]])

        q-res (fn [s]
                (-> s
                    (insert (->Temperature 10 "MCI"))
                    fire-rules
                    (query q)))

        s1 (mk-session [r q])
        s2 (mk-session [r r q])
        s3 (mk-session [r] [r q])]
    (is (= (q-res s1)
           (q-res s2)
           (q-res s3)
           [{:?c (->Cold 10)}])
        (str "Duplicate rules should not cause duplicate RHS activations." \newline
             "s1 res: " (vec (q-res s1)) \newline
             "s2 res: " (vec (q-res s2)) \newline
             "s3 res: " (vec (q-res s2)) \newline))))

(deftest test-equivalent-rule-sources-caching
  (is (instance? clojure.lang.IAtom @#'com/session-cache)
      "Enforce that this test is revisited if the cache structure (an implementation detail) is changed.
       This test should have a clean cache but should also not impact the global cache, which
       requires resetting the cache for the duration of this test.")

  (let [original-cache (-> #'com/session-cache deref deref)
        _ (reset! @#'com/session-cache {})
        s1 (mk-session [test-rule] :cache false)
        s2 (mk-session [test-rule])
        s3 (mk-session [test-rule test-rule])
        s4 (mk-session [test-rule] [test-rule])

        ;; Since functions use reference equality create a single function instance
        ;; to test reuse when options are the same.
        alternate-alpha-fn (constantly Object)
        s5 (mk-session [test-rule] :fact-type-fn alternate-alpha-fn :cache false)
        s6 (mk-session [test-rule] :fact-type-fn alternate-alpha-fn)
        s7 (mk-session [test-rule test-rule] :fact-type-fn alternate-alpha-fn)
        s8 (mk-session [test-rule cold-query] :fact-type-fn alternate-alpha-fn)

        ;; Find all distinct references, with distinctness determined by reference equality.
        ;; If the reference to a session is identical to a previous session we infer that
        ;; the session was the result of a cache hit; if the reference is not identical to
        ;; a previous session it is the result of a cache miss.
        distinct-sessions (reduce (fn [existing new]
                                    (if-not (some (partial identical? new)
                                                  existing)
                                      (conj existing new)
                                      existing))
                                  []
                                  [s1 s2 s3 s4 s5 s6 s7 s8])]
    (is (= distinct-sessions
           [s1 s2 s5 s6 s8]))
  (reset! @#'com/session-cache original-cache)))

#_{:clj-kondo/ignore [:unresolved-symbol]}
(deftest test-try-eval-failures-includes-compile-ctx
  (let [q1 (dsl/parse-query [] [[:not [Temperature (= ?t temperature)]]])
        q2 (dsl/parse-query [] [[First (= ?b bogus)]])]

    (assert-ex-data {:production q1}
                    (mk-session [q1]))

    (assert-ex-data {:condition (-> q2 :lhs first)}
                    (mk-session [q2]))))

(deftest test-complex-nested-truth-maintenance-with-unconditional-insert
  (let [r (dsl/parse-rule [[Cold (= ?t temperature)]
                           [:not [:or [ColdAndWindy (= ?t temperature)]
                                  [Hot (= ?t temperature)]]]]
                          (insert-unconditional! (->First)))

        q (dsl/parse-query [] [[First]])

        session->results (fn [session] (-> session
                                           (insert (->Cold 10) (->Hot 10))
                                           (fire-rules)
                                           (query q)))]

    (is (= (session->results (mk-session [r q]))
           ;; Validate that equal salience is handled correctly by
           ;; the activation-group-sort-fn when the user provides
           ;; a function with a numerical return value.
           (session->results (mk-session [r q] :activation-group-sort-fn
                                         (fn [x y]
                                           (cond
                                             (= x y) 0
                                             (> x y) -1
                                             :else 1))))
           []))))


(def some-rules [(assoc (dsl/parse-query [] [[Temperature (< temperature 40) (= ?t temperature) (= ?l location)]])
                        :name "cold")
                 (assoc (dsl/parse-query [] [[Temperature (> temperature 80) (= ?t temperature) (= ?l location)]])
                        :name "hot")])

(deftest load-rules-from-qualified-symbol
  ;; Test getting a production by symbol
  (let [session (-> (mk-session 'clara.test-rules/cold-query)
                    (insert (->Temperature 35 "BOS"))
                    (fire-rules))]

    ;; Query by location.
    (is (= #{{:?l "BOS" :?t 35}}
           (set (query session cold-query :?l "BOS")))))

  ;; Test getting a sequence of rules by symbol.
  (let [session (-> (mk-session 'clara.test-rules/some-rules)
                    (insert (->Temperature 35 "BOS"))
                    (insert (->Temperature 85 "MIA"))
                    (fire-rules))]

    ;; Query by location.
    (is (= #{{:?l "BOS" :?t 35}}
           (set (query session "cold"))))

    (is (= #{{:?l "MIA" :?t 85}}
           (set (query session "hot")))))

  ;; Test bogus symbol
  (is (thrown? clojure.lang.ExceptionInfo
       (mk-session 'clara.test-rules/bogus-symbol))))

(defprotocol Getter
  (getX [this])
  (getY [this]))

(deftype TestBean [x y]
  Getter
  (getX [_] x)
  (getY [_]
    (throw (ex-info "getY isn't used and shouldn't be accessed by the rules" {}))))

(deftest test-only-used-field-names-accessed
  (let [alpha (dsl/parse-query [] [[TestBean (= ?x x)]])
        join-filter (dsl/parse-query [] [[Temperature (= ?t temperature)]
                                         [TestBean (= ?t x)]])
        s (-> (mk-session [alpha join-filter])
              (insert (->TestBean 1 2)
                      (->Temperature 1 "MCI"))
              fire-rules)]
    (is (= #{{:?x 1}} (set (query s alpha))))
    (is (= #{{:?t 1}} (set (query s join-filter))))))

(deftest test-flush-all-updates-before-changing-activation-group
  (let [results (atom [])
        r1 (dsl/parse-rule [[:not [Temperature (= temperature 100)]]]
                           (insert! (->Cold 1))
                           {:salience 1})

        r2 (dsl/parse-rule [[Cold (= ?t temperature)]]
                           (insert! (->Temperature ?t "MCI"))
                           {:salience 1})

        r3 (dsl/parse-rule [[Hot (= ?t temperature)]]
                           (insert! (->Temperature ?t "MCI")))

        r4 (dsl/parse-rule [[?ts <- (acc/all :temperature) :from [Temperature]]]
                           (do (swap! results conj ?ts)
                               (insert! (->TemperatureHistory ?ts)))
                           {:salience -1})

        q (dsl/parse-query []
                           [[TemperatureHistory (= ?ts temperatures)]])

        s (-> (mk-session [r1 r2 r3 r4 q])
              (insert (->Hot 100))
              fire-rules)]

    (is (= #{{:?ts [100]}}
           (set (query s q))))
    (is (= [[100]]
           @results))))

(definterface Marker)
(defrecord Type1 [] Marker)
(defrecord Type2 [] Marker)

(deftest test-retract-diff-types-equal-fields-common-ancestor-type
  (let [q (dsl/parse-query []
                           [[?m <- Marker]])
        init-state (-> (mk-session [q])
                       (insert (->Type1)
                               (->Type2))
                       fire-rules)
        retract1 (-> init-state
                     (retract (->Type1))
                     fire-rules)
        retract2 (-> retract1
                     (retract (->Type1))
                     fire-rules)]

    (is (= (frequencies [{:?m (->Type1)}
                         {:?m (->Type2)}])
           (frequencies (query init-state q))))

    ;; Retracted two objects that are different classes, but with
    ;; a common ancestor class do not clash with one another.  Only
    ;; facts with the same class will be retracted.
    ;; This distinction is important in cases like Clojure's record
    ;; types.  When using java.lang.Object.equals() on Clojure records
    ;; they do not take into account the type of the the record.
    ;; Records act as generic java.util.Map's in this sense.
    ;; When Clojure records are compared with clojure.core/= however,
    ;; the type of the records must be equal as well.  Since we are using
    ;; Java collection types in our retraction workflow of the JVM transient
    ;; working memory right now, it is important that we don't fall prey to
    ;; this subtle difference with Java equals vs Clojure equals on records.
    (is (= (frequencies [{:?m (->Type2)}])
           (frequencies (query retract1 q))
           (frequencies (query retract2 q))))))

(deftest test-rule-order-respected
  (let [fire-order (atom [])
        rule-A (dsl/parse-rule [[Cold]]
                               (swap! fire-order conj :A))
        rule-B (dsl/parse-rule [[Cold]]
                               (swap! fire-order conj :B))]

    (reset! fire-order [])

    (-> (mk-session [rule-A rule-B] :cache false)
        (insert (->Cold 10))
        fire-rules)
    (is (= @fire-order [:A :B])
        "Rule order in a seq of rule structures should be respected")

    (reset! fire-order [])

    (-> (mk-session [rule-B rule-A] :cache false)
        (insert (->Cold 10))
        fire-rules)
    (is (= @fire-order [:B :A])
        "Validate that when we reverse the seq of rule structures the firing order is reversed.")

    (reset! fire-order [])

    (binding [order-rules/*rule-order-atom* fire-order]
      (-> (mk-session [rule-A] 'clara.order-ruleset :cache false)
          (insert (->Cold 10))
          fire-rules)
      (is (= @fire-order [:A :C :D])
          "Rules should fire in the order they appear in a namespace.  A rule that is before that namespace
           in the rule sources should fire first."))

    (reset! fire-order [])

    (binding [order-rules/*rule-order-atom* fire-order]
      (-> (mk-session 'clara.order-ruleset [rule-A] :cache false)
          (insert (->Cold 10))
          fire-rules)
      (is (= @fire-order [:C :D :A])
          "Rules should fire in the order they appear in a namespace.  A rule that is after that namespace
           in the rule sources should fire later."))

    (reset! fire-order [])

    (let [rule-C-line (-> #'order-rules/rule-C meta :line)
          rule-D-line (-> #'order-rules/rule-D meta :line)]
      (alter-meta! #'order-rules/rule-C (fn [m] (assoc m :line rule-D-line)))
      (alter-meta! #'order-rules/rule-D (fn [m] (assoc m :line rule-C-line)))

      (binding [order-rules/*rule-order-atom* fire-order]
        (-> (mk-session 'clara.order-ruleset :cache false)
            (insert (->Cold 10))
            fire-rules))

      (is (= @fire-order [:D :C])
          "When we alter the metadata of the rules to reverse their line order their
           firing order should also be reversed.")

      ;; Reset the line metadata on the rules to what it was previously.
      (alter-meta! #'order-rules/rule-C (fn [m] (assoc m :line rule-C-line)))
      (alter-meta! #'order-rules/rule-D (fn [m] (assoc m :line rule-D-line))))

    (reset! fire-order [])

    (binding [order-rules/*rule-order-atom* fire-order
              order-rules/*rule-seq-prior* [rule-A rule-B]]
      (-> (mk-session 'clara.order-ruleset :cache false)
          (insert (->Cold 10))
          fire-rules)
      (is (= @fire-order [:A :B :C :D])
          "When a :production-seq occurs before defrules, the rules in the :production-seq
           should fire before those rules and in the order they are in in the :production-seq."))

    (reset! fire-order [])

    (binding [order-rules/*rule-order-atom* fire-order
              order-rules/*rule-seq-after* [rule-A rule-B]]
      (-> (mk-session 'clara.order-ruleset :cache false)
          (insert (->Cold 10))
          fire-rules)
      (is (= @fire-order [:C :D :A :B])
          "When a :production-seq occurs after defrules, the rules in the :production-seq
           should fire after those rules and in the order they are in in the :production-seq."))

    (reset! fire-order [])

    (binding [order-rules/*rule-order-atom* fire-order
              order-rules/*rule-seq-after* [rule-B rule-A]]
      (-> (mk-session 'clara.order-ruleset :cache false)
          (insert (->Cold 10))
          fire-rules)
      (is (= @fire-order [:C :D :B :A])
          "Validate that when the order of rules in the :production-seq is reversed those rules
           fire in the reversed order"))

    (reset! fire-order [])

    (-> (mk-session [rule-A (assoc-in rule-B [:props :salience] 1)] :cache false)
        (insert (->Cold 10))
        fire-rules)
    (is (= @fire-order [:B :A])
        "Validate that when explicit salience is present it overrides rule order.")

    (reset! fire-order [])

    (-> (mk-session [rule-A rule-B rule-A] :cache false)
        (insert (->Cold 10))
        fire-rules)
    (is (= @fire-order [:A :B])
        "Validate that the first occurence of a rule is used for rule ordering when it occurs multiple times.")

    (reset! fire-order [])))

(deftest test-rule-order-respected-by-batched-inserts
  (let [qholder (atom [])

        r1 (dsl/parse-rule [[Temperature (= ?t temperature)]]
                           (insert! (->Cold ?t)))
        r2 (dsl/parse-rule [[Temperature (= ?t temperature)]]
                           (insert! (->Hot ?t)))

        ;; Make two "alpha roots" that the 2 rules above insertions will need to propagate to.
        q1 (dsl/parse-query [] [[?c <- Cold  (swap! qholder conj :cold)]])
        q2 (dsl/parse-query [] [[?h <- Hot (swap! qholder conj :hot)]])

        order1 (mk-session [r1 r2 q1 q2] :cache false)
        order2 (mk-session [r2 r1 q1 q2] :cache false)

        run-session (fn [s]
                      (let [s (-> s
                                  (insert (->Temperature 10 "MCI"))
                                  fire-rules)]
                        [(-> s (query q1) frequencies)
                         (-> s (query q2) frequencies)]))

        [res11 res12] (run-session order1)
        holder1 @qholder
        _ (reset! qholder [])

        [res21 res22] (run-session order2)
        holder2 @qholder
        _ (reset! qholder [])]

    ;; Sanity check that the query matches what is expected.
    (is (= (frequencies [{:?c (->Cold 10)}])
           res11
           res21))
    (is (= (frequencies [{:?h (->Hot 10)}])
           res12
           res22))

    (is (= [:cold :hot] holder1))
    (is (= [:hot :cold] holder2))))

;; TODO: Move this to test-dsl once a strategy for replicating assert-ex-data is determined and implemented.
#_{:clj-kondo/ignore [:unresolved-symbol]}
(deftest test-reused-var-in-constraints
  (let [q (dsl/parse-query [] [[Temperature (= ?t (+ 5 temperature)) (< ?t 10)]])

        ;; Test that a value must be bound before use.
        invalid (dsl/parse-query [] [[Temperature (< ?t 10) (= ?t (+ 5 temperature))]] )

        s (mk-session [q] :cache false)]

    ;; Item that does not satisfy the second criterion should produce no results.
    (is (empty?
         (-> s
             (insert (->Temperature 20 "MCI"))
             (fire-rules)
             (query q))))

    ;; Item that does satisfy second criterion should match.
    (is (= [{:?t 5}]
         (-> s
             (insert (->Temperature 0 "MCI"))
             (fire-rules)
             (query q))))

    ;; The variable used out of order should be marked as unbound.
    (assert-ex-data {:variables #{'?t}}
                    (mk-session [invalid] :cache false))))

(deftest test-extra-right-activations-with-disjunction-of-negations
  (let [no-join (dsl/parse-rule [[:or
                                  [:not [Cold]]
                                  [:not [Hot]]]]
                                (insert! (->LousyWeather)))

        complex-join (dsl/parse-rule [[Temperature (= ?temp temperature)]
                                      [:or
                                       [:not [Cold (> temperature ?temp)]]
                                       [:not [Hot (> temperature ?temp)]]]]
                                     (insert! (->LousyWeather)))

        q  (dsl/parse-query [] [[LousyWeather]])]

    (doseq [[empty-session join-type] [[(mk-session [no-join q] :cache false) "simple hash join"]
                                       [(mk-session [complex-join q] :cache false) "complex join"]]]

      (is (= (-> empty-session
                 (insert (->Hot 100) (->Temperature -100 "ORD"))
                 fire-rules
                 (insert (->Hot 120))
                 fire-rules
                 (query q))
             [{}])
          (str "As long as one negation condition in the :or matches, regardless of how many facts match the other "
               "negation the rule should fire for join type " join-type)))))

(deftest test-unresolvable-symbols-in-metadata-on-conditions
  ;; Test removal of unwanted metadata; see PR 243 for details
  (let [rule-output (atom nil)
        ns-nom (ns-name *ns*)
        rule {:ns-name ns-nom
              :name (str ns-nom "/unresolvable-metadata-rule")
              :lhs [(with-meta {:type Temperature
                                :constraints [(list `< 'temperature 20)]}
                      {:custom-meta 'unresolvable-symbol})]
              :rhs `(do (reset! ~'rule-output ~'?__token__))
              :env {:rule-output rule-output}}

        session (-> (mk-session [rule])
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

    (is (has-fact? @rule-output (->Temperature 10 "MCI")))))

(deftest test-alpha-batching-with-multiple-ancestors
  ;; Validate that two distinct fact types are batched together when passed to a condition on a
  ;; common ancestor type. We use an accumulator because it provides a convenient way to directly
  ;; access the facts passed to the condition without exposing Clara internals.
  ;; see issue 257 for more details of the bug surrounding this test
  (let [accum-state (atom [])

        stateful-accum (acc/accum
                         {:initial-value []
                          :reduce-fn conj
                          :retract-fn (fn [items retracted] (remove #{retracted} items))
                          :convert-return-fn (fn [items]
                                               (do
                                                 (swap! accum-state conj items)
                                                 items))})

        common-ancestor-rule (dsl/parse-rule [[?lists <- stateful-accum :from [List]]]
                                             ;; don't care about whats inserted
                                             (->LousyWeather))

        array-list (ArrayList.)
        linked-list (LinkedList.)

        ses (-> (mk-session [common-ancestor-rule])
              (insert-all [array-list linked-list])
              (fire-rules))]

    (is (not-any? #(= 1 (count %)) @accum-state)
        "Facts with common ancestors should be batched together, expected either the initial accumulator value or a vector containing both lists but never a vector containing one list.")))

(deftest test-single-condition-queries-constraint-exception
  (let [query-template (dsl/parse-query [] [[Temperature
                                             (= ?location location)
                                             (> temperature 0)]])
        temperature-query1 (assoc query-template :name "temperature-query1")
        temperature-query2 (assoc query-template :name "temperature-query2")
        temperature-fact (->Temperature nil "MCI")]

    (assert-ex-data {:bindings nil
                     :fact temperature-fact
                     :conditions-and-rules
                     {[clara.rules.testfacts.Temperature '(= ?location location) '(> temperature 0)]
                      (sorted-set [:query  "temperature-query1"] [:query "temperature-query2"])}}
                    (-> (mk-session [temperature-query1 temperature-query2] :cache false)
                        (insert temperature-fact)
                        (fire-rules)
                        (query temperature-query1)))))

;; See https://github.com/cerner/clara-rules/issues/379 for more info
(deftest test-single-condition-multiple-rule-constraint-exception
  (let [rule-one (dsl/parse-rule [[WindSpeed
                                   (= ?location location)]
                                  [Temperature
                                   (> temperature 0)]]
                                 (println ?location))
        rule-two (dsl/parse-rule [[Cold
                                   (> 21 temperature)]
                                  [Temperature
                                   (> temperature 0)]]
                                 (println "ok"))
        temperature-rule1 (assoc rule-one :name "rule-1")
        temperature-rule2 (assoc rule-two :name "rule-2")
        temperature-fact (->Temperature nil "MCI")]

    (assert-ex-data {:bindings nil
                     :fact temperature-fact
                     :conditions-and-rules
                     {[clara.rules.testfacts.Temperature '(> temperature 0)]
                      (sorted-set [:production  "rule-1"] [:production "rule-2"])}}
                    (-> (mk-session [temperature-rule1 temperature-rule2] :cache false)
                        (insert temperature-fact)
                        (fire-rules)))))

(deftest test-single-condition-rules-constraint-exception
  (let [rule-template (dsl/parse-rule [[Temperature
                                        (= ?location location)
                                        (> temperature 0)]]
                                      (println "Ok"))
        temperature-rule1 (assoc rule-template :name "temperature-rule1")
        temperature-rule2 (assoc rule-template :name "temperature-rule2")
        temperature-fact (->Temperature nil "MCI")]

    (assert-ex-data {:bindings nil
                     :fact temperature-fact
                     :conditions-and-rules
                     {[clara.rules.testfacts.Temperature '(= ?location location) '(> temperature 0)]
                      (sorted-set [:production  "temperature-rule1"] [:production "temperature-rule2"])}}
                    (-> (mk-session [temperature-rule1 temperature-rule2] :cache false)
                        (insert temperature-fact)
                        (fire-rules)))))

(deftest test-single-condition-negation-rules-constraint-exception
  (let [rule-template (dsl/parse-rule [[:not [Temperature (> temperature 0)]]]
                                      (println "Ok"))
        temperature-rule (assoc rule-template :name "temperature-rule")
        temperature-fact (->Temperature nil "MCI")]
    (assert-ex-data {:bindings nil
                     :fact temperature-fact
                     :conditions-and-rules
                     {[:not [clara.rules.testfacts.Temperature '(> temperature 0)]]
                      (sorted-set [:production  "temperature-rule"])}}
                    (-> (mk-session [temperature-rule] :cache false)
                        (insert temperature-fact)
                        (fire-rules)))))

(deftest test-single-condition-query-and-rule-constraint-exception
  (let [query-template (dsl/parse-query [] [[Temperature
                                             (= ?location location)
                                             (> temperature 0)]])
        temperature-query (assoc query-template :name "temperature-query")
        rule-template (dsl/parse-rule [[Temperature
                                        (= ?location location)
                                        (> temperature 0)]]
                                      (println "Ok"))
        temperature-rule (assoc rule-template :name "temperature-rule")
        temperature-fact (->Temperature nil "MCI")]
    (assert-ex-data {:bindings nil
                     :fact temperature-fact
                     :conditions-and-rules
                     {[clara.rules.testfacts.Temperature '(= ?location location) '(> temperature 0)]
                      (sorted-set [:query  "temperature-query"] [:production  "temperature-rule"])}}
                    (-> (mk-session [temperature-query temperature-rule] :cache false)
                        (insert temperature-fact)
                        (fire-rules)
                        (query temperature-query)))))

(deftest test-expression-join-query-constraint-exception-from-bindings
  (let [query-template (dsl/parse-query [] [[Temperature
                                             (= ?location location)
                                             (= ?temperature temperature)]
                                            [WindSpeed
                                             (= ?location location)
                                             (> ?temperature windspeed)]])
        temperature-query (assoc query-template :name "temperature-query")
        temperature-fact (->Temperature nil "MCI")
        windspeed-fact (->WindSpeed 30 "MCI")]
    (assert-ex-data {:bindings {:?location "MCI", :?temperature nil}
                     :fact windspeed-fact
                     :conditions-and-rules
                     {[clara.rules.testfacts.WindSpeed '(= ?location location) '(> ?temperature windspeed)]
                      (sorted-set [:query  "temperature-query"])}}
                    (-> (mk-session [temperature-query] :cache false)
                        (insert temperature-fact)
                        (insert windspeed-fact)
                        (fire-rules)
                        (query temperature-query)))))

(deftest test-expression-join-query-constraint-exception-from-fact
  (let [query-template (dsl/parse-query [] [[Temperature
                                             (= ?location location)
                                             (= ?temperature temperature)]
                                            [WindSpeed
                                             (= ?location location)
                                             (> ?temperature windspeed)]])
        temperature-query (assoc query-template :name "temperature-query")
        temperature-fact (->Temperature 90 "MCI")
        windspeed-fact (->WindSpeed nil "MCI")]
    (assert-ex-data {:bindings {:?location "MCI", :?temperature 90}
                     :fact windspeed-fact
                     :conditions-and-rules
                     {[clara.rules.testfacts.WindSpeed '(= ?location location) '(> ?temperature windspeed)]
                      (sorted-set [:query  "temperature-query"])}}
                    (-> (mk-session [temperature-query] :cache false)
                        (insert temperature-fact)
                        (insert windspeed-fact)
                        (fire-rules)
                        (query temperature-query)))))

(deftest test-single-condition-accum-constraint-exception
  (let [query-template (dsl/parse-query [] [[?wind <- (acc/all) :from [Temperature (> temperature 0)]]])
        temperature-query (assoc query-template :name "temperature-query")
        temperature-fact (->Temperature nil "MCI")]
    (assert-ex-data {:bindings nil
                     :fact temperature-fact
                     :conditions-and-rules
                     {['?wind '<- '(clara.rules.accumulators/all) :from [clara.rules.testfacts.Temperature '(> temperature 0)]]
                      (sorted-set [:query "temperature-query"])}}
                    (-> (mk-session [temperature-query] :cache false)
                        (insert temperature-fact)
                        (fire-rules)
                        (query temperature-query)))))

(deftest test-stored-insertion-retraction-ordering

  (let [r (dsl/parse-rule [[:exists [Cold]]]
                          (insert! (->LousyWeather)))

        lousy-weather-query (dsl/parse-query [] [[LousyWeather]])

        cold-query (dsl/parse-query [] [[Cold (= ?t temperature)]])

        empty-session (mk-session [r lousy-weather-query cold-query] :cache false)

        single-ops-retract-first (-> empty-session
                                     (retract (->Cold 0))
                                     (insert (->Cold 0))
                                     fire-rules)

        single-ops-insert-first (-> empty-session
                                    (insert (->Cold 0))
                                    (retract (->Cold 0))
                                    fire-rules)

        single-ops-retract-fire-insertion (-> empty-session
                                              (retract (->Cold 0))
                                              fire-rules
                                              (insert (->Cold 0)))

        two-cold-one-retracted-first (-> empty-session
                                         (insert (->Cold -10))
                                         (retract (->Cold 10))
                                         (insert (->Cold 10))
                                         (retract (->Cold -10))
                                         fire-rules)

        ops-cleared-across-fire-rules (-> empty-session
                                          (insert (->Cold -10))
                                          (retract (->Cold 10))
                                          fire-rules
                                          (insert (->Cold 10))
                                          (retract (->Cold -10))
                                          fire-rules)]

    (testing "Single insertion and retraction of Cold, with the retraction first"

      (is (= (query single-ops-retract-first lousy-weather-query)
             [{}]))

      (is (= (query single-ops-retract-first cold-query)
             [{:?t 0}])))

    (testing "Single insertion and retraction of Cold, with the insertion first"

      (is (empty? (query single-ops-insert-first lousy-weather-query)))
      (is (empty? (query single-ops-insert-first cold-query))))

    (testing "Two distinct Cold facts inserted and retracted, with the insertion first in one case and the retraction in the other"

      (is (= (query two-cold-one-retracted-first lousy-weather-query)
             [{}]))
      (is (= (query two-cold-one-retracted-first cold-query)
             [{:?t 10}])))

    (testing (str "Two distinct Cold facts inserted and retracted, with the insertion first in one case and last in the other." \newline
                  "A fire-rules call is between the insertion and retraction for each case to validate that calling fire-rules clear the cache")

      (is (= (query ops-cleared-across-fire-rules lousy-weather-query)
             [{}]))
      (is (= (query ops-cleared-across-fire-rules cold-query)
             [{:?t 10}])))))

(deftest test-cancelling-facts
  (binding [*side-effect-holder* (atom false)]
    (let [cold-rule (dsl/parse-rule [[ColdAndWindy (= ?t temperature) (< ?t 100)]]
                                    (insert! (->Cold ?t)))

          lousy-weather-rule (dsl/parse-rule [[Cold]]
                                             (do
                                               (reset! *side-effect-holder* true)
                                               (insert! (->LousyWeather))))

          cold-windy-query (dsl/parse-query [] [[ColdAndWindy (= ?t temperature) (= ?w windspeed)]])

          cold-query (dsl/parse-query [] [[Cold (= ?t temperature)]])

          lousy-weather-query (dsl/parse-query [] [[LousyWeather]])

          empty-session (mk-session [cold-rule cold-query lousy-weather-rule
                                     lousy-weather-query cold-windy-query] :cache false)

          with-cold-session (-> empty-session
                                (insert (->ColdAndWindy -10 20))
                                fire-rules)

          first-cold-rhs-fired? @*side-effect-holder*

          _ (reset! *side-effect-holder* false)

          updated-cold-session (-> with-cold-session
                                   (insert (->ColdAndWindy -10 30))
                                   (retract (->ColdAndWindy -10 20))
                                   (fire-rules {:cancelling true}))

          after-update-cold-rhs-fired? @*side-effect-holder*

          cold-removed-session (-> with-cold-session
                                   (insert (->ColdAndWindy 200 20))
                                   (retract (->ColdAndWindy -10 20))
                                   (fire-rules {:cancelling true}))]

      (is (= (query with-cold-session cold-query)
             [{:?t -10}])
          "Sanity check that the Cold fact was inserted")

      (is (= (query with-cold-session lousy-weather-query)
             [{}])
          "Sanity check that the LousyWeather fact was inserted")

      (is (= (query with-cold-session cold-windy-query)
             [{:?t -10 :?w 20}])
          "Sanity check that the ColdAndWindy fact was inserted")

      (is (true? first-cold-rhs-fired?)
          "Sanity check of the RHS atom")

      ;;; Tests with the ColdAndWindy fact updated that will not impact the Cold fact.

      (is (= (query updated-cold-session cold-query)
             [{:?t -10}])
          (str "Test that we still have the same Cold fact value after an update that should not impact "
               "it but is a direct consequence of the updated fact."))

      (is (= (query updated-cold-session cold-windy-query)
             [{:?t -10 :?w 30}])
          "Validate that the ColdAndWindy fact was updated")

      (is (= (query with-cold-session lousy-weather-query)
             [{}])
          "Sanity check that the LousyWeather fact is still present after the update.")

      (is (false? after-update-cold-rhs-fired?)
          "Check that the RHS of the rule matching on RHS was not fired.")

      ;;; Tests with the ColdAndWindy fact updated in a way that should cause the removal
      ;;; of the ColdAndWindy fact.

      (is (= (query cold-removed-session cold-windy-query)
             [{:?t 200 :?w 20}])
          "Check that the invalid ColdAndWindy fact was inserted.")

      (is (empty? (query cold-removed-session cold-query))
          "Validate that the Cold was removed.")

      (is (empty? (query cold-removed-session lousy-weather-query))
          "Validate that the LousyWeather was removed"))))

(deftest test-fire-rules-direct-one-arity-interop-call
  ;; This tests that, even after changing fire-rules to take a second argument in issue 249
  ;; we can still call the fire-rules method on the session with one argument.  Note that was
  ;; done for passivity even though this method is an implementation detail and could still
  ;; change or be removed in the future.
  (let [cold-query (dsl/parse-query [] [[Cold (= ?t temperature)]])]

    (is (= (-> (mk-session [cold-query] :cache false)
               ^ISession (insert (->Cold -10))
               .fire_rules
               (query cold-query))
           [{:?t -10}]))))

(deftest test-insert-retract-same-fact-before-firing-rules-with-cancelling
  (let [cold-query (dsl/parse-query [] [[Cold (= ?t temperature)]])]

    (is (empty? (-> (mk-session [cold-query] :cache false)
                    (retract (->Cold -10))
                    (insert (->Cold -10))
                    (fire-rules {:cancelling true})
                    (query cold-query))))))

;; Partial test for https://github.com/cerner/clara-rules/issues/267
;; This test has a counterpart of the same name in clara.test-bindings.  Once
;; we land on a strategy for error checking tests in ClojureScript we can move this
;; test case there.
(deftest test-local-scope-visible-in-join-filter
  (let [check-exception (dsl/parse-query [] [[WindSpeed (= ?w windspeed)]
                                             [Temperature (= ?t temperature)
                                              (> ?t ?w)]])]

    (let [e (try
              (-> (mk-session [check-exception])
                  (insert (->WindSpeed 10 "MCI") (->Temperature nil "MCI"))
                  (fire-rules)
                  (query check-exception))
              (is false "Scope binding test is expected to throw an exception.")
              (catch Exception e e))]
      (is (= {:?w 10, :?t nil}
             (-> e (ex-data) :bindings))))))

(deftest test-include-details-when-exception-is-thrown-in-test-filter
  (testing "when a condition exception is thrown ensure it contains the necessary details and text"
    (let [check-exception (assoc (dsl/parse-query [] [[WindSpeed (= ?w windspeed)]
                                                      [Temperature (= ?t temperature)]
                                                      [:test (> ?t ?w)]])
                                 :name "my-test-query")]

      (assert-ex-data "Condition exception raised.\nwith no fact\nwith bindings\n  {:?w 10, :?t nil}\nConditions:\n\n1. [:test (> ?t ?w)]\n   queries:\n     my-test-query\n"
                      {:bindings {:?w 10, :?t nil}
                       :fact nil
                       :env nil
                       :conditions-and-rules {[:test '(> ?t ?w)] #{[:query "my-test-query"]}}}
                      (-> (mk-session [check-exception])
                          (insert (->WindSpeed 10 "MCI") (->Temperature nil "MCI"))
                          (fire-rules)
                          (query check-exception))))))

;;; Test that we can properly assemble a session, insert facts, fire rules,
;;; and run a query with keyword-named productions.
(deftest test-simple-insert-data-with-keyword-names
  (let [session (-> (mk-session (rules-data/weather-rules-with-keyword-names))
                    (insert (->Temperature 15 "MCI"))
                    (insert (->WindSpeed 45 "MCI"))
                    (fire-rules))]
    (is (= [{:?fact (->ColdAndWindy 15 45)}]
           (query session ::rules-data/find-cold-and-windy-data)))))

;;; Verify that an exception is thrown when a duplicate name is encountered.
;;; Note we create the session with com/mk-session*, as com/mk-session allows
;;; duplicate names and will take what it considers to be the most recent
;;; definition of a production.
(deftest test-duplicate-name
  (assert-ex-data {:names #{::rules-data/is-cold-and-windy-data}}
                  (com/mk-session*
                    (set (com/add-production-load-order (conj (rules-data/weather-rules-with-keyword-names)
                                                              {:doc  "An extra rule to test for duplicate names."
                                                               :name :clara.rules.test-rules-data/is-cold-and-windy-data
                                                               :lhs  []
                                                               :rhs  '(println "I have no meaning outside of this test")}))) {})))

(deftest test-negation-multiple-children-exception
  (let [not-rule (dsl/parse-rule [[:not
                                   [Hot (= ?t temperature)]
                                   [Temperature (> temperature 0)]]]
                                 (insert! (->LousyWeather)))]
    (assert-ex-data
     {:illegal-negation [:not {:type clara.rules.testfacts.Hot
                               :constraints ['(= ?t temperature)]}
                         {:type clara.rules.testfacts.Temperature
                          :constraints ['(> temperature 0)]}]}
     (mk-session [not-rule] :cache false))))
