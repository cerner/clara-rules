(ns clara.test-rules
  (:use clojure.test
        clara.rules
        [clara.rules.engine :only [->Token ast-to-dnf load-rules *trace-transport* 
                                   description print-memory]]
        clara.rules.testfacts)
  (:require [clara.sample-ruleset :as sample]
            [clara.other-ruleset :as other]
            [clojure.set :as s])
  (import [clara.rules.testfacts Temperature WindSpeed Cold ColdAndWindy LousyWeather First Second Third Fourth]
          [java.util TimeZone]))

(deftest test-simple-rule
  (let [rule-output (atom nil)
        cold-rule (mk-rule [[Temperature (< temperature 20)]] 
                            (reset! rule-output ?__token__) )

        session (-> (mk-rulebase cold-rule)
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

    (is (= 
         (->Token [(->Temperature 10 "MCI")] {})
         @rule-output))))

(deftest test-multiple-condition-rule
  (let [rule-output (atom nil)
        cold-windy-rule (mk-rule [(Temperature (< temperature 20))
                                   (WindSpeed (> windspeed 25))] 
                                  (reset! rule-output ?__token__))

        session (-> (mk-rulebase cold-windy-rule) 
                    (mk-session)
                    (insert (->WindSpeed 30 "MCI"))
                    (insert (->Temperature 10 "MCI")))]

    (fire-rules session)

    (is (= 
         (->Token [(->Temperature 10 "MCI") (->WindSpeed 30 "MCI")] {})
         @rule-output))))

(deftest test-multiple-simple-rules

  (let [cold-rule-output (atom nil)
        windy-rule-output (atom nil)

        cold-rule (mk-rule [(Temperature (< temperature 20))] 
                            (reset! cold-rule-output ?__token__))

        windy-rule (mk-rule [(WindSpeed (> windspeed 25))] 
                             (reset! windy-rule-output ?__token__))
        session (-> (mk-rulebase cold-rule windy-rule) 
                    (mk-session)
                    (insert (->WindSpeed 30 "MCI"))
                    (insert (->Temperature 10 "MCI")))]

    (fire-rules session)

    ;; Check rule side effects contin the expected token.
    (is (= 
         (->Token [(->Temperature 10 "MCI")] {})
         @cold-rule-output))

    (is (= 
         (->Token [(->WindSpeed 30 "MCI")] {})
         @windy-rule-output))))

(deftest test-multiple-rules-same-fact

  (let [cold-rule-output (atom nil)
        subzero-rule-output (atom nil)
        cold-rule (mk-rule [(Temperature (< temperature 20))] 
                            (reset! cold-rule-output ?__token__))
        subzero-rule (mk-rule [(Temperature (< temperature 0))] 
                            (reset! subzero-rule-output ?__token__))

        session (-> (mk-rulebase cold-rule subzero-rule) 
                    (mk-session)
                    (insert (->Temperature -10 "MCI")))]

    (fire-rules session)

    (is (= 
         (->Token [(->Temperature -10 "MCI")] {})
         @cold-rule-output))

    (is (= 
         (->Token [(->Temperature -10 "MCI")] {})
         @subzero-rule-output))))

(deftest test-simple-binding
  (let [rule-output (atom nil)
        cold-rule (mk-rule [(Temperature (< temperature 20) (== ?t temperature))] 
                            (reset! rule-output ?t) )

        session (-> (mk-rulebase cold-rule) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI")))]


    (fire-rules session)
    (is (= 10 @rule-output))))

(deftest test-simple-join-binding 
  (let [rule-output (atom nil)
        same-wind-and-temp (mk-rule [(Temperature (== ?t temperature))
                                      (WindSpeed (== ?t windspeed))] 
                                     (reset! rule-output ?t) )

        session (-> (mk-rulebase same-wind-and-temp) 
                    (mk-session)
                    (insert (->Temperature 10  "MCI"))
                    (insert (->WindSpeed 10  "MCI")))]

    (fire-rules session)
    (is (= 10 @rule-output))))

(deftest test-simple-join-binding-nomatch
  (let [rule-output (atom nil)
        same-wind-and-temp (mk-rule [(Temperature (== ?t temperature))
                                      (WindSpeed (== ?t windspeed))] 
                                     (reset! rule-output ?t) )

        session (-> (mk-rulebase) 
                    (add-productions same-wind-and-temp)
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (insert (->WindSpeed 20 "MCI")))]

    (fire-rules session)
    (is (= nil @rule-output))))

(deftest test-simple-query
  (let [cold-query (mk-query [] [(Temperature (< temperature 20) (== ?t temperature))])

        session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 80 "MCI")))]

    ;; The query should identify all items that wer einserted and matchd the
    ;; expected criteria.
    (is (= #{{:?t 15} {:?t 10}}
           (set (query session cold-query))))))

(deftest test-param-query
  (let [cold-query (mk-query [:?l] [(Temperature (< temperature 50)
                                                  (== ?t temperature)
                                                  (== ?l location))])

        session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 20 "MCI")) ; Test multiple items in result.
                    (insert (->Temperature 10 "ORD"))
                    (insert (->Temperature 35 "BOS"))
                    (insert (->Temperature 80 "BOS")))]

    (comment
      (println "OLD:")
      (println (:query-nodes (add-productions (mk-rulebase) cold-query)))
      (println "NEW:")
      (println (:query-nodes (mk-rulebase cold-query))))

    ;; Query by location.
    (is (= #{{:?l "BOS" :?t 35}}
           (set (query session cold-query :?l "BOS"))))

    (is (= #{{:?l "MCI" :?t 15} {:?l "MCI" :?t 20}}
           (set (query session cold-query :?l "MCI"))))

    (is (= #{{:?l "ORD" :?t 10}}
           (set (query session cold-query :?l "ORD"))))))

(deftest test-simple-condition-binding
  (let [cold-query (mk-query [] [(?t <- Temperature (< temperature 20))])

        session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI")))]

    (is (= #{{:?t #clara.rules.testfacts.Temperature{:temperature 15 :location "MCI"}} 
             {:?t #clara.rules.testfacts.Temperature{:temperature 10 :location "MCI"}}}
           (set (query session cold-query))))))

(deftest test-condition-and-value-binding
  (let [cold-query (mk-query [] [(?t <- Temperature (< temperature 20) (== ?v temperature))])

        session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI")))]

    ;; Ensure the condition's fact and values are all bound.
    (is (= #{{:?v 10, :?t #clara.rules.testfacts.Temperature{:temperature 10 :location "MCI"}} 
             {:?v 15, :?t #clara.rules.testfacts.Temperature{:temperature 15 :location "MCI"}}}
           (set (query session cold-query))))))

(deftest test-simple-accumulator
  (let [lowest-temp (accumulate
                     :reduce-fn (fn [value item]
                                  (if (or (= value nil)
                                          (< (:temperature item) (:temperature value) ))
                                    item
                                    value)))
        coldest-query (mk-query [] [[?t <- lowest-temp from [Temperature]]])

        session (-> (mk-rulebase coldest-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 80 "MCI")))]

    ;; Accumulator returns the lowest value.
    (is (= #{{:?t (->Temperature 10 "MCI")}}
           (set (query session coldest-query))))))

(defn min-fact 
  "Function to create a new accumulator for a test."
  [field]
  (accumulate
   :reduce-fn (fn [value item]
                (if (or (= value nil)
                        (< (field item) (field value) ))
                  item
                  value))))

(deftest test-defined-accumulator 
  (let [coldest-query (mk-query [] [[?t <- (min-fact :temperature) from [Temperature]]])

        session (-> (mk-rulebase coldest-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 80 "MCI")))]

    ;; Accumulator returns the lowest value.
    (is (= #{{:?t (->Temperature 10 "MCI")}}
           (set (query session coldest-query))))))


(defn average-value 
  "Test accumulator that returns the average of a field"
  [field]
  (accumulate 
   :initial-value [0 0]
   :reduce-fn (fn [[value count] item]
                [(+ value (field item)) (inc count)])
   :combine-fn (fn [[value1 count1] [value2 count2]]
                 [(+ value1 value2) (+ count1 count2)])
   :convert-return-fn (fn [[value count]] (/ value count))))

(deftest test-accumulator-with-result 

  (let [average-temp-query (mk-query [] [[?t <- (average-value :temperature) from [Temperature]]])

        session (-> (mk-rulebase average-temp-query) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 20 "MCI"))
                    (insert (->Temperature 30 "MCI"))
                    (insert (->Temperature 40 "MCI"))
                    (insert (->Temperature 50 "MCI"))
                    (insert (->Temperature 60 "MCI")))]

 
    ;; Accumulator returns the lowest value.
    (is (= #{{:?t 35}}
           (set (query session average-temp-query))))))

(deftest test-accumulate-with-retract
  (let [coldest-query (mk-query [] [[?t <- (accumulate
                                            :initial-value []
                                            :reduce-fn conj
                                            :combine-fn concat

                                            ;; Retract by removing the retracted item.
                                            ;; In general, this would need to remove
                                            ;; only the first matching item to achieve expected semantics.
                                            :retract-fn (fn [reduced item] 
                                                          (remove #{item} reduced))

                                            ;; Sort here and return the smallest.
                                            :convert-return-fn (fn [reduced] 
                                                                 (first 
                                                                  (sort #(< (:temperature %1) (:temperature %2))
                                                                        reduced))))

                                   :from (Temperature (< temperature 20))]])

        session (-> (mk-rulebase coldest-query) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))            
                    (insert (->Temperature 17 "MCI"))
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 80 "MCI"))
                    (retract (->Temperature 10 "MCI")))]

    ;; The accumulator result should be 
    (is (= #{{:?t (->Temperature 15 "MCI")}}
           (set (query session coldest-query))))))



(deftest test-joined-accumulator
  (let [coldest-query (mk-query [] [(WindSpeed (== ?loc location))
                                  [?t <- (accumulate
                                           :reduce-fn (fn [value item]
                                                        (if (or (= value nil)
                                                                (< (:temperature item) (:temperature value) ))
                                                          item
                                                          value)))
                                   :from (Temperature (== ?loc location))]])

        session (-> (mk-rulebase coldest-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 5 "SFO"))

                    ;; Insert last to exercise left activation of accumulate node.
                    (insert (->WindSpeed 30 "MCI")))
        
        session-retracted (retract session (->WindSpeed 30 "MCI"))]


    ;; Only the value that joined to WindSpeed should be visible.
    (is (= #{{:?t (->Temperature 10 "MCI") :?loc "MCI"}}
           (set (query session coldest-query))))
    
    (is (empty? (query session-retracted coldest-query)))))

(deftest test-bound-accumulator-var
  (let [coldest-query (mk-query [:?loc] 
                                 [[?t <- (accumulate
                                           :reduce-fn (fn [value item]
                                                        (if (or (= value nil)
                                                                (< (:temperature item) (:temperature value) ))
                                                          item
                                                          value)))
                                   :from (Temperature (== ?loc location))]])

        session (-> (mk-rulebase coldest-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 5 "SFO")))]

    (is (= #{{:?t (->Temperature 10 "MCI") :?loc "MCI"}}
           (set (query session coldest-query :?loc "MCI"))))

    (is (= #{{:?t (->Temperature 5 "SFO") :?loc "SFO"}}
           (set (query session coldest-query :?loc "SFO"))))))

(deftest test-simple-negation
  (let [not-cold-query (mk-query [] [(not (Temperature (< temperature 20)))])

        session (-> (mk-rulebase not-cold-query) 
                    (mk-session))

        session-with-temp (insert session (->Temperature 10 "MCI"))
        session-retracted (retract session-with-temp (->Temperature 10 "MCI"))]

    ;; No facts for the above criteria exist, so we should see a positive result
    ;; with no bindings.
    (is (= #{{}}
           (set (query session not-cold-query))))
    
    ;; Inserting an item into the sesion should invalidate the negation.
    (is (empty? (query session-with-temp
                       not-cold-query)))

    ;; Retracting the inserted item should make the negation valid again.
    (is (= #{{}}
           (set (query session-retracted not-cold-query))))))


(deftest test-negation-with-other-conditions
  (let [windy-but-not-cold-query (mk-query [] [(WindSpeed (> windspeed 30) (== ?w windspeed)) 
                                               (not (Temperature (< temperature 20)))])

        session (-> (mk-rulebase windy-but-not-cold-query) 
                    (mk-session))

        ;; Make it windy, so our query should indicate that.
        session (insert session (->WindSpeed 40 "MCI"))
        windy-result  (set (query session windy-but-not-cold-query))

        ;; Make it hot and windy, so our query should still succeed.
        session (insert session (->Temperature 80 "MCI"))
        hot-and-windy-result (set (query session windy-but-not-cold-query))

        ;; Make it cold, so our query should return nothing.
        session (insert session (->Temperature 10 "MCI"))
        cold-result  (set (query session windy-but-not-cold-query))]


    (is (= #{{:?w 40}} windy-result))
    (is (= #{{:?w 40}} hot-and-windy-result))

    (is (empty? cold-result))))


(deftest test-negated-conjunction
  (let [not-cold-and-windy (mk-query [] [(not (and (WindSpeed (> windspeed 30))
                                                 (Temperature (< temperature 20))))])

        session (-> (mk-rulebase not-cold-and-windy) 
                    (mk-session))

        session-with-data (-> session
                              (insert (->WindSpeed 40 "MCI"))
                              (insert (->Temperature 10 "MCI")))]

    ;; It is not cold and windy, so we should have a match.
    (is (= #{{}}
           (set (query session not-cold-and-windy))))

    ;; Make it cold and windy, so there should be no match.
    (is (empty? (query session-with-data not-cold-and-windy)))))

(deftest test-negated-disjunction
  (let [not-cold-or-windy (mk-query [] [(not (or (WindSpeed (> windspeed 30))
                                                 (Temperature (< temperature 20))))])

        session (-> (mk-rulebase) 
                    (add-productions not-cold-or-windy)
                    (mk-session))

        session-with-temp (insert session (->WindSpeed 40 "MCI"))
        session-retracted (retract session-with-temp (->WindSpeed 40 "MCI"))]

    ;; It is not cold and windy, so we should have a match.
    (is (= #{{}}
           (set (query session not-cold-or-windy))))

    ;; Make it cold and windy, so there should be no match.
    (is (empty? (query session-with-temp not-cold-or-windy)))

    ;; Retract the added fact and ensure we now match something.
    (is (= #{{}}
           (set (query session-retracted not-cold-or-windy))))))


(deftest test-simple-retraction
  (let [cold-query (mk-query [] [[Temperature (< temperature 20) (== ?t temperature)]])

        temp (->Temperature 10 "MCI")

        session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert temp))]

    ;; Ensure the item is there as expected.
    (is (= #{{:?t 10}}
           (set (query session cold-query))))

    ;; Ensure the item is retracted as expected.
    (is (= #{}
           (set (query (retract session temp) cold-query))))))

(deftest test-noop-retraction
  (let [cold-query (mk-query [] [[Temperature (< temperature 20) (== ?t temperature)]])

        session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (retract (->Temperature 15 "MCI")))] ; Ensure retracting a non-existant item has no ill effects.

    (is (= #{{:?t 10}}
           (set (query session cold-query))))))

(deftest test-retraction-of-join
  (let [same-wind-and-temp (mk-query [] [(Temperature (== ?t temperature))
                                      (WindSpeed (== ?t windspeed))])

        session (-> (mk-rulebase same-wind-and-temp) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (insert (->WindSpeed 10 "MCI")))]

    ;; Ensure expected join occurred.
    (is (= #{{:?t 10}}
           (set (query session same-wind-and-temp))))

    ;; Ensure item was removed as viewed by the query.

    (is (= #{}
           (set (query 
                 (retract session (->Temperature 10 "MCI"))
                 same-wind-and-temp))))))


(deftest test-simple-disjunction
  (let [or-query (mk-query [] [(or (Temperature (< temperature 20) (== ?t temperature))
                                 (WindSpeed (> windspeed 30) (== ?w windspeed)))])

        rulebase (-> (mk-rulebase or-query))

        cold-session (insert (mk-session rulebase) (->Temperature 15 "MCI"))
        windy-session (insert (mk-session rulebase) (->WindSpeed 50 "MCI"))  ]

    (is (= #{{:?t 15}}
           (set (query cold-session or-query))))

    (is (= #{{:?w 50}}
           (set (query windy-session or-query))))))

(deftest test-disjunction-with-nested-and

  (let [really-cold-or-cold-and-windy 
        (mk-query [] [(or (Temperature (< temperature 0) (== ?t temperature))
                          (and (Temperature (< temperature 20) (== ?t temperature))
                               (WindSpeed (> windspeed 30) (== ?w windspeed))))])

        rulebase (mk-rulebase really-cold-or-cold-and-windy) 

        cold-session (-> (mk-session rulebase)
                         (insert (->Temperature -10 "MCI")))

        windy-session (-> (mk-session rulebase)
                          (insert (->Temperature 15 "MCI"))
                          (insert (->WindSpeed 50 "MCI")))]

    (is (= #{{:?t -10}}
           (set (query cold-session really-cold-or-cold-and-windy))))

    (is (= #{{:?w 50 :?t 15}}
           (set (query windy-session really-cold-or-cold-and-windy))))))

(deftest test-simple-insert 
    (let [rule-output (atom nil)
        ;; Insert a new fact and ensure it exists.
        cold-rule (mk-rule [(Temperature (< temperature 20) (== ?t temperature))] 
                            (insert! (->Cold ?t)) )

        cold-query (mk-query [] [(Cold (== ?c temperature))])

        session (-> (mk-rulebase cold-rule cold-query) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

      (is (= #{{:?c 10}}
             (set (query session cold-query))))))

(deftest test-insert-and-retract 
    (let [rule-output (atom nil)
        ;; Insert a new fact and ensure it exists.
        cold-rule (mk-rule [(Temperature (< temperature 20) (== ?t temperature))] 
                            (insert! (->Cold ?t)) )

        cold-query (mk-query [] [(Cold (== ?c temperature))])

        session (-> (mk-rulebase cold-rule cold-query) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

      (is (= #{{:?c 10}}
             (set (query session cold-query))))

      ;; Ensure retracting the temperature also removes the logically inserted fact.
      (is (empty? 
           (query 
            (retract session (->Temperature 10 "MCI"))
            cold-query)))))


(deftest test-insert-and-retract-multi-input 
    (let [rule-output (atom nil)
        ;; Insert a new fact and ensure it exists.
        cold-rule (mk-rule [(Temperature (< temperature 20) (== ?t temperature))
                             (WindSpeed (> windspeed 30) (== ?w windspeed))] 
                            (insert! (->ColdAndWindy ?t ?w)) )

        cold-query (mk-query [] [(ColdAndWindy (== ?ct temperature) (== ?cw windspeed))])

        session (-> (mk-rulebase cold-rule cold-query) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (insert (->WindSpeed 40 "MCI"))
                    (fire-rules))]

      (is (= #{{:?ct 10 :?cw 40}}
             (set (query session cold-query))))

      ;; Ensure retracting the temperature also removes the logically inserted fact.
      (is (empty? 
           (query 
            (retract session (->Temperature 10 "MCI"))
            cold-query)))))

(deftest test-ast-to-dnf 

  ;; Test simple condition.
  (is (= {:type :condition :content :placeholder} 
         (ast-to-dnf {:type :condition :content :placeholder} )))

  ;; Test single-item conjunection.
  (is (= {:type :and 
            :content [{:type :condition :content :placeholder}]} 
         (ast-to-dnf {:type :and 
                      :content [{:type :condition :content :placeholder}]})))

  ;; Test multi-item conjunction.
  (is (= {:type :and 
            :content [{:type :condition :content :placeholder1}
                      {:type :condition :content :placeholder2}
                      {:type :condition :content :placeholder3}]} 
         (ast-to-dnf {:type :and 
                      :content [{:type :condition :content :placeholder1}
                                {:type :condition :content :placeholder2}
                                {:type :condition :content :placeholder3}]})))
  
  ;; Test simple disjunction
  (is (= {:type :or
          :content [{:type :condition :content :placeholder1}
                    {:type :condition :content :placeholder2}
                    {:type :condition :content :placeholder3}]}
         (ast-to-dnf {:type :or
                      :content [{:type :condition :content :placeholder1}
                                {:type :condition :content :placeholder2}
                                {:type :condition :content :placeholder3}]})))


  ;; Test simple disjunction with nested conjunction.
  (is (= {:type :or
          :content [{:type :condition :content :placeholder1}
                    {:type :and
                     :content [{:type :condition :content :placeholder2}
                               {:type :condition :content :placeholder3}]}]}
         (ast-to-dnf {:type :or
                      :content [{:type :condition :content :placeholder1}
                                {:type :and
                                 :content [{:type :condition :content :placeholder2}
                                           {:type :condition :content :placeholder3}]}]}))) 

  ;; Test simple distribution of a nested or expression.
  (is (= {:type :or,
          :content
          [{:type :and,
            :content
            [{:content :placeholder1, :type :condition}
             {:content :placeholder3, :type :condition}]}
           {:type :and,
            :content
            [{:content :placeholder2, :type :condition}
             {:content :placeholder3, :type :condition}]}]}

         (ast-to-dnf {:type :and
                      :content 
                      [{:type :or 
                        :content 
                        [{:type :condition :content :placeholder1}
                         {:type :condition :content :placeholder2}]}                                 
                       {:type :condition :content :placeholder3}]})))

  ;; Test push negation to edges.
  (is (= {:type :and, 
           :content 
           [{:type :not, :content [{:content :placeholder1, :type :condition}]} 
            {:type :not, :content [{:content :placeholder2, :type :condition}]} 
            {:type :not, :content [{:content :placeholder3, :type :condition}]}]}
          (ast-to-dnf {:type :not 
                       :content
                       [{:type :or 
                         :content 
                         [{:type :condition :content :placeholder1}
                          {:type :condition :content :placeholder2}
                          {:type :condition :content :placeholder3}]}]})))

  (is (= {:type :and,
          :content [{:type :and,
                     :content
                     [{:type :not, :content [{:content :placeholder1, :type :condition}]}
                      {:type :not, :content [{:content :placeholder2, :type :condition}]}]}]}
         
       (ast-to-dnf {:type :and
                      :content
                      [{:type :not
                        :content
                        [{:type :or
                          :content
                          [{:type :condition :content :placeholder1}
                           {:type :condition :content :placeholder2}]}]}]})))
  
  ;; Test push negation to edges.
  (is (= {:type :or, 
          :content [{:type :not, :content [{:content :placeholder1, :type :condition}]} 
                    {:type :not, :content [{:content :placeholder2, :type :condition}]} 
                    {:type :not, :content [{:content :placeholder3, :type :condition}]}]}
         (ast-to-dnf {:type :not 
                      :content
                      [{:type :and
                        :content 
                        [{:type :condition :content :placeholder1}
                         {:type :condition :content :placeholder2}
                         {:type :condition :content :placeholder3}]}]})))

  ;; Test simple identity disjunction.
  (is (= {:type :or
          :content
          [{:type :not :content [{:type :condition :content :placeholder1}]}
           {:type :not :content [{:type :condition :content :placeholder2}]}]}
         (ast-to-dnf {:type :or
                      :content
                      [{:type :not :content [{:type :condition :content :placeholder1}]}
                       {:type :not :content [{:type :condition :content :placeholder2}]}]})))

  ;; Test distribution over multiple and expressions.
  (is (= {:type :or,
          :content
          [{:type :and,
            :content
            [{:content :placeholder1, :type :condition}
             {:content :placeholder4, :type :condition}
             {:content :placeholder5, :type :condition}]}
           {:type :and,
            :content
            [{:content :placeholder2, :type :condition}
             {:content :placeholder4, :type :condition}
             {:content :placeholder5, :type :condition}]}
           {:type :and,
            :content
            [{:content :placeholder3, :type :condition}
             {:content :placeholder4, :type :condition}
             {:content :placeholder5, :type :condition}]}]}
         (ast-to-dnf {:type :and
                      :content 
                      [{:type :or 
                        :content 
                        [{:type :condition :content :placeholder1}
                         {:type :condition :content :placeholder2}
                         {:type :condition :content :placeholder3}]}                                 
                       {:type :condition :content :placeholder4}
                       {:type :condition :content :placeholder5}]}))))

(def simple-defrule-side-effect (atom nil))

(defrule test-rule 
  (Temperature (< temperature 20))
  =>
  (reset! simple-defrule-side-effect ?__token__))

(deftest test-simple-defrule
  (let [session (-> (mk-rulebase test-rule) 
                    (mk-session)
                    (insert (->Temperature 10 "MCI")))]

    (fire-rules session)

    (is (= 
         (->Token [(->Temperature 10 "MCI")] {})
         @simple-defrule-side-effect))))

(defquery cold-query  
  [:?l] 
  (Temperature (< temperature 50)
               (== ?t temperature)
               (== ?l location)))

(deftest test-defquery
  (let [session (-> (mk-rulebase cold-query) 
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 20 "MCI")) ; Test multiple items in result.
                    (insert (->Temperature 10 "ORD"))
                    (insert (->Temperature 35 "BOS"))
                    (insert (->Temperature 80 "BOS")))]


    ;; Query by location.
    (is (= #{{:?l "BOS" :?t 35}}
           (set (query session cold-query :?l "BOS"))))

    (is (= #{{:?l "MCI" :?t 15} {:?l "MCI" :?t 20}}
           (set (query session cold-query :?l "MCI"))))

    (is (= #{{:?l "ORD" :?t 10}}
           (set (query session cold-query :?l "ORD"))))))

(deftest test-rules-from-ns

  (is (= #{{:?loc "MCI"} {:?loc "BOS"}}
       (set (-> (mk-session 'clara.sample-ruleset)
                (insert (->Temperature 15 "MCI"))
                (insert (->Temperature 22 "BOS"))
                (insert (->Temperature 50 "SFO"))
                (query sample/freezing-locations)))))

  (let [session (-> (mk-session 'clara.sample-ruleset)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->WindSpeed 45 "MCI"))
                    (fire-rules))]

    (is (= #{{:?fact (->ColdAndWindy 15 45)}}  
           (set 
            (query session sample/find-cold-and-windy))))))

(deftest test-rules-from-multi-namespaces

  (let [session (-> (mk-session 'clara.sample-ruleset 'clara.other-ruleset)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "BOS"))
                    (insert (->Temperature 50 "SFO"))
                    (insert (->Temperature -10 "CHI")))]

    (is (= #{{:?loc "MCI"} {:?loc "BOS"} {:?loc "CHI"}}
           (set (query session sample/freezing-locations))))

    (is (= #{{:?loc "CHI"}}
           (set (query session other/subzero-locations))))))

(deftest test-transitive-rule

  (is (= #{{:?fact (->LousyWeather)}}  
         (set (-> (mk-session 'clara.sample-ruleset 'clara.other-ruleset)
                  (insert (->Temperature 15 "MCI"))
                  (insert (->WindSpeed 45 "MCI"))
                  (fire-rules)
                  (query sample/find-lousy-weather))))))


(deftest test-mark-as-fired
  (let [rule-output (atom nil)
        cold-rule (mk-rule [[Temperature (< temperature 20)]] 
                            (reset! rule-output ?__token__) )

        session (-> (mk-rulebase) 
                    (add-productions cold-rule)
                    (mk-session)
                    (insert (->Temperature 10 "MCI"))
                    (fire-rules))]

    (is (= 
         (->Token [(->Temperature 10 "MCI")] {})
         @rule-output))
    
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
    
    (is (= 
         (->Token [(->Temperature 10 "MCI")] {})
         @rule-output))))


(deftest test-chained-inference
  (let [item-query (mk-query [] [(?item <- Fourth)])

        session (-> (mk-rulebase)                    
                    (add-productions (mk-rule [(Third)] (insert! (->Fourth)))) ; Rule order shouldn't matter, but test it anyway.
                    (add-productions (mk-rule [(First)] (insert! (->Second))))
                    (add-productions (mk-rule [(Second)] (insert! (->Third))))
                    (add-productions item-query)
                    (mk-session)
                    (insert (->First))
                    (fire-rules))]

    ;; The query should identify all items that wer einserted and matchd the
    ;; expected criteria.
    (is (= #{{:?item (->Fourth)}}
           (set (query session item-query))))))


(deftest test-node-id-map
  (let [cold-rule (mk-rule [(Temperature (< temperature 20))] 
                           (println "Placeholder"))
        windy-rule (mk-rule [(WindSpeed (> windspeed 25))] 
                            (println "Placeholder"))

        rulebase  (mk-rulebase cold-rule windy-rule) 

        cold-rule2 (mk-rule [(Temperature (< temperature 20))] 
                            (println "Placeholder"))
        windy-rule2 (mk-rule [(WindSpeed (> windspeed 25))] 
                             (println "Placeholder"))

        rulebase2 (mk-rulebase cold-rule2 windy-rule2)]

    ;; The keys should be consistent between maps since the rules are identical.
    (is (= (keys (:id-to-node rulebase))
           (keys (:id-to-node rulebase2))))

    ;; Ensure there are beta and production nodes as expected.
    (is (= 4 (count (:id-to-node rulebase))))
    
    (is (= (:id-to-node rulebase) (s/map-invert (:node-to-id rulebase))))))

(deftest test-simple-test
  (let [distinct-temps-query (mk-query [] [(Temperature (< temperature 20) (== ?t1 temperature))
                                           (Temperature (< temperature 20) (== ?t2 temperature))
                                           (test (< ?t1 ?t2))])

        session (-> (mk-rulebase) 
                    (add-productions distinct-temps-query)
                    (mk-session)
                    (insert (->Temperature 15 "MCI"))
                    (insert (->Temperature 10 "MCI"))
                    (insert (->Temperature 80 "MCI")))]

    ;; Finds two temperatures such that t1 is less than t2.
    (is (= #{ {:?t1 10, :?t2 15}} 
           (set (query session distinct-temps-query))))))

(deftest test-bean-support

  ;; Use TimeZone for this test as it is an available JavaBean-like object.
  (let [tz-offset-query (mk-query [:?offset]
                                  [[TimeZone (== ?offset rawOffset)
                                             (== ?id ID)]])
        
        session (-> (mk-rulebase)
                    (add-productions tz-offset-query)
                    (mk-session)
                    (insert (TimeZone/getTimeZone "America/Chicago")
                            (TimeZone/getTimeZone "UTC")))]

    (is (= #{{:?id "America/Chicago" :?offset -21600000}} 
           (set (query session tz-offset-query :?offset -21600000))))

    (is (= #{{:?id "UTC" :?offset 0}} 
           (set (query session tz-offset-query :?offset 0))))))


(deftest test-multi-insert-retract

  (is (= #{{:?loc "MCI"} {:?loc "BOS"}}
         (set (-> (mk-session 'clara.sample-ruleset)
                  (insert (->Temperature 15 "MCI"))
                  (insert (->Temperature 22 "BOS"))

                  ;; Insert a duplicate and then retract it.
                  (insert (->Temperature 22 "BOS"))
                  (retract (->Temperature 22 "BOS"))
                  (query sample/freezing-locations)))))

  ;; Normal retractions should still work.
  (is (= #{}
         (set (-> (mk-session 'clara.sample-ruleset)
                  (insert (->Temperature 15 "MCI"))
                  (insert (->Temperature 22 "BOS"))
                  (retract (->Temperature 22 "BOS") (->Temperature 15 "MCI"))
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

(deftest test-retract! 
  (let [not-cold-rule (mk-rule [[Temperature (> temperature 50)]] 
                               (retract! (->Cold 20)))

        cold-query (mk-query [] [[Cold (== ?t temperature)]])

        session (-> (mk-rulebase not-cold-rule cold-query) 
                    (mk-session)
                    (insert (->Cold 20))              
                    (fire-rules))]

    ;; The session should contain our initial cold reading.
    (is (= #{{:?t 20}}
           (set (query session cold-query))))

    ;; Insert a higher temperature and ensure the cold fact was retracted.
    (is (= #{}
           (set (query (-> session
                           (insert (->Temperature 80 "MCI"))
                           (fire-rules)) 
                       cold-query))))))
