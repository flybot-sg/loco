(ns loco.constraints
  (:require
   [loco.core :as core :refer [->choco
                               ->choco*]])
  (:import
   [org.chocosolver.solver Model]
   [org.chocosolver.solver.variables IntVar BoolVar]
   [org.chocosolver.solver.constraints Constraint]))

(defn- domain-min
  [x]
  (if (number? x)
    x
    (.getLB ^IntVar x)))

(defn- domain-max
  [x]
  (if (number? x)
    x
    (.getUB ^IntVar x)))

(defn- make-const-var
  [^Model model n]
  (.intVar model n))

(defn- make-int-var
  "Quick helper function to generate an integer variable for intermediate calculations."
  [model min max]
  (.intVar model (str (gensym "_int-var")) min max))

(defn- make-bool-var
  "Quick helper function to generate a boolean variable for intermediate calculations."
  [model]
  (.boolVar model (str (gensym "_bool-var"))))

(defn- constrain!
  [model ^Constraint constraint]
  (.post constraint))

(defn- ->int-var
  "Takes a Choco IntVar or a number, and if it is a number, coerces it to an IntVar."
  [model x]
  (cond
    (number? x) (make-const-var model x)
    (instance? IntVar x) x
    (instance? Constraint x) (throw (IllegalArgumentException. "Expected a variable or a number, but got a constraint"))
    :else (throw (IllegalArgumentException. "Expected an int variable or number"))))

(defn- ->choco-int-var
  "Chains ->choco and ->int-var"
  [solver x]
  (->> x (->choco solver) (->int-var (:model solver))))

(defn- id
  []
  (gensym "id"))

;;;;; VAR GENERATION

(defn $in
  "Declares that a variable must be in a certain domain.
Possible arglist examples:
($in :x 1 5)
($in :x [1 2 3 4 5])
($in :x 1 5 :bounded)"
  [var-name & args]
  {:pre [(or (keyword? var-name)
             (and (vector? var-name)
                  (keyword? (first var-name))))]}
  (let [m {:type :int-domain
           :can-init-var true
           :name var-name}
        [m args] (if (number? (first args))
                   [(assoc m :domain {:min (first args) :max (second args)}) (rest (rest args))]
                   [(assoc m :domain (first args)) (rest args)])
        [m args] (if (and (= (first args) :bounded) (map? (:domain m)))
                   [(assoc-in m [:domain :bounded] true) (rest args)]
                   [m args])]
    (when (and (:bounded m)
               (not (map? (:domain m))))
      (throw (IllegalArgumentException. "Bounded domains take a min and a max only")))
    m))

(defmethod ->choco* :int-domain
  [solver {var-name :name domain :domain}]
  (let [model (:model solver)
        v (->choco var-name)]
    (if (map? domain)
      (.intVar model v (:min domain) (:max domain))
      (.intVar model v (int-array (sort (distinct domain)))))))

(defmethod ->choco* :int-var
  [solver data]
  (let [model (:model solver)
        domain-expr (:domain data)
        var-name (:name data)
        real-name (:real-name data)
        v (case [(boolean (:bounded domain-expr)) (sequential? domain-expr)]
            [false false] (.intVar model real-name (:min domain-expr) (:max domain-expr))
            [false true] (.intVar model real-name (int-array (sort domain-expr)))
            [true false] (.intVar model  real-name (:min domain-expr) (:max domain-expr)
                                  true))]
    (swap! (:my-vars solver) assoc var-name v)
    nil))

(defmethod ->choco* :bool-var
  [{:keys [model] :as solver} {var-name :name real-name :real-name}]
  (let [v (.boolVar model real-name)]
    (swap! (:my-vars solver) assoc var-name v)
    nil))

;;;;; ARITHMETIC

(defn- $+view
  [model x const]
  (.intOffsetView model x const))

(defn $+
  "Takes a combination of int-vars and numbers, and returns another number/int-var which is constrained to equal the sum."
  ([x]
    x)
  ([x y & more]
    {:type :+
     :args (list* x y more)
     :id (id)
     :eq-shortcut true}))

(defmethod ->choco* [:+ :=]
  [{:keys [model] :as solver} {:keys [args eq-arg] :as m}]
  (.sum model
        (into-array IntVar (map #(->choco-int-var solver %) args))
        "=" ;; FIXME not sure
        (->choco-int-var solver (:eq-arg m))))

(defmethod ->choco* :+
  [{:keys [model]} {:keys [args] :as m}]
  (let [[x y & more :as vars] (map ->choco args)]
    (cond
      (and (empty? more) (number? y)) ($+view model x y)
      (and (empty? more) (number? x)) ($+view model y x)
      :else (let [vars (map ->int-var vars) ; converting numbers to int-views
                  mins (map #(.getLB ^IntVar %) vars)
                  maxes (map #(.getUB ^IntVar %) vars)
                  sum-var (make-int-var model (apply + mins) (apply + maxes))
                  vars (try (into-array BoolVar vars)
                            (catch Exception e
                              (into-array IntVar vars)))]
              (constrain! model (.sum model (into-array IntVar vars) sum-var))
              sum-var))))

(defn $-
  "Takes a combination of int-vars and numbers, and returns another number/int-var which is constrained
to equal (x - y - z - ...) or (-x) if there's only one argument."
  ([x]
    (if (number? x)
      (- x)
      {:type :neg
       :arg x
       :id (id)}))
  ([x & more]
   (apply $+ x (map $- more))))

(defmethod ->choco* :neg
  [{:keys [model] :as solver} {x :arg}]
  (let [x (->choco solver x)]
    (if (number? x)
      (- x)
      (.intMinusView model x))))

(declare $=)

(defn $*
  "Takes two arguments. One of the arguments can be a number greater than or equal to -1."
  [x y]
  {:type :*
   :arg1 x
   :arg2 y
   :id (id)
   :eq-shortcut true})

(defn- $*view
  [model x const]
  (.intScaleView model x const))

(defn- keypoints
  [vars op neutral]
  (if (empty? vars)
    [neutral]
    (let [v (first vars)
          lo (domain-min v)
          hi (domain-max v)]
      (for [arg1 [lo hi]
            arg2 (keypoints (rest vars) op neutral)]
        (op arg1 arg2)))))

(defmethod ->choco* [:* :=]
  [{:keys [model] :as solver} {x :arg1 y :arg2 z :eq-arg}]
  (let [x (->choco solver x)
        y (->choco solver y)]
    (cond
      (number? y) (.arithm model ($*view model x y) "=" (->choco-int-var solver z))
      (number? x) (.arithm model ($*view model y x) "=" (->choco-int-var solver z))
      :else (.times model x y (->choco-int-var solver z)))))

(defmethod ->choco* :*
  [{:keys [model]} {x :arg1 y :arg2}]
  (let [x (->choco x)
        y (->choco y)]
    (cond
      (number? y) ($*view x y)
      (number? x) ($*view y x)
      :else (let [nums (keypoints [x y] * 1)
                  total-min (apply min nums)
                  total-max (apply max nums)
                  z (make-int-var model total-min total-max)]
              (constrain! model (.times model x y z))
              z))))

(defn $min
  "The minimum of several arguments. The arguments can be a mixture of int-vars and numbers."
  [& args]
  {:type :min
   :args args
   :id (id)
   :eq-shortcut true})

(defmethod ->choco* [:min :=]
  [{:keys [model] :as solver} {:keys [args eq-arg]}]
  (let [args (map #(->choco-int-var solver %) args)
        eq-arg (->choco-int-var solver eq-arg)]
    (if (= (count args) 2)
      (.min model eq-arg (first args) (second args))
      (.min model eq-arg (into-array IntVar args)))))

(defmethod ->choco* :min
  [{:keys [model] :as solver} {:keys [args]}]
  (let [args (map #(->choco-int-var solver %) args)
        mins (map domain-min args)
        maxes (map domain-max args)
        final-min (apply min mins)
        final-max (apply min maxes)
        new-var (make-int-var model final-min final-max)]
    (constrain! model
                (if (= (count args) 2)
                  (.min model new-var (first args) (second args))
                  (.min model new-var (into-array IntVar args))))
    new-var))

(defn $max
  "The maximum of several arguments. The arguments can be a mixture of int-vars and numbers."
  [& args]
  {:type :max
   :args args
   :id (id)
   :eq-shortcut true})

(defmethod ->choco* [:max :=]
  [{:keys [model] :as solver} {:keys [args eq-arg]}]
  (let [args (map #(->choco-int-var solver %) args)
        eq-arg (->choco-int-var solver eq-arg)]
    (if (= (count args) 2)
      (.max model eq-arg (first args) (second args))
      (.max model eq-arg (into-array IntVar args)))))

(defmethod ->choco* :max
  [{:keys [model] :as solver} {:keys [args]}]
  (let [args (map #(->choco-int-var solver %) args)
        mins (map domain-min args)
        maxes (map domain-max args)
        final-min (apply max mins)
        final-max (apply max maxes)
        new-var (make-int-var model final-min final-max)]
    (constrain! model
                (if (= (count args) 2)
                  (.max model new-var (first args) (second args))
                  (.max model new-var (into-array IntVar args))))
    new-var))

(defn $mod
  "Given variables X and Y, returns X mod Y."
  [X Y]
  {:type :mod
   :arg1 X
   :arg2 Y
   :id (id)
   :eq-shortcut true})

(defmethod ->choco* [:mod :=]
  [{:keys [model] :as solver} {X :arg1 Y :arg2 Z :eq-arg}]
  (.mod model
        (->choco-int-var solver X)
        (->choco-int-var solver Y)
        (->choco-int-var solver Z)))

(defmethod ->choco* :mod
  [{:keys [model] :as solver} {X :arg1 Y :arg2}]
  (let [X (->choco-int-var solver X)
        Y (->choco-int-var solver Y)
        Ymax (domain-max Y)
        Z (make-int-var model 0 (max (dec Ymax) 0))]
    (constrain! model (.mod model X Y Z))
    Z))

(defn $abs
  "Given a variable X, returns the absolute value of X, or |X|."
  [X]
  {:type :abs
   :arg X
   :id (id)
   :eq-shortcut true})

(defmethod ->choco* [:abs :=]
  [{:keys [model] :as solver} {X :arg Y :eq-arg}]
  (.absolute model (->choco-int-var solver Y) (->choco-int-var solver X)))

(defmethod ->choco* :abs
  [{:keys [model] :as solver} {X :arg}]
  (.intAbsView model (->choco-int-var solver X)))

(defn $scalar
  "Given a list of variables X, Y, Z, etc. and a list of number coefficients a, b, c, etc. returns a new variable constrained to equal aX + bY + cZ ..."
  [variables coefficients]
  {:type :scalar
   :variables variables
   :coefficients coefficients
   :id (id)
   :eq-shortcut true})

(defmethod ->choco* [:scalar :=]
  [{:keys [model] :as solver} {:keys [variables coefficients eq-arg]}]
  (.scalar model
           (into-array IntVar (map #(->choco-int-var solver %) variables))
           (int-array coefficients)
           "="
           (->choco-int-var solver eq-arg)))

(defmethod ->choco* :scalar
  [{:keys [model] :as solver} {:keys [variables coefficients]}]
  (let [variables (map #(->choco-int-var solver %) variables)
        minmaxes (for [[v c] (map vector variables coefficients)
                       :let [dmin (* (domain-min v) c)
                             dmax (* (domain-max v) c)]]
                   (if (< dmin dmax)
                     [dmin dmax]
                     [dmax dmin]))
        final-min (apply + (map first minmaxes))
        final-max (apply + (map second minmaxes))
        new-var (make-int-var model final-min final-max)]
    (constrain! model (.scalar model (into-array IntVar variables) (int-array coefficients) "=" new-var))
    new-var))

(declare $not $and)

(def ^:private eq-converse
  {:= :=
   :< :>
   :> :<
   :<= :>=
   :>= :<=
   :!= :!=})

(defmacro ^:private defn-equality-constraint
  [fnname docstring eqstr]
  `(defn ~fnname
     ~docstring
     ([X# Y#]
       {:type :arithm-eq
        :eq ~eqstr
        :arg1 X#
        :arg2 Y#})
     ([X# Y# & more#]
      (apply $and (map (partial apply ~fnname) (partition 2 1 (list* X# Y# more#)))))))

(defmethod ->choco* :arithm-eq
  [{:keys [model] :as solver} data]
  (let [op (:eq data)
        X (->choco-int-var solver (:arg1 data))
        Y (->choco-int-var solver (:arg2 data))]
    (.arithm model X (name op) Y)))

(defn-equality-constraint $<
  "Constrains that X < Y.
Giving more than 2 inputs results in an $and statement with multiple $< statements."
  "<")
(defn-equality-constraint $>
  "Constrains that X > Y.
Giving more than 2 inputs results in an $and statement with multiple $> statements."
  ">")
(defn-equality-constraint $<=
  "Constrains that X <= Y.
Giving more than 2 inputs results in an $and statement with multiple $<= statements."
  "<=")
(defn-equality-constraint $>=
  "Constrains that X >= Y.
Giving more than 2 inputs results in an $and statement with multiple $>= statements."
  ">=")

(defn-equality-constraint ^:private $=*
  "(internal) Raw equal constraint."
  "=")
(defn $=
  "Constrains that X = Y.
  Giving more than 2 inputs results in an $and statement with multiple $= statements."
  ([X Y]
   (cond
     (:eq-shortcut X) (assoc X
                             :id (id)
                             :type [(:type X) :=]
                             :eq-arg Y)
     (:eq-shortcut Y) (assoc Y
                             :id (id)
                             :type [(:type Y) :=]
                             :eq-arg X)
     :else ($=* X Y)))
  ([X Y Z & more]
   (apply $=* X Y Z more)))

(defn $!=
  "Constrains that X != Y, i.e. (not X = Y = ...)"
  ([X Y]
    {:type :arithm-eq
     :eq :!=
     :arg1 X
     :arg2 Y})
  ([X Y Z & more]
    ($not (apply $= X Y Z more))))

;;;;; LOGIC

(defn $true
  "Always true."
  []
  {:type :true
   :id (id)})

(defmethod ->choco* :true
  [{:keys [model]} _]
  (.trueConstraint model))

(defn $false
  "Always false."
  []
  {:type :false
   :id (id)})

(defmethod ->choco* :false
  [{:keys [model]} _]
  (.falseConstraint model))

(defn $and
  "An \"and\" statement (i.e. \"P^Q^...\"); this statement is true if and only if every subconstraint is true."
  [& constraints]
  (if (empty? constraints)
    ($true)
    {:type :and, :constraints constraints}))

(defmethod ->choco* :and
  [{:keys [model] :as solver} {constraints :constraints}]
  (let [constraints (map #(->choco solver %) constraints)]
    (.and model (into-array Constraint constraints))))

(defn $or
  "An \"or\" statement (i.e. \"PvQv...\"); this statement is true if and only if at least one subconstraint is true."
  [& constraints]
  (if (empty? constraints)
    ($false)
    {:type :or, :constraints constraints}))

(defmethod ->choco* :or
  [{:keys [model]} {constraints :constraints}]
  (let [constraints (map ->choco constraints)]
    (.or model (into-array Constraint constraints))))

(defn $not
  "Given a constraint C, returns \"not C\" a.k.a. \"~C\", which is true iff C is false."
  [C]
  {:type :not, :arg C})

(defmethod ->choco* :not
  [{:keys [model] :as solver} {C :arg}]
  (let [c (->choco solver C)]
    (.boolNotView model (if (instance? BoolVar c)
                          c
                          (.reify c)))))

(defn $if
  "An \"if\" statement (i.e. \"implies\", \"P=>Q\"); this statement is true if and only if P is false or Q is true.
In other words, if P is true, Q must be true (otherwise the whole statement is false).
An optional \"else\" field can be specified, which must be true if P is false."
  ([if-this then-this]
    {:type :if
     :if if-this
     :then then-this})
  ([if-this then-this else-this]
    {:type :if
     :if if-this
     :then then-this
     :else else-this}))

(defmethod ->choco* :if
  [{:keys [model] :as solver} {if-this :if then-this :then else-this :else}]
  (if-not else-this
    (.ifThen model
             (->choco solver if-this)
             (->choco solver then-this))
    (do
      (.ifThenElse model
                   (->choco solver if-this)
                   (->choco solver then-this)
                   (->choco solver else-this)))))

(defn $cond
  "A convenience function for constructing a \"cond\"-like statement out of $if statements.
The final \"else\" can be specified by itself (being the odd argument) or with the :else keyword.

Example:
($cond P Q, R S, :else T)
=> ($if P Q ($if R S T))

If no \"else\" clause is specified, it is \"True\" by default."
  [& clauses]
  (cond
    (empty? clauses) ($true)
    (empty? (rest clauses)) (first clauses)
    (empty? (rest (rest clauses))) (if (= (first clauses) :else)
                                     (second clauses)
                                     (apply $if clauses))
    :else ($if (first clauses) (second clauses) (apply $cond (rest (rest clauses))))))

(defn $reify
  "Given a constraint C, will generate a bool-var V such that (V = 1) iff C."
  [C]
  {:type :reify
   :arg C
   :id (id)})

(defmethod ->choco* :reify
  [{:keys [model] :as solver} {C :arg}]
  (let [C (->choco solver C)
        V (make-bool-var model)]
    (.reification model V C)
    V))

;;;;; GLOBAL

(defn $distinct
  "Given a bunch of int-vars, ensures that all of them have different values, i.e. no two of them are equal."
  [vars]
  {:type :distinct
   :args vars})

(defmethod ->choco* :distinct
  [{:keys [model] :as solver} {vars :args}]
  (let [vars (map #(->choco solver %) vars)]
    (.allDifferent model (into-array IntVar vars) "DEFAULT")))

(defn $circuit
  "Given a list of int-vars L, and an optional offset number (default 0), the elements of L define a circuit, where
(L[i] = j + offset) means that j is the successor of i.
Hint: make the offset 1 when using a 1-based list."
  ([list-of-vars]
    ($circuit list-of-vars 0))
  ([list-of-vars offset]
    {:type :circuit
     :vars list-of-vars
     :offset offset}))
(defmethod ->choco* :circuit
  [{:keys [model] :as solver} {list-of-vars :vars offset :offset}]
  (let [list-of-vars (map #(->choco-int-var solver %) list-of-vars)]
    (.circuit model (into-array IntVar list-of-vars) offset)))

(defn $nth
  "Given a list of int-vars L, an int-var i, and an optional offset number (default 0), returns a new int-var constrained to equal L[i], or L[i - offset]."
  ([list-of-vars index-var]
    ($nth list-of-vars index-var 0))
  ([list-of-vars index-var offset]
    {:type :nth
     :vars list-of-vars
     :index index-var
     :offset offset
     :id (id)
     :eq-shortcut true}))

(defmethod ->choco* [:nth :=]
  [{:keys [model] :as solver} {:keys [vars index offset eq-arg]}]
  (let [vars (map #(->choco-int-var solver %) vars)
        index (->choco-int-var solver index)
        value (->choco-int-var solver eq-arg)]
    (.element model value (into-array IntVar vars) index offset)))

(defmethod ->choco* :nth
  [{:keys [model] :as solver} {:keys [vars index offset]}]
  (let [vars (map #(->choco-int-var solver %) vars)
        index (->choco-int-var solver index)
        final-min (apply min (map domain-min vars))
        final-max (apply max (map domain-max vars))
        new-var (make-int-var model final-min final-max)]
    (constrain! model (.element model new-var (into-array IntVar vars) index offset))
    new-var))

(defn $cardinality
  "Takes a list of variables, and a frequency map (from numbers to frequencies), constrains
that the frequency map is accurate. If the :closed flag is set to true, any keys that aren't
in the frequency map can't appear at all in the list of variables.

Example: ($cardinality [:a :b :c :d :e] {1 :ones, 2 :twos} :closed true)
=> {:a 1, :b 1, :c 2, :d 2, :e 2
    :ones 2, :twos 3}"
  [variables frequencies & {:as args}]
  {:type :cardinality
   :variables variables
   :values (keys frequencies)
   :occurrences (vals frequencies)
   :closed (:closed args)})
(defmethod ->choco* :cardinality
  [{:keys [model] :as solver} {variables :variables values :values occurrences :occurrences closed :closed}]
  (let [values (int-array values)
        occurrences (into-array IntVar (map #(->choco-int-var solver %) occurrences))
        variables (into-array IntVar (map #(->choco-int-var solver %) variables))]
    (.globalCardinality model variables values occurrences (boolean closed))))

(defn $knapsack
  "Takes constant weights / values for a list of pre-defined items, and
a list of variables representing the amount of each item. Constrains that
the values of all the items add up to the total-value, while the items'
weights add up to total-weight.

Example: ($knapsack [3 1 2]    ; weights
                    [5 6 7]    ; values
                    [:x :y :z] ; occurrences
                    :W         ; total weight
                    :V)        ; total value"
  [weights values occurrences total-weight total-value]
  (assert (and (every? integer? weights)
               (every? integer? values))
          "$knapsack: weights and values must be collections of constant integers")
  {:type :knapsack
   :weights weights
   :values values
   :occurrences occurrences
   :total-weight total-weight
   :total-value total-value})
(defmethod ->choco* :knapsack
  [{:keys [model] :as solver} {:keys [weights values occurrences total-weight total-value]}]
  (let [occurrences (map #(->choco-int-var solver %) occurrences)
        total-weight (->choco-int-var solver total-weight)
        total-value (->choco-int-var solver total-value)]
    (.knapsack model
               (into-array IntVar occurrences)
               ^IntVar total-weight
               ^IntVar total-value
               (int-array weights)
               (int-array values))))
