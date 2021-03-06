(ns loco.core
  (:import
   [org.chocosolver.solver.variables IntVar]
   [org.chocosolver.solver.exception SolverException]
   [org.chocosolver.solver ResolutionPolicy Model Solver Solution]
   [org.chocosolver.solver.constraints Constraint]
   [org.chocosolver.solver.search.strategy
    Search
    strategy.AbstractStrategy]
   [org.chocosolver.util ESat]))

(defn- namey?
  [x]
  (try (boolean (name x))
    (catch Exception e
      false)))

(defn- id
  []
  (gensym "id"))

(defmulti ->choco*
  "(INTERNAL) Given Clojure data generated by the Loco DSL, returns a Choco variable (to be used inside
a constraint), or returns a constraint (to be posted to the solver)."
  (fn [_ data]
    (if (and (vector? data)
             (keyword? (first data)))
      :vector-var-name
      (or (:type data) (type data)))))

(defn- intersect-domains
  [d1 d2]
  (cond
    (and (not (map? d1))
         (not (map? d2))) (filter (set d1) d2)
    (and (not (map? d1))
         (map? d2)) (let [{lo :min hi :max} d2]
                      (filter #(<= lo % hi) d1))
    (and (map? d1)
         (not (map? d2))) (recur d2 d1)
    :else (let [{lo1 :min hi1 :max b1? :bounded} d1
                {lo2 :min hi2 :max b2? :bounded} d2
                m {:min (max lo1 lo2)
                   :max (min hi1 hi2)}]
            (if (and b1? b2?)
              (assoc m :bounded true)
              m))))

(defn- top-level-var-declarations
  "finds top-level domain declarations, merges them per-variable,
and returns a list of variable declarations"
  [data]
  (let [domain-decls (filter :can-init-var data)
        all-domains (group-by :name domain-decls)]
    (for [[var-name decls] all-domains
          :let [final-domain (reduce intersect-domains (map :domain decls))]]
      (if (if (map? final-domain)
            (= final-domain {:min 0 :max 1})
            (= #{0 1} (set final-domain)))
        {:type :bool-var
         :name var-name
         :real-name (name (gensym "bool-var"))}
        {:type :int-var
         :name var-name
         :real-name (name (gensym "int-var"))
         :domain (reduce intersect-domains (map :domain decls))}))))

(defn- without-top-level-var-declarations
  [data]
  (remove :can-init-var data))

(defrecord LocoSolver
  [^Model model memo-table my-vars n-solutions])

(defn- new-solver
  []
  (->LocoSolver
   (Model. (str (gensym "solver")))
   (atom {})
   (atom {})
   (atom 0)))

(defn- find-int-var
  [solver n]
  (or (@(:my-vars solver) n)
      (throw (IllegalAccessException. (str "var with name " n
                                           " doesn't have a corresponding "
                                           "\"$in\" call in the top-level"
                                           " of the problem")))))

(defn- get-val
  [^IntVar v]
  (.getLB v))

(defn ->choco
  "(INTERNAL) Memoized version of ->choco*"
  [solver data]
  (let [lookup (when (:id data)
                 (@(:memo-table solver) (:id data)))]
    (if lookup
      lookup
      (let [result (->choco* solver data)]
        (when (:id data)
          (swap! (:memo-table solver) assoc (:id data) result))
        result))))

(defmethod ->choco* java.lang.Number
  [_ data]
  data)

(defmethod ->choco* clojure.lang.Keyword
  [solver data]
  (find-int-var solver data))

(defmethod ->choco* :vector-var-name
  [solver data]
  (find-int-var solver data))

(defn default-search
  "Create default search strategy"
  []
  {:type :default-search})

(defmethod ->choco* :default-search
  [solver _]
  (Search/defaultSearch (:model solver)))

(defn- constrain!
  [^Constraint constraint]
  (.post constraint))

(defn- install-strategies!
  [{:keys [model] :as solver} strategies]
  (let [csolver (.getSolver model)
        strategies
        (into-array AbstractStrategy
                    (map #(->choco solver %) strategies))]
    (.setSearch csolver strategies)))

(defn- problem->solver
  ([problem]
   (problem->solver problem nil))
  ([problem strategies]
   (let [problem (concat (top-level-var-declarations problem)
                         ;; dig for the var declarations and put them at the front
                         (without-top-level-var-declarations problem))
         s (new-solver)]
     (doseq [i problem
             :let [i (->choco s i)]]         
       (when (instance? Constraint i)
         (constrain! i)))
     (install-strategies!
      s (or strategies
            [(default-search)]))
     s)))

(defn- Solution->solution-map
  [solver ^Solution S]
  (into {} (for [[var-name v] @(:my-vars solver)
                 :when (if (keyword? var-name)
                         (not= (first (name var-name)) \_)
                         (not= (first (name (first var-name))) \_))]
             [var-name (.getIntVal S v)])))

(defn- solutions
  [solver]
  (let [^Model model (:model solver)
        ^Solver csolver (.getSolver model)
        ^Solution solution
        (Solution. model
                   (into-array IntVar
                               (vals @(:my-vars solver))))]
    (take-while
     identity
     (repeatedly
      (fn []
        (when (.solve csolver)
          (.record solution)
          (Solution->solution-map solver solution)))))))

(defn solve
  "Solves the solver using the constraints and returns nil if no solution,
  or a lazy seq of maps (for each solution) if no objective set,
  or a map of solution if with objective,
  the map includes pairs from variable names to their values.
Keyword arguments:
- :timeout <number> - the sequence ends prematurely if the timer exceeds a certain number of milliseconds.
- :maximize <var> - finds all solutions that maximize the given var or expression. NOT lazy.
- :minimize <var> - finds all solutions that minimize the given var or expression. NOT lazy."
  ([problem] (solve problem {}))
  ([problem args]
   (let [strategies (:strategies args)
         solver (problem->solver problem strategies)
         ^Model model (:model solver)
         ^Solver csolver (.getSolver model)
         timeout (:timeout args)
         maximize (:maximize args)
         minimize (:minimize args)]
     (when timeout
       (.limitTime ^Solver csolver ^long timeout))
     (cond
       maximize
       (do (.setObjective model Model/MAXIMIZE
                          (->choco solver maximize))
           (last (solutions solver)))
       
       minimize
       (do (.setObjective model Model/MINIMIZE
                          (->choco solver minimize))
           (last (solutions solver)))
       
       :else (solutions solver)))))

