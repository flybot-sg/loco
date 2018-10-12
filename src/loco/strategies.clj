(ns loco.strategies
  "Search strategies"
  (:require
   [loco.core :refer [->choco*]])
  (:import
   [org.chocosolver.solver.variables IntVar]
   [org.chocosolver.solver.search.strategy Search]
   [org.chocosolver.solver.search.strategy.selectors.values
    IntDomainMin]
   [org.chocosolver.solver.search.strategy.selectors.variables
    FirstFail]))

(defn- grab-choco-variables
  "Takes a list of variables or :all, returns the Choco variable objects in a IntVar array"
  [solver selector]
  (let [var-map @(:my-vars solver)]
    (into-array
     IntVar
     (if (= :all selector)
       (vals var-map)
       (for [var-name selector]
         (or (var-map var-name)
             (throw (IllegalArgumentException.
                     (str "Var name " var-name
                          " used in strategy but not declared in constraint model")))))))))

(defn min-dom-lb-search
  "Create min Dom LB search strategy"
  [& {:keys [vars] :as opts}]
  {:type :min-dom-lb-search
   :opts opts})

(defmethod ->choco* :min-dom-lb-search
  [solver {{:keys [vars]} :opts}]
  (Search/minDomLBSearch
   (grab-choco-variables solver (or vars :all))))

(defn int-var-search-first-fail-with-domain-min
  [& {:keys [vars] :as opts}]
  {:type :int-var-search-first-fail-with-domain-min
   :opts opts})

(defmethod ->choco* :int-var-search-first-fail-with-domain-min
  [solver {{:keys [vars]} :opts}]
  (Search/intVarSearch
   (FirstFail. (:model solver))
   (IntDomainMin.)
   (grab-choco-variables solver (or vars :all))))
