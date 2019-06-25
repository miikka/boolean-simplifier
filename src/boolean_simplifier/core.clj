(ns boolean-simplifier.core
  "Simplify your Boolean expressions."
  (:require [clojure.set :as set]))

(defn get-tag
  "Dispatch function for Boolean expressions."
  [x]
  (if (vector? x) (first x) x))

(defn- xnot [x]
  (if (= :not (get-tag x))
    (second x)
    [:not x]))

(defmulti ^:private clause->facts get-tag)

(defmethod clause->facts :default [x] [x])

(defmethod clause->facts :and [[_ & args]]
  (mapcat clause->facts args))

(defmethod clause->facts :or [[_ & args]]
  (let [args (into #{} (mapcat clause->facts) args)]
    (if (= 1 (count args))
      args
      [[:or args]])))

(defn- known? [env x]
  (set/subset? (into #{} (clause->facts x)) env))

(defn- add-facts [env xs]
  (into env (mapcat clause->facts) xs))

(defmulti ^:private simplify-clause (fn [_env x] (get-tag x)))

(defmethod simplify-clause :default [env x]
  (cond
    (known? env x) true
    (known? env (xnot x)) false
    true x))

(defmethod simplify-clause :and [env [op & args]]
  (let [args (->> (map-indexed #(simplify-clause (add-facts env (take %1 args)) %2) args)
                  (remove true?))
        term (into [op] args)]
    (cond
      (empty? args) true
      (= 1 (count args)) (first args)
      (contains? (into #{} args) false) false
      true term)))

(defmethod simplify-clause :or [env [op & args]]
  (let [args (->> args
                  (map-indexed #(simplify-clause (add-facts env (map xnot (take %1 args))) %2))
                  (remove false?))
        term (into [op] args)]
    (cond
      (empty? args) false
      (= 1 (count args)) (first args)
      (contains? (into #{} args) true) true
      (known? env term) true
      true term)))

(defn simplify
  "Given a Boolean expression x, return an equivalent but possibly simpler
  Boolean expression."
  [x]
  (simplify-clause #{} x))
