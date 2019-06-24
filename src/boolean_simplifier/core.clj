(ns boolean-simplifier.core)

(defn get-tag [x] (if (vector? x) (first x) x))

(defn xnot [x]
  (if (= :not (get-tag x))
    (second x)
    [:not x]))

(defn known? [env x] (contains? env x))

(defmulti clause->facts get-tag)

(defmethod clause->facts :default [x] [x])

(defmethod clause->facts :and [[_ & args]]
  (mapcat clause->facts args))

(defmethod clause->facts :or [[_ & args]]
  [:or (into #{} (mapcat clause->facts) args)])

(defn add-facts [env xs]
  (into env (mapcat clause->facts) xs))

(defmulti simplify-clause (fn [_env x] (get-tag x)))

(defmethod simplify-clause :default [env x]
  (cond
    (known? env x) true
    (known? env (xnot x)) false
    true x))

(defmethod simplify-clause :and [env [op & args]]
  (let [args (->> (map-indexed #(simplify-clause (add-facts env (take %1 args)) %2) args)
                  (remove true?))]
    (cond
      (empty? args) true
      (= 1 (count args)) (first args)
      (contains? (into #{} args) false) false
      true (into [op] args))))

(defmethod simplify-clause :or [env [op & args]]
  (let [args (->> args
                  (map-indexed #(simplify-clause (add-facts env (map xnot (take %1 args))) %2))
                  (remove false?))
        argset (into #{} args)]
    (cond
      (empty? args) false
      (= 1 (count args)) (first args)
      (contains? (into #{} args) true) true
      true (into [op] args))))

(defn simplify [x]
  (simplify-clause #{} x))
