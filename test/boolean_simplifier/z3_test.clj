(ns boolean-simplifier.z3-test
  (:require [backtick :refer [template]]
            [boolean-simplifier.core :as bs]
            [clojure.java.shell :refer [sh]]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.spec.alpha :as spec]
            [clojure.set :as set])
  (:import java.io.File))

(defmulti collect-vars bs/get-tag)
(defmethod collect-vars :default [x] [x])
(defmethod collect-vars true [_] nil)
(defmethod collect-vars false [_] nil)
(defmethod collect-vars :and [[_ & args]] (mapcat collect-vars args))
(defmethod collect-vars :or [[_ & args]] (mapcat collect-vars args))
(defmethod collect-vars :not [[_ arg]] (collect-vars arg))

(defmulti z3-expr bs/get-tag)

(defmethod z3-expr :default [x] (symbol x))
(defmethod z3-expr true [_] true)
(defmethod z3-expr false [_] false)

(defmethod z3-expr :and [[_ & args]]
  (template (and ~@(map z3-expr args))))

(defmethod z3-expr :or [[_ & args]]
  (template (or ~@(map z3-expr args))))

(defmethod z3-expr :not [[_ arg]]
  (template (not ~(z3-expr arg))))

(defn z3-equality-check
  [x y]
  (let [vars (set (collect-vars x))]
    (assert (set/subset? (set (collect-vars y)) vars))
    (template
     [~@(for [var vars]
          (template (declare-const ~(z3-expr var) Bool)))

      (define-fun conj1 () Bool
        ~(z3-expr x))

      (define-fun conj2 () Bool
        ~(z3-expr y))

      (assert (not (= conj1 conj2)))
      (check-sat)])))

(defn z3->str [expr-vec]
  (str/join "\n" (map str expr-vec)))

(defn z3-check
  "Check using z3 that two Boolean expressions are equal."
  [x y]
  (let [tempfile (File/createTempFile "boolean_simplifier" ".z3")]
    (.deleteOnExit tempfile)
    (with-open [file (io/writer tempfile)]
      (binding [*out* file]
        (println (z3->str (z3-equality-check x y)))))
    (let [{:keys [exit out]} (sh "z3" (.getAbsolutePath tempfile))
          result (str/trim out)]
      (if (zero? exit)
        (do
          (assert (zero? exit) (str exit))
          (assert (contains? #{"sat" "unsat"} result))
          (= "unsat" result))
        (do
          (println "#### GENERATED Z3 CODE ####")
          (println (slurp (.getAbsolutePath tempfile)))
          (println "###########################")
          (println "#### STDOUT ####")
          (println out)
          (println "################")
          false)))))

(def +scalars+ (into [true false] (map #(str "var" %) (range 10))))

(defn and-or-not-gen [inner-gen]
  (gen/one-of [(gen/fmap #(into [:and] %) (gen/vector inner-gen 1 5))
               (gen/fmap #(into [:or] %) (gen/vector inner-gen 1 5))
               (gen/fmap (fn [x] [:not x]) inner-gen)]))

(def expr-gen
  (gen/recursive-gen and-or-not-gen (gen/elements +scalars+)))

(defspec expression-equality
  100
  (prop/for-all [x expr-gen]
    (z3-check x (bs/simplify x))))
