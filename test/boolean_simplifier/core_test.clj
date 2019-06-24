(ns boolean-simplifier.core-test
  (:require [boolean-simplifier.core :as bs]
            [clojure.test :refer [deftest]]
            [testit.core :refer [facts =>]]))

(deftest simplify-test
  (facts
   (bs/simplify '[:and int? [:and int? pos?]]) => '[:and int? pos?]
   (bs/simplify '[:and [:and int? pos?] int?]) => '[:and int? pos?]
   (bs/simplify '[:and zero? [:not zero?]]) => false
   (bs/simplify '[:and [:not zero?] zero?]) => false
   (bs/simplify '[:or zero? [:not zero?]]) => true
   (bs/simplify '[:or [:not zero?] zero?]) => true
   (bs/simplify '[:and [:or int?] int?]) => 'int?))
