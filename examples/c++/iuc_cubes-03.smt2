;; iuc (not (= b a))

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

;; B
(assert (and (= b c) (= c d) (not (= a d))))

;; A
(assert (and (= a b)))
