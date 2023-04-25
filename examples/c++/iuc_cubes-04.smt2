;; iuc (b = c)

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

(assert (and (= b c) (= c d)))

(assert (and (= a b) (not (= a d))))
