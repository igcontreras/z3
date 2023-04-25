;; iuc: B

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

;; B
(assert (and (= a b) (= c d)))

;; A
(assert (= b c))
(assert (not (= a d)))
