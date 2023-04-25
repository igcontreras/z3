;; iuc a = c

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

;; B
(assert (and (= a b) (= b c)))

;; A
(assert (and (= c d) (not (= a d))))
