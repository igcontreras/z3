;; iuc: a != d && b = c


;; propagation from the EUF solver is required, conflict in one literal
(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

(declare-const tr Bool)

;; B
(assert (and (= b c) (= c d) (not (= a d))))


;; A
(assert (or (= a d) (not (= b c))))
