;; iuc (not (= a d))


;; simple boolean propagation (not coming back from the euf solver)
(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

(declare-const tr Bool)

;; B
(assert (and (= b c) (= c d) (not (= a d))))


;; A
(assert (or (not tr) (= a b)))
(assert (and tr))
