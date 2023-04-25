;; iuc (= b (f1 l)) (= (f g) (f h))

;; colorable two congruence with shared argument
(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)
(declare-const e A)
(declare-const f A)
(declare-const g A)
(declare-const h A)
(declare-const i A)
(declare-const j A)
(declare-const l A)

(declare-fun f1 (A) A)

; B
(assert (and (= b (f1 l)) (= g h)))

; A
(assert (and (= a (f1 g)) (= h l)  (not (= a b))))
