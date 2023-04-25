;; iuc (= a (f1 i)) (not (= a b))

(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

(declare-const i A)
(declare-const j A)

(declare-fun f1 (A) A)

; B
(assert (and (= b (f1 j)) (= i j) (not (= a b))))

; A
(assert (= a (f1 i)))
