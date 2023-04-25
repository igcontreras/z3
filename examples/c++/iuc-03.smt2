;; iuc: the whole B is necessary (no implication because f1 is in the shared language)

;; got inconsistent egraph with this one!!

;; two steps of propagation between sat and euf solver
(declare-sort A)
(declare-const a A)
(declare-const b A)
(declare-const c A)
(declare-const d A)

(declare-const x A)
(declare-const y A)


(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b4 Bool)

(declare-fun f1 (A) A)

;; B
(assert (and (= x (f1 a)) (= y (f1 b))))


;; A
(assert (or b2 (not (= x y)))) ;; conflict here?
(assert (or (not b1) (not b2)))
(assert (or (not b1) (= a b))) ;; BCP makes a = b true --> propagate to euf solver
(assert (and (not b3) b1))
