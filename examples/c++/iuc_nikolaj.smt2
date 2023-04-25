;; IUC

;; nikolaj's original example requires search!, needs to be adapted
(declare-fun f (Int) Int)
(declare-const z Int)

; B
(assert (and (not (= (f (f (f (f (f (f z)))))) z))))

; A
(assert (or (= (f (f (f z))) z) (= (f (f z)) z)))
