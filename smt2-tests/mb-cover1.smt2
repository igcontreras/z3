(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(mb-cover ((= a b) (= c a)) (a))
(mb-cover ((= a b) (= a d)) (d))
(mb-cover ((= a b) (= a (f d))) (d))

(declare-const x Int)
(declare-const y Int)
(mb-cover ((= x (f x)) (= (f x) (f y))) (x a)) ;; y = f(y)
(mb-cover ((= x 3)) (x)) ;; true
(mb-cover ((= x 3)) (y)) ;; x = 3
(mb-cover ((= x (+ y d)) (= a (+ y d))) (y)) ;; x = y
(mb-cover ((= x 3) (= y (f x))) (x)) ;; y = f(3)
(mb-cover ((= x 3) (= y (g x a))) (x)) ;; y = g(3,a)
(mb-cover ((= x 3) (= y (g x x))) (x)) ;; y = g(3,3)
(mb-cover ((= x 3) (= b a) (= y (g b x))) (x b)) ;; y = g(a,3)

(declare-const z Int)
(declare-const e1 Int)
(declare-const e2 Int)
(declare-const e3 Int)
(declare-const e4 Int)
(declare-fun f (Int Int Int) Int)
;; equalities with functions this example is to simulate a merge after split
;; decision (the last equality literal is the decision)
(mb-cover ((= z (f e1 x y)) (= c e2) (= e4 (f a e2 e3)) (= z e4)) (e1 e2 e3 e4))


;; --------------------------------------------------
;; Ghilardi et. al example
;; --------------------------------------------------
(declare-const z0 Int)
(declare-const z1 Int)
(declare-const z2 Int)
(declare-const z3 Int)
(declare-const z4 Int)
(declare-const e Int)
(declare-fun h (Int) Int)
(declare-fun f (Int Int) Int)
(mb-cover ((= (g z4 e) z0) (= (f z2 e) (g z3 e)) (= (h (f z1 e)) z0)) (e))
