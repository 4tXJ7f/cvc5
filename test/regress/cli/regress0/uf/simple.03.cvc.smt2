; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun x () A)
(declare-fun y () A)
(declare-fun a () A)
(declare-fun b () A)
(declare-fun f (A) B)
(assert (or (and (= x a) (= y a)) (and (= x b) (= y b))))
(check-sat-assuming ( (not (= (f x) (f y))) ))