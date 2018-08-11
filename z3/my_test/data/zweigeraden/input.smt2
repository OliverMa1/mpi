;;Declare variables, variables for edges, variables for additional exprs
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const x_dash Int)
(declare-const y_dash Int)
(declare-const z_dash Int)
(declare-const x+y Int)
(declare-const x-y Int)
;; Initial Condition
(assert (and(= z 0)(and(>= y (- x 2)) (<= y (+ x 2)))))
;; Safe Condition
(assert (and(>= y (- x 2)) (<= y (+ x 2))))
;; Player 0 
(assert (= z 0))
;; Player 1
(assert (= z 1))
;; Edge Relation
(assert(and(and(or(or(= x (+ x_dash 1)) (= x (- x_dash 1))) (= x x_dash))(or(or(= y (+ y_dash 1)) (= y (- y_dash 1))) (= y y_dash)))
(= z (- 1 z_dash))))
;; one expr per assert
(assert(= 1 (+ x y)))
(assert(= 0 (- x y)))
