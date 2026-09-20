; Manual issue-10301 corpus. See reports/cad-sample-costs.md for the equations.
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (= (+ (* 16 x x) (* (- 8) x) (* 64 y y) (- 3)) 0))
(assert (>= (+ (* x x) (* y y)) 1))
(check-sat-using (then simplify (using-params nlsat :cell_sample false :shuffle_vars false :reorder false :seed 0)))
(get-info :all-statistics)
