import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

private theorem result (x : Int) : Matrix.det !![1 + 1*x, 2*x, 3*x, 4*x, 5*x; 2*x, 1 + 4*x, 6*x, 8*x, 10*x; 3*x, 6*x, 1 + 9*x, 12*x, 15*x; 4*x, 8*x, 12*x, 1 + 16*x, 20*x; 5*x, 10*x, 15*x, 20*x, 1 + 25*x] = 1+55*x := by
  simp only [norm_det] <;> ring

#print axioms result
