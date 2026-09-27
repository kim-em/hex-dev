import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

private def certificate (x : Int) : {d : Int // Matrix.det (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [norm_det]
  rfl

#print axioms certificate
