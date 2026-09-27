import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

private def certificate (x : Int) : {d : Int // Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [norm_det]
  rfl

#print axioms certificate
