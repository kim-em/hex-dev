import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

private def certificate : {d : Int // Matrix.det (!![(1 : Int), 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [norm_det]
  rfl

#print axioms certificate
