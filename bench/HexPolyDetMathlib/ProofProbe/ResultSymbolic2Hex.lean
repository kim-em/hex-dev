import HexPolyDetMathlib

open Matrix

private def certificate (x : Int) : {d : Int // Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  let c := det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int)
  exact ⟨c.value, c.proof⟩

#print axioms certificate
