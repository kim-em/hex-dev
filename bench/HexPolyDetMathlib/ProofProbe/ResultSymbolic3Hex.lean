import HexPolyDetMathlib

open Matrix

private def certificate (x : Int) : {d : Int // Matrix.det (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int) = d} := by
  let c := det% (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int)
  exact ⟨c.value, c.proof⟩

#print axioms certificate
