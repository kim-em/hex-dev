import HexPolyDetMathlib

open Matrix

private theorem result (x : Int) : Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = x^2-1 := by
  det

#print axioms result
