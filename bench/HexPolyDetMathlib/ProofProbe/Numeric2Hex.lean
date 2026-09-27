import HexPolyDetMathlib

open Matrix

private theorem result : Matrix.det (!![(1 : Int), 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) = -2 := by
  det

#print axioms result
