import HexPolyDetMathlib

open Matrix

private theorem result (a b c d u v w x : Rat) : Matrix.det (!![a/u, b/v; c/w, d/x] : Matrix (Fin 2) (Fin 2) Rat) = a*d/(u*x)-b*c/(v*w) := by
  det

#print axioms result
