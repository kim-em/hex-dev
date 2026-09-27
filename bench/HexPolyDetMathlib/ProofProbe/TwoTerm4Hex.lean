import HexPolyDetMathlib

open Matrix

private theorem result (a b u : Rat) : Matrix.det !![(a+b)/u, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = (a+b)/u := by
  det

#print axioms result
