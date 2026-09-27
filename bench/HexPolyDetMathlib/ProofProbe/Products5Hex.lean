import HexPolyDetMathlib

open Matrix

private theorem result (a b c d u v w z : Rat) : Matrix.det !![a*c/(u*w), a*d/(u*z), 0, 0, 0; b*c/(v*w), b*d/(v*z), 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] = 0 := by
  det

#print axioms result
