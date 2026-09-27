import HexPolyDetMathlib

open Matrix

private theorem result {R : Type} [CommRing R] (a b c d e f g h i j k l : R) : Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; a+e, b+f, c+g, d+h] = 0 := by
  det

#print axioms result
