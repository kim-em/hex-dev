import HexPolyDetMathlib
import HexPolyDetMathlib.ProofProbe.GeneralSupport

open Matrix

private theorem result (x : Int) : Matrix.det (HexPolyDetMathlib.ProofProbe.quadratic x) = x^4-3*x^2+1 := by
  det

#print axioms result
