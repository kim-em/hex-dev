/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPosDef
import HexMatrix.Notation

/-! Independent certificate, producer, malformed-data, and Gaussian conjugation checks. -/

open Hex.PosDef

#guard (Int.certify (Hex.Matrix.ofFn fun (_ _ : Fin 0) => (0 : Int))).toOption =
  some (.positive (.triangular []))
#guard (Int.certify #m[(2 : Int), 1; 1, 2]).toOption =
  some (.positive (.triangular [[1], [-1, 2]]))
#guard (Int.certify #m[(2 : Int), 0; 0, 3]).toOption =
  some (.positive (.triangular [[1], [0, 1]]))
#guard (Int.certify #m[(1 : Int), 2; 2, 1]).toOption =
  some (.negative (.nonpositive [-2, 1]))
#guard (Int.certify #m[(0 : Int), 1; 1, 0]).toOption =
  some (.negative (.nonpositive [1, 0]))
#guard (Int.certify #m[(1 : Int), 2; 0, 1]).toOption =
  some (.negative (.notHermitian 0 1))
#guard (Int.certify #m[(2 : Int), -1; -1, 2] .positiveVector).isOk
#guard match Int.certify #m[(2 : Int), 1; 1, 2] .positiveVector with
  | .error (.unsupported _) => true
  | _ => false
#guard match Int.certify #m[(0 : Int)] .positiveVector with
  | .error (.unsupported _) => true
  | _ => false

#guard Int.checkPositive 2 [[2, -1], [-1, 2]] (.positiveVector [2, 3])
#guard !Int.checkPositive 2 [[2, -1], [-1, 2]] (.positiveVector [0, 3])
#guard !Int.checkPositive 2 [[2, 1], [1, 2]] (.triangular [[1], [1, 2]])
#guard !Int.checkPositive 2 [[2, 1], [1, 2]] (.triangular [[1], [-1]])
#guard !Int.checkPositive 2 [[2, 1], [1]] (.triangular [[1], [-1, 2]])
#guard !Int.checkNegative 2 [[1, 2], [2, 1]] (.nonpositive [0, 0])
#guard !Int.checkNegative 2 [[1, 2], [2, 1]] (.nonpositive [1])
#guard !Int.checkNegative 2 [[1, 2], [2, 1]] (.notHermitian 2 0)
#guard !Int.checkNegative 2 [[1, 2], [2, 1]] (.notHermitian 0 1)
#guard !Int.checkNegative 1 [[1]] (.nonpositive [1])

private def hermitian (d : Int) : Hex.Matrix Gaussian 2 2 :=
  #m[⟨d, 0⟩, ⟨0, 1⟩; ⟨0, -1⟩, ⟨d, 0⟩]

#guard (Gaussian.certify (hermitian 2)).toOption =
  some (.positive (.triangular [[⟨1, 0⟩], [⟨0, 1⟩, ⟨2, 0⟩]]))
#guard (Gaussian.certify (hermitian 1)).toOption =
  some (.negative (.nonpositive [⟨0, -1⟩, ⟨1, 0⟩]))
#guard !Gaussian.checkNegative 2 [[⟨1, 0⟩, ⟨0, 1⟩], [⟨0, -1⟩, ⟨1, 0⟩]]
  (.nonpositive [⟨0, 1⟩, ⟨1, 0⟩])
#guard (Gaussian.certify #m[(⟨0, 1⟩ : Gaussian)]).toOption =
  some (.negative (.notHermitian 0 0))
#guard !Gaussian.checkPositive 0 [] (.positiveVector [])
#guard Gaussian.scaleRows 6 [[(1/2, 1/3)]] [[⟨3, 2⟩]]
#guard !Gaussian.scaleRows 6 [[(1/2, 1/3)]] [[⟨3, -2⟩]]

#guard (Gaussian.certify #m[(⟨3, 0⟩ : Gaussian), ⟨0, 1⟩, ⟨0, 0⟩;
    ⟨0, -1⟩, ⟨3, 0⟩, ⟨0, 1⟩; ⟨0, 0⟩, ⟨0, -1⟩, ⟨3, 0⟩]).toOption =
  some (.positive (.triangular [[⟨1, 0⟩], [⟨0, 1⟩, ⟨3, 0⟩], [⟨-1, 0⟩, ⟨0, 3⟩, ⟨8, 0⟩]]))
#guard !Gaussian.checkPositive 2 [[⟨2, 0⟩, ⟨0, 1⟩], [⟨0, -1⟩, ⟨2, 0⟩]]
  (.triangular [[⟨1, 0⟩], [⟨0, -1⟩, ⟨2, 0⟩]])
