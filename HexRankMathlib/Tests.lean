/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRank
import HexRankMathlib
import HexMatrix.Notation

/-! Build-only examples: a hand-written certificate discharged in the kernel,
the integer producer, the `Decidable` instance, and the scalar-extension
theorem at the two fraction-field instances a consumer meets. -/

open Hex Hex.Matrix HexMatrixMathlib
open scoped Hex

/-- A `3 × 4` integer matrix of rank `2`. -/
def rankTestMatrix : Hex.Matrix Int 3 4 := #m[1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]

/-- A hand-written certificate for it. -/
def rankTestCert : RankCert Int 3 4 :=
  ⟨2, #v[0, 2], #v[0, 1], -2, #m[0, -2; -1, 1]⟩

example : (matrixEquiv rankTestMatrix).rank = 2 :=
  checkRank_sound (A := rankTestMatrix) (c := rankTestCert) (by decide +kernel)

example : (matrixEquiv rankTestMatrix).rank = 2 :=
  (rank_eq rankTestMatrix).symm.trans (by decide +kernel)

example : (matrixEquiv rankTestMatrix).rank = 2 := by decide +kernel

example (M : Matrix (Fin 3) (Fin 4) ℤ) : (M.map (algebraMap ℤ ℚ)).rank = M.rank :=
  rank_map_eq M

example (M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    (M.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = M.rank :=
  rank_map_eq M

example [CommRing R] [IsDomain R] [DecidableEq R] (A : Hex.Matrix R 2 2) :
    ∃ c : RankCert R 2 2, checkRank A c = true :=
  exists_rankCert A
