/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

namespace HexPrimalityMathlib.ProofProbe

/-! End-to-end Mathlib elaboration at the exact 512-bit policy ceiling. The
above-table factor `100297` forces the accepted route through bounded rho. -/

theorem mathlib512 : Nat.Prime 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177 := by
  primality

#print axioms mathlib512

end HexPrimalityMathlib.ProofProbe
