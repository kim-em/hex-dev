/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.ReassemblyProofs

public section
set_option backward.proofsInPublic true

/-!
# Primitive square-free factorization problems

Both modular paths are indexed by the primitive square-free core produced by
normalization. A plan or lift for one core therefore cannot be paired with a
different polynomial.
-/

namespace Hex

/-- A primitive square-free polynomial presented to the classical engine.
The executable layer stores the polynomial; the Mathlib correctness layer
supplies and retains the normalization invariants. -/
structure CoreProblem where
  poly : ZPoly
deriving DecidableEq

namespace CoreProblem

/-- Package the square-free core produced by the common normalization pass. -/
@[expose]
def ofNormalized (normalized : FactorNormalizationData) : CoreProblem :=
  ⟨normalized.squareFreeCore⟩

end CoreProblem

end Hex
