/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.FactorizationResult

public section
set_option backward.proofsInPublic true

/-!
# Primitive square-free factorization problems

Both modular paths are indexed by the square-free part produced by
normalization. A plan or lift for one square-free part therefore cannot be paired with a
different polynomial.
-/

namespace Hex

/-- A square-free part presented to classical factorization.
The executable layer stores the polynomial; the Mathlib correctness layer
supplies and retains the normalization invariants. -/
structure SquareFreeInput where
  /-- The square-free part to be factored. -/
  poly : ZPoly
deriving DecidableEq

namespace SquareFreeInput

/-- Package the primitive square-free part produced by the common normalization pass. -/
@[expose]
def ofNormalized (normalized : FactorNormalizationData) : SquareFreeInput :=
  ⟨normalized.squareFreeCore⟩

end SquareFreeInput

end Hex
