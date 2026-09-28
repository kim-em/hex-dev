/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.Interpret

public section

namespace Hex.RealClosure

variable {E : Type u} [Zero E] [DecidableEq E] [One E]
variable [Add E] [Sub E] [Mul E] [Div E]

/-- The linear factor for a root in the coefficient field. -/
@[expose] def linear (root : E) : DensePoly E :=
  DensePoly.ofCoeffs #[0, 1] - DensePoly.C root

/-- Exact removal of one linear factor from this stored nonzero polynomial.
Squarefreeness, when available, makes the removed point root-free for the
quotient. Old descriptors and root counts must be recomputed or transported. -/
structure Deflation (p : DensePoly E) (root : E) where
  private mk ::
  quotient : DensePoly E
  nonzero : p ≠ 0
  divided : DensePoly.divMod p (linear root) = (quotient, 0)

/-- Remove a linear factor only when the shared division returns zero remainder.
Failure means that the input is zero or the supplied point is not a root under
the coefficient interpretation; it never discards a nonzero remainder. -/
def deflate? (p : DensePoly E) (root : E) : Option (Deflation p root) :=
  if hp : p = 0 then none else
    let qr := DensePoly.divMod p (linear root)
    if hr : qr.2 = 0 then
      some ⟨qr.1, hp, Prod.ext rfl hr⟩
    else none

/-- Successful deflation retains the quotient already computed by division. -/
theorem deflate?_quotient {p : DensePoly E} {root : E} {d : Deflation p root}
    (h : deflate? p root = some d) :
    d.quotient = (DensePoly.divMod p (linear root)).1 := by
  unfold deflate? at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases Option.some.inj h
      rfl
    · cases h

/-- Every successful exact division produces the opaque witness. -/
theorem deflate?_isSome (p : DensePoly E) (root : E) :
    (deflate? p root).isSome = true ↔
      p ≠ 0 ∧ (DensePoly.divMod p (linear root)).2 = 0 := by
  unfold deflate?
  split <;> simp_all

end Hex.RealClosure
