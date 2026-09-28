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
variable [Add E] [Sub E] [Mul E]

/-- The linear factor for a root in the coefficient field. -/
@[expose] def linearFactor (root : E) : DensePoly E :=
  DensePoly.ofCoeffs #[0 - root, 1]

omit [Add E] [Mul E] in
/-- Literal leading one makes the shared monic division available on raw
coefficient representations. No additive or multiplicative laws are needed. -/
theorem linearFactor_monic (root : E) (hone : (1 : E) ≠ 0) :
    (linearFactor root).Monic := by
  have hc : (linearFactor root).coeff 1 = 1 := by
    simp [linearFactor, DensePoly.coeff_ofCoeffs]
  have hle : (linearFactor root).size ≤ 2 :=
    DensePoly.size_ofCoeffs_le #[0 - root, 1]
  have hpos : 1 < (linearFactor root).size := by
    by_cases h : 1 < (linearFactor root).size
    · exact h
    · have hz := DensePoly.coeff_eq_zero_of_size_le (linearFactor root) (by omega :
        (linearFactor root).size ≤ 1)
      exact False.elim (hone (hc.symm.trans hz))
  have hsize : (linearFactor root).size = 2 := by omega
  change (linearFactor root).leadingCoeff = 1
  rw [DensePoly.leadingCoeff_eq_coeff_last _ (by omega), hsize]
  exact hc

/-- Exact removal of one linear factor from this stored nonzero polynomial.
Squarefreeness, when available, makes the removed point root-free for the
quotient. Old descriptors and root counts must be recomputed or transported. -/
structure Deflation (p : DensePoly E) (root : E) where
  private mk ::
  quotient : DensePoly E
  nonzero : p ≠ 0
  monic : (linearFactor root).Monic
  divided : DensePoly.divModMonic p (linearFactor root) monic = (quotient, 0)

/-- Remove a linear factor only when the shared monic division returns zero remainder.
Failure means that the input is zero or the supplied point is not a root under
the coefficient interpretation; it never discards a nonzero remainder.
The finite monicity check is proved to pass under that interpretation. -/
def deflate? (p : DensePoly E) (root : E) : Option (Deflation p root) :=
  if hp : p = 0 then none else
    if hm : (linearFactor root).leadingCoeff = 1 then
      let qr := DensePoly.divModMonic p (linearFactor root) hm
      if hr : qr.2 = 0 then
        some ⟨qr.1, hp, hm, Prod.ext rfl hr⟩
      else none
    else none

/-- Successful deflation retains the quotient already computed by division. -/
theorem deflate?_quotient {p : DensePoly E} {root : E} {d : Deflation p root}
    (h : deflate? p root = some d) :
    d.quotient = (DensePoly.divModMonic p (linearFactor root) d.monic).1 := by
  unfold deflate? at h
  split at h
  · cases h
  · split at h
    · dsimp only at h
      split at h
      · cases Option.some.inj h
        rfl
      · cases h
    · cases h

/-- Every successful exact division produces the opaque witness. -/
theorem deflate?_isSome (p : DensePoly E) (root : E) (hq : (linearFactor root).Monic) :
    (deflate? p root).isSome = true ↔
      p ≠ 0 ∧ (DensePoly.divModMonic p (linearFactor root) hq).2 = 0 := by
  have hm : (linearFactor root).leadingCoeff = 1 := hq
  unfold deflate?
  split <;> simp_all

end Hex.RealClosure
