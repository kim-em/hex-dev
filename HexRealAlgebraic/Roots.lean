/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Order
public import HexNumberField.Radical

public section

/-! Real polynomials, sorted roots with multiplicities, and square roots. -/

namespace Hex

/-- A normalized canonical algebraic polynomial with real coefficients. -/
@[expose] def RealAlgebraicPoly :=
  {f : AlgebraicPoly // ∀ a ∈ f.coeffs, a.isReal = true}

namespace RealAlgebraicPoly

/-- The existing normalized algebraic polynomial. -/
@[expose] def toAlgebraic (f : RealAlgebraicPoly) : AlgebraicPoly := f.val

/-- Normalize a real coefficient array with the canonical polynomial normalizer. -/
@[expose] def ofArray (coeffs : Array RealAlgebraicNumber) : RealAlgebraicPoly :=
  ⟨AlgebraicPoly.ofArray (coeffs.map RealAlgebraicNumber.toAlgebraic), by
    intro a ha
    rw [AlgebraicPoly.coeffs_ofArray] at ha
    rw [Array.popWhile_map] at ha
    obtain ⟨b, _, rfl⟩ := Array.mem_map.mp ha
    exact b.property⟩

/-- Check every stored coefficient, rejecting polynomials with nonreal coefficients. -/
@[expose] def ofAlgebraic? (f : AlgebraicPoly) : Option RealAlgebraicPoly :=
  if h : f.coeffs.all AlgebraicNumber.isReal = true then
    some ⟨f, Array.all_eq_true_iff_forall_mem.mp h⟩
  else none

/-- Checked conversion succeeds exactly when every coefficient is real. -/
theorem ofAlgebraic?_isSome (f : AlgebraicPoly) :
    (ofAlgebraic? f).isSome = true ↔ ∀ a ∈ f.coeffs, a.isReal = true := by
  unfold ofAlgebraic?
  split
  · rename_i h
    constructor
    · intro _
      exact Array.all_eq_true_iff_forall_mem.mp h
    · intro _
      rfl
  · rename_i h
    constructor
    · intro hfalse
      cases hfalse
    · intro hr
      exact False.elim (h (Array.all_eq_true_iff_forall_mem.mpr hr))

end RealAlgebraicPoly

/-- A canonical real root with its positive polynomial multiplicity. -/
structure RealRootCount where
  /-- The canonical real value. -/
  root : RealAlgebraicNumber
  /-- Its multiplicity in the polynomial. -/
  multiplicity : Nat
  /-- Only positive multiplicities are stored. -/
  multiplicity_pos : 0 < multiplicity

/-- Real roots of a polynomial, retaining the universal root set of zero. -/
inductive RealRootSet where
  /-- Every real algebraic number is a root. -/
  | all
  /-- Distinct increasing roots with positive multiplicities. -/
  | finite (roots : Array RealRootCount)

namespace RealRootSet

/-- Finite roots, with zero-polynomial roots represented by none. -/
@[expose] def finite? : RealRootSet → Option (Array RealRootCount)
  | .all => none
  | .finite roots => some roots

/-- The finite entries; callers needing universal membership must inspect finite?. -/
@[expose] def toArray (roots : RealRootSet) : Array RealRootCount :=
  roots.finite?.getD #[]

/-- Membership, including the universal root set. -/
@[expose] def contains (roots : RealRootSet) (a : RealAlgebraicNumber) : Bool :=
  match roots with
  | .all => true
  | .finite roots => roots.any fun r => r.root == a

end RealRootSet

namespace RealAlgebraicPoly

/-- Exactify and retain a lazy root precisely when it is real, preserving multiplicity. -/
@[expose] def realRoot? (r : RootCount) : Option RealRootCount := do
  let a ← RealAlgebraicNumber.ofRoot? r.root
  return ⟨a, r.multiplicity, r.multiplicity_pos⟩

/-- Extract real roots from an existing root set and sort by exact value. -/
@[expose] def realRoots : RootSet → RealRootSet
  | .all => .all
  | .finite roots => .finite
    (((roots.filterMap realRoot?).toList.mergeSort
      (fun a b => decide (a.root ≤ b.root))).toArray)

/-- Real roots in increasing order, with multiplicities and the zero case preserved. -/
@[expose] def roots (f : RealAlgebraicPoly) : RealRootSet :=
  realRoots f.toAlgebraic.roots

end RealAlgebraicPoly

/-- Distinct real roots of an integer polynomial, sorted by exact comparison.
Every constant, including zero, inherits the empty-array convention. -/
@[expose] def ZPoly.realAlgebraicRoots (p : ZPoly) : Array RealAlgebraicNumber :=
  (((p.algebraicRoots.filterMap RealAlgebraicNumber.ofAlgebraic?).toList.mergeSort
    (fun a b => decide (a ≤ b))).toArray)

namespace RealAlgebraicNumber

/-- Select the unique nonnegative root of the square-root polynomial. -/
@[expose] def sqrtRoot? (a : RealAlgebraicNumber) : Option RealAlgebraicNumber :=
  if a < 0 then none else ofAlgebraic? a.toAlgebraic.sqrt

/-- Return the nonnegative square root, or none for a negative argument. -/
@[expose] def sqrt? (a : RealAlgebraicNumber) : Option RealAlgebraicNumber :=
  if a < 0 then none else sqrtRoot? a

/-- Square root of a nonnegative argument. The companion proves selection succeeds,
so the fallback is unreachable-by-pipeline-invariant under the supplied hypothesis. -/
@[expose] def sqrt (a : RealAlgebraicNumber) (_h : 0 ≤ a) : RealAlgebraicNumber :=
  a.sqrt?.getD (Hex.panicWith zero "RealAlgebraicNumber.sqrt: nonnegative root not found")

end RealAlgebraicNumber
end Hex
