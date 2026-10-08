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
@[expose] noncomputable def realRoots : RootSet → RealRootSet
  | .all => .all
  | .finite roots => .finite
    (((roots.filterMap realRoot?).toList.mergeSort
      (fun a b => decide (a.root ≤ b.root))).toArray)

namespace Internal

/-- Reuse a parent's factorization when exactifying its real entries. Factor
checks and canonical isolation use the existing number-field selector. -/
@[expose] def factorPicker (p : ZPoly) (factors : Factorization)
    (_hfactor : ZPoly.factorize p = factors)
    (fallback : RootCount → Option RealRootCount) (r : RootCount) :
    Option RealRootCount :=
  if p = r.root.p then
    if r.root.isReal then do
      let exact := factors.factors.foldl
        (fun found entry => match found with
          | some a => some a
          | none => r.root.exactFactor? entry.1) none
      let canonical := match exact with
        | some a => a
        | none => Hex.panicWith 0 "AlgebraicRoot.exact: certification failed"
      let a ← RealAlgebraicNumber.ofAlgebraic? canonical
      return ⟨a, r.multiplicity, r.multiplicity_pos⟩
    else none
  else fallback r

set_option backward.isDefEq.respectTransparency false in
/-- Sharing the factor array preserves all checked exactification results. -/
theorem factorPicker_eq (p : ZPoly) (factors : Factorization)
    (hfactor : ZPoly.factorize p = factors) :
    factorPicker p factors hfactor realRoot? = realRoot? := by
  funext r
  unfold factorPicker
  split
  · rename_i hp
    rw [← hfactor, hp]
    change (if r.root.isReal then do
      let a ← RealAlgebraicNumber.ofAlgebraic? (match r.root.exact? with
        | some a => a
        | none => Hex.panicWith 0 "AlgebraicRoot.exact: certification failed")
      pure ⟨a, r.multiplicity, r.multiplicity_pos⟩ else none) = realRoot? r
    unfold realRoot? RealAlgebraicNumber.ofRoot? AlgebraicRoot.exact
    split
    · cases r.root.exact? <;> rfl
    · rfl
  · rfl

/-- Exactify roots of `p` using one certified parent-isolation run. Other
polynomials use the supplied selector; nonreal roots retain early rejection.
Proper irreducible factors still use their own canonical isolation. -/
@[expose] def rootPicker (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (isolations : Array (DyadicRootIsolation p))
    (refined : Array (RefinedIsolation p))
    (hisolate : ZPoly.isolateComplexRoots? p squarefree (separationDepth p : Int) =
      some isolations)
    (hrefine : isolations.mapM DyadicRootIsolation.toRefined? = some refined)
    (fallback : RootCount → Option RealRootCount) (r : RootCount) :
    Option RealRootCount :=
  if hp : p = r.root.p then
    if r.root.isReal then do
      let exact := r.root.exactIn? (hp ▸ isolations) (hp ▸ refined)
        (by cases hp; exact hisolate) (by cases hp; exact hrefine)
      let canonical := match exact with
        | some a => a
        | none => Hex.panicWith 0 "AlgebraicRoot.exact: certification failed"
      let a ← RealAlgebraicNumber.ofAlgebraic? canonical
      return ⟨a, r.multiplicity, r.multiplicity_pos⟩
    else none
  else fallback r

set_option backward.isDefEq.respectTransparency false in
/-- Certified isolation reuse preserves the entire checked selector result. -/
theorem rootPicker_eq (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (isolations : Array (DyadicRootIsolation p))
    (refined : Array (RefinedIsolation p))
    (hisolate : ZPoly.isolateComplexRoots? p squarefree (separationDepth p : Int) =
      some isolations)
    (hrefine : isolations.mapM DyadicRootIsolation.toRefined? = some refined) :
    rootPicker p squarefree isolations refined hisolate hrefine realRoot? = realRoot? := by
  funext r
  unfold rootPicker
  split
  · rw [AlgebraicRoot.exactIn?_eq]
    unfold realRoot? RealAlgebraicNumber.ofRoot? AlgebraicRoot.exact
    split
    · cases r.root.exact? <;> rfl
    · rfl
  · rfl

/-- Share factorization within groups with at least two real entries, and
parent isolation when the factor array contains that parent. Other groups
use the original selector. Return a concrete pair and prevent inlining: returning only a
function lets compiler uncurrying rebuild the cache on every application.
The cache contains functions and polynomial keys, without changing root storage. -/
@[noinline, expose] def rootSelectors (roots : Array RootCount) :
    Array ZPoly × (RootCount → Option RealRootCount) :=
  roots.foldl (fun (state : Array ZPoly × (RootCount → Option RealRootCount)) r =>
    if !r.root.isReal || state.1.contains r.root.p then state
    else
      let seen := state.1.push r.root.p
      if (roots.countP fun s => s.root.isReal && s.root.p == r.root.p) < 2 then
        (seen, state.2)
      else
        let factors := ZPoly.factorize r.root.p
        let fallback := factorPicker r.root.p factors rfl state.2
        if !(factors.factors.any fun entry => entry.1 == r.root.p) then
          (seen, fallback)
        else match hisolate : ZPoly.isolateComplexRoots? r.root.p r.root.squarefree
            (separationDepth r.root.p : Int) with
        | none => (seen, fallback)
        | some isolations =>
          match hrefine : isolations.mapM DyadicRootIsolation.toRefined? with
          | none => (seen, fallback)
          | some refined =>
            (seen, rootPicker r.root.p r.root.squarefree isolations refined
              hisolate hrefine fallback)) (#[], realRoot?)

/-- Every cached selector is identical to independent exactification. -/
theorem rootSelectors_eq (roots : Array RootCount) : (rootSelectors roots).2 = realRoot? := by
  unfold rootSelectors
  apply Array.foldl_induction (as := roots)
    (motive := fun _ (state : Array ZPoly × (RootCount → Option RealRootCount)) =>
      state.2 = realRoot?)
  · rfl
  · intro i state hstate
    dsimp only
    split
    · exact hstate
    · split
      · exact hstate
      · split
        · dsimp only
          rw [hstate]
          exact factorPicker_eq _ _ _
        · split
          · dsimp only
            rw [hstate]
            exact factorPicker_eq _ _ _
          · split
            · dsimp only
              rw [hstate]
              exact factorPicker_eq _ _ _
            · dsimp only
              rw [hstate, factorPicker_eq]
              exact rootPicker_eq _ _ _ _ _ _

end Internal

/-- Real-root filtering with parent isolation shared across real entries. -/
@[expose] def realRootsImpl : RootSet → RealRootSet
  | .all => .all
  | .finite roots => .finite
    (((roots.filterMap (Internal.rootSelectors roots).2).toList.mergeSort
      (fun a b => decide (a.root ≤ b.root))).toArray)

/-- Compile through certified reuse without changing the public root result,
its canonical representatives, multiplicities, order or checked failures. -/
@[csimp] theorem realRoots_eq_impl : realRoots = realRootsImpl := by
  funext roots
  cases roots with
  | all => rfl
  | finite roots => simp only [realRoots, realRootsImpl, Internal.rootSelectors_eq]

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

/-- Select the unique nonnegative root of the square-root polynomial.
This entry point checks the argument sign and rejects negative inputs. -/
@[expose] def sqrtRoot? (a : RealAlgebraicNumber) : Option RealAlgebraicNumber :=
  if a < 0 then none else ofAlgebraic? a.toAlgebraic.sqrt

/-- Return the nonnegative square root, or none for a negative argument. -/
@[expose] def sqrt? (a : RealAlgebraicNumber) : Option RealAlgebraicNumber :=
  sqrtRoot? a

/-- Square root of a nonnegative argument. The companion proves selection succeeds,
so the fallback is unreachable-by-pipeline-invariant under the supplied hypothesis. -/
@[expose] def sqrt (a : RealAlgebraicNumber) (_h : 0 ≤ a) : RealAlgebraicNumber :=
  a.sqrt?.getD (Hex.panicWith zero "RealAlgebraicNumber.sqrt: nonnegative root not found")

end RealAlgebraicNumber
end Hex
