/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Batteries.Util.Panic
public import HexBerlekampZassenhaus
public meta import HexBerlekampZassenhaus
public import HexRoots
public meta import HexRoots

public section

/-!
Core representations for exact algebraic numbers.

`QAdjoin` stores reduced rational coordinates in a fixed presentation,
`AlgebraicRoot` stores a squarefree factorization-lazy root, and
`AlgebraicNumber` seals the canonical irreducible representation behind a
private constructor. The only constructor exposed to later implementation
modules uses the fixed representative of zero for `X`; all other inputs run
the fixed root isolator and select its canonical disc.
-/
namespace Hex

/-- Runtime evidence that the factorization-backed irreducibility checker
accepted an integer polynomial. -/
class ZPoly.CheckedIrreducible (p : ZPoly) : Prop where
  is_true : ZPoly.isIrreducible p = true
  pos_degree : 0 < p.degree?.getD 0

/-- Canonical reduced rational coordinates in the fixed field `ℚ(x)`. -/
structure QAdjoin (p : ZPoly) (x : SimpleRoot p) where
  coeffs : DensePoly Rat
  degree_lt : coeffs.degree?.getD 0 < p.degree?.getD 0

/-- A factorization-lazy algebraic root with an eagerly certified isolating
representative. -/
structure AlgebraicRoot where
  p : ZPoly
  prim : ZPoly.Primitive p
  pos_lc : 0 < p.leadingCoeff
  pos_degree : 0 < p.degree?.getD 0
  squarefree : HasOnlySimpleRoots p
  x : SimpleRoot p
  rep : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x

namespace AlgebraicNumber

private def zeroSquare : DyadicSquare :=
  ⟨0, 0, (separationDepth ZPoly.X : Int)⟩

/-- The fixed explicit representative of the root of `X`. -/
def zeroRep : RefinedIsolation ZPoly.X :=
  ⟨⟨zeroSquare, by
      exact .ofWitness (by
        left
        decide)⟩,
    by
      simp only [zeroSquare, separationDepth]
      omega⟩

/-- Evidence that a representative is the deterministic representative stored
by the canonical algebraic-number constructor. -/
@[expose]
def IsCanonical (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) : Prop :=
  (p = ZPoly.X ∧ HEq rep zeroRep) ∨
    (p ≠ ZPoly.X ∧
      ∃ (isolations : Array (DyadicRootIsolation p))
        (refined : Array (RefinedIsolation p)),
        isolate p squarefree (separationDepth p : Int) = some isolations ∧
          isolations.mapM DyadicRootIsolation.toRefined? = some refined ∧
          rep ∈ refined.toList)

/-- Run the deterministic representative-selection pipeline and retain its
provenance together with the match against the supplied root. -/
@[expose]
def canonicalRep? (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) (hzero : p ≠ ZPoly.X) :
    Option {r : RefinedIsolation p //
      IsCanonical p squarefree r ∧ r.sameRoot rep = true} :=
  match hisolate : isolate p squarefree (separationDepth p : Int) with
  | none => none
  | some isolations =>
      match hrefine : isolations.mapM DyadicRootIsolation.toRefined? with
      | none => none
      | some refined =>
          match hfind : refined.toList.find? fun r => r.sameRoot rep with
          | none => none
          | some canonical => some ⟨canonical, Or.inr
              ⟨hzero, isolations, refined, hisolate, hrefine,
                List.mem_of_find?_eq_some hfind⟩,
              by
                exact List.find?_some
                  (p := fun r : RefinedIsolation p => r.sameRoot rep) hfind⟩

end AlgebraicNumber

/-- A canonical algebraic number. Construction is sealed so each normalized
polynomial/root pair receives one fixed representative. -/
structure AlgebraicNumber where
  private mk ::
  p : ZPoly
  prim : ZPoly.Primitive p
  pos_lc : 0 < p.leadingCoeff
  pos_degree : 0 < p.degree?.getD 0
  checked : ZPoly.CheckedIrreducible p
  squarefree : HasOnlySimpleRoots p
  rep : RefinedIsolation p
  canonical : AlgebraicNumber.IsCanonical p squarefree rep

namespace AlgebraicNumber

/-- The selected simple root is determined by the canonical representative. -/
@[expose]
def x (a : AlgebraicNumber) : SimpleRoot a.p :=
  SimpleRoot.mk a.rep

/-- The stored canonical representative selects exactly the root `a.x`. -/
@[simp] theorem rep_mk (a : AlgebraicNumber) :
    SimpleRoot.mk a.rep = a.x := rfl

private theorem zero_isIrreducible : ZPoly.isIrreducible ZPoly.X = true := by
  exact ZPoly.isIrreducible_X

private theorem zero_squarefree : HasOnlySimpleRoots ZPoly.X := by
  -- Kernel reduction stops inside rational-polynomial gcd, so this cannot be
  -- replaced by `by decide` under the module system.
  have hX : ZPoly.toRatPoly ZPoly.X =
      DensePoly.monomial 1 (1 : Rat) := by
    apply DensePoly.ext_coeff
    intro n
    rw [ZPoly.coeff_toRatPoly, DensePoly.coeff_monomial]
    by_cases hn : n = 1
    · subst n
      simp [ZPoly.X]
    · rw [if_neg hn]
      rw [ZPoly.X, DensePoly.coeff_monomial, if_neg hn]
      change ((0 : Int) : Rat) = 0
      simp
  have hderiv : DensePoly.derivative (ZPoly.toRatPoly ZPoly.X) =
      DensePoly.C (1 : Rat) := by
    rw [hX]
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_derivative_semiring, DensePoly.coeff_C,
      DensePoly.coeff_monomial]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, if_neg (by omega : n + 1 ≠ 1)]
      change ((n + 1 : Nat) : Rat) * 0 = 0
      exact Rat.mul_zero _
  unfold HasOnlySimpleRoots ZPoly.SquareFreeRat
  rw [hderiv]
  by_cases hg : (DensePoly.gcd (ZPoly.toRatPoly ZPoly.X)
      (DensePoly.C (1 : Rat))).size = 0
  · omega
  · exact ZPoly.rat_size_le_of_dvd_nonzero hg (by decide)
      (DensePoly.gcd_dvd_right _ _)

private def zeroRaw : AlgebraicNumber :=
  .mk ZPoly.X (by rfl) (by decide) (by decide)
    ⟨zero_isIrreducible, by decide⟩ zero_squarefree zeroRep
    (Or.inl ⟨rfl, HEq.rfl⟩)

-- Keep executable evidence that the ordinary isolator also meets its stated
-- completeness bound on `X`; the explicit zero path makes totality independent
-- of this bounded computation.
#guard (isolate ZPoly.X zero_squarefree
  (separationDepth ZPoly.X : Int)).isSome

/-- The canonical algebraic number zero, represented by the fixed explicit
isolation of the normalized polynomial `X`. -/
def zero : AlgebraicNumber :=
  zeroRaw

instance : Zero AlgebraicNumber := ⟨zero⟩

/-- The named canonical zero agrees with the `Zero` instance. -/
theorem zero_eq_zero : AlgebraicNumber.zero = (0 : AlgebraicNumber) := rfl

/-- The canonical zero retains `X` as its normalized polynomial. -/
@[simp] theorem zero_p : (0 : AlgebraicNumber).p = ZPoly.X := by
  rfl

/-- Re-isolate an already normalized irreducible polynomial with the fixed
default strategy and retain the unique canonical disc matching `rep`.

The normalized polynomial `X` takes the explicit canonical-zero fast path, so
the total `Zero` instance does not depend on success of a bounded driver. For
all other inputs this is the implementation boundary used by later smart
constructors. It is checked because failure of the bounded isolation driver is
retired only by the Mathlib companion's completeness proof. -/
def ofNormalized?
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) : Option AlgebraicNumber :=
  if _hzero : p = ZPoly.X then
    some zeroRaw
  else do
    let canonical ← canonicalRep? p squarefree rep _hzero
    some (.mk p prim pos_lc pos_degree checked squarefree canonical.1
      canonical.2.1)

/-- The success bit of canonicalization is exactly the success bit of its
isolation, refinement, and representative-selection pipeline. This exposes
the checked boundary needed by the Mathlib totality proof without exposing the
sealed `AlgebraicNumber` constructor. -/
theorem ofNormalized?_isSome_eq
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) :
    (ofNormalized? p prim pos_lc pos_degree checked squarefree rep).isSome =
      if _hzero : p = ZPoly.X then true else
        (canonicalRep? p squarefree rep _hzero).isSome := by
  unfold ofNormalized?
  split
  · simp
  · cases hcanonical : canonicalRep? p squarefree rep _ with
    | none => simp
    | some canonical => simp

/-- Successful canonicalization retains the supplied normalized polynomial. -/
theorem ofNormalized?_p
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) {a : AlgebraicNumber}
    (h : ofNormalized? p prim pos_lc pos_degree checked squarefree rep = some a) :
    a.p = p := by
  unfold ofNormalized? at h
  split at h
  · next hp =>
    cases h
    simp [zeroRaw, hp]
  · obtain ⟨canonical, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rfl

/-- A successful canonicalization either takes the explicit zero path or
stores a representative intersecting the supplied isolation. This is the
Mathlib-free behavioral boundary used by semantic soundness proofs. -/
theorem ofNormalized?_spec
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) {a : AlgebraicNumber}
    (h : ofNormalized? p prim pos_lc pos_degree checked squarefree rep = some a) :
    (p = ZPoly.X ∧ a = 0) ∨
      ∃ hp : a.p = p, Intersects (hp ▸ a.rep) rep := by
  unfold ofNormalized? at h
  split at h
  · next hp =>
    left
    refine ⟨hp, ?_⟩
    cases h
    rfl
  · right
    obtain ⟨canonical, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact ⟨rfl, canonical.2.2⟩

instance : Inhabited AlgebraicNumber := ⟨zero⟩

/-- Two canonical values are equal once their dependent polynomials and stored
representatives agree. The remaining fields are propositions, and the selected
`SimpleRoot` is forced by `rep_mk`. -/
theorem ext (a b : AlgebraicNumber) (hp : a.p = b.p)
    (hrep : HEq a.rep b.rep) : a = b := by
  cases a
  cases b
  cases hp
  cases eq_of_heq hrep
  rfl

end AlgebraicNumber

/-- Closed-disc membership test for zero, including boundary contact. -/
@[expose]
def RefinedIsolation.containsZero {p : ZPoly} (r : RefinedIsolation p) : Bool :=
  r.1.square.discContains (0, 0)

/-- Canonical equality: compare minimal polynomials, then the selected roots. -/
@[expose]
def AlgebraicNumber.beq (a b : AlgebraicNumber) : Bool :=
  a.p == b.p && a.rep.1.square.discsMeet b.rep.1.square

instance : BEq AlgebraicNumber := ⟨AlgebraicNumber.beq⟩

/-- A canonical algebraic number is zero exactly when its minimal polynomial
is `X`. -/
@[expose]
def AlgebraicNumber.isZero (a : AlgebraicNumber) : Bool :=
  a.p == ZPoly.X

/-- The selected lazy root is zero exactly when its polynomial has zero
constant coefficient and its closed isolating disc contains zero. The refined
separation bound makes this test decisive between distinct simple roots. -/
@[expose]
def AlgebraicRoot.isZero (a : AlgebraicRoot) : Bool :=
  a.p.coeff 0 == 0 && a.rep.containsZero

/-- Print a diagnostic in compiled code and return the supplied fallback. -/
@[expose]
def panicWith (fallback : α) (message : String) : α :=
  Batteries.panicWith fallback message

#guard AlgebraicNumber.zero.isZero

/-- A root paired with its positive multiplicity. -/
structure RootCount where
  root : AlgebraicRoot
  multiplicity : Nat
  multiplicity_pos : 0 < multiplicity

/-- A polynomial root set; `.all` is reserved for the zero polynomial. -/
inductive RootSet where
  | all
  | finite (roots : Array RootCount)

end Hex
