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
  x : SimpleRoot p
  rep : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x

namespace AlgebraicNumber

private def zeroSquare : DyadicSquare :=
  ⟨0, 0, (separationDepth ZPoly.X : Int)⟩

/-- The fixed explicit representative of the root of `X`. -/
private def zeroRep : RefinedIsolation ZPoly.X :=
  ⟨⟨zeroSquare, by
      left
      decide⟩,
    by
      simp only [zeroSquare, separationDepth]
      omega⟩

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
    ⟨zero_isIrreducible, by decide⟩ zero_squarefree (SimpleRoot.mk zeroRep)
    zeroRep rfl

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
    let isolations ← isolate p squarefree (separationDepth p : Int)
    let refined ← isolations.mapM DyadicRootIsolation.toRefined?
    let canonical ← refined.toList.find? fun r => r.sameRoot rep
    some (.mk p prim pos_lc pos_degree checked squarefree (SimpleRoot.mk canonical)
      canonical rfl)

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
  · obtain ⟨isolations, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨refined, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨canonical, _, h⟩ := Option.bind_eq_some_iff.mp h
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
    obtain ⟨isolations, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨refined, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨canonical, hcanonical, h⟩ := Option.bind_eq_some_iff.mp h
    have hsame : canonical.sameRoot rep = true :=
      List.find?_some (p := fun r : RefinedIsolation p => r.sameRoot rep)
        hcanonical
    cases h
    exact ⟨rfl, hsame⟩

instance : Inhabited AlgebraicNumber := ⟨zero⟩

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
