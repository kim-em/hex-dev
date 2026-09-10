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

`PolyQuot` stores reduced rational coordinates in a fixed presentation,
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
  /-- The factorization-backed Boolean irreducibility checker accepted `p`. -/
  is_true : ZPoly.isIrreducible p = true
  /-- `p` has positive degree, excluding the prime constants the integer
  checker also accepts. -/
  pos_degree : 0 < p.natDegree

/-- Canonical reduced rational coordinates in the fixed field `ℚ(x)`. -/
structure PolyQuot (p : ZPoly) (x : SimpleRoot p) where
  /-- Reduced rational coordinates in the power basis of the selected root. -/
  coeffs : DensePoly Rat
  /-- The coordinates are already reduced modulo the defining polynomial. -/
  degree_lt : coeffs.natDegree < p.natDegree

/-- A factorization-lazy algebraic root with an eagerly certified isolating
representative. -/
structure AlgebraicRoot where
  /-- The enclosing integer polynomial; it need not be irreducible. -/
  p : ZPoly
  /-- `p` has unit content. -/
  prim : ZPoly.Primitive p
  /-- `p` has positive leading coefficient. -/
  pos_lc : 0 < p.leadingCoeff
  /-- `p` has positive degree. -/
  pos_degree : 0 < p.natDegree
  /-- `p` has only simple roots. -/
  squarefree : HasOnlySimpleRoots p
  /-- The selected root of `p`. -/
  x : SimpleRoot p
  /-- The certified refined isolation of the selected root. -/
  rep : RefinedIsolation p
  /-- The stored representative selects exactly the root `x`. -/
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
        ZPoly.isolateComplexRoots? p squarefree (separationDepth p : Int) = some isolations ∧
          isolations.mapM DyadicRootIsolation.toRefined? = some refined ∧
          rep ∈ refined.toList)

/-- Run the deterministic representative-selection pipeline and retain its
provenance together with the match against the supplied root. -/
@[expose]
def rawRep? (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) (hzero : p ≠ ZPoly.X) :
    Option {r : RefinedIsolation p //
      IsCanonical p squarefree r ∧ r.sameRoot rep = true} :=
  match hisolate : ZPoly.isolateComplexRoots? p squarefree (separationDepth p : Int) with
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

/-- The real axis or one of the two open half planes. -/
inductive RootSide where
  | real | upper | lower
  deriving DecidableEq, BEq

/-- An isolation with a canonical upper or real base and an orientation. -/
structure OrientedIsolation (p : ZPoly) where
  base : RefinedIsolation p
  side : RootSide
  valid : match side with
    | .real => base.1.square.meetsRealAxis = true
    | .upper | .lower => base.1.square.radiusHi < base.1.square.im

/-- The effective isolation of an oriented root. -/
@[expose] def OrientedIsolation.rep {p : ZPoly} (r : OrientedIsolation p) :
    RefinedIsolation p :=
  match r.side with
  | .lower => r.base.conj
  | _ => r.base

/-- Reflect an oriented root without changing its base isolation. -/
@[expose] def OrientedIsolation.conj {p : ZPoly} (r : OrientedIsolation p) :
    OrientedIsolation p :=
  match r with
  | ⟨base, .real, h⟩ => ⟨base, .real, h⟩
  | ⟨base, .upper, h⟩ => ⟨base, .lower, h⟩
  | ⟨base, .lower, h⟩ => ⟨base, .upper, h⟩

@[simp] theorem OrientedIsolation.conj_base {p : ZPoly} (r : OrientedIsolation p) :
    r.conj.base = r.base := by
  rcases r with ⟨base, side, h⟩
  cases side <;> rfl

/-- Determine the half plane of a refined isolation. -/
@[expose] def sideOf {p : ZPoly} (r : RefinedIsolation p) : RootSide :=
  if r.1.square.meetsRealAxis then .real
  else if r.1.square.radiusHi < r.1.square.im then .upper else .lower

/-- Check that the base lies in the required half plane. -/
@[expose] def orient? {p : ZPoly} (base : RefinedIsolation p) (side : RootSide) :
    Option (OrientedIsolation p) :=
  match side with
  | .real => if h : base.1.square.meetsRealAxis = true then some ⟨base, .real, h⟩ else none
  | .upper => if h : base.1.square.radiusHi < base.1.square.im then some ⟨base, .upper, h⟩ else none
  | .lower => if h : base.1.square.radiusHi < base.1.square.im then some ⟨base, .lower, h⟩ else none

/-- Successful orientation preserves the base. -/
theorem orient?_base {p : ZPoly} {base : RefinedIsolation p} {side : RootSide}
    {r : OrientedIsolation p} (h : orient? base side = some r) : r.base = base := by
  cases side <;> simp only [orient?] at h <;> split at h <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> cases h <;> rfl

/-- Select the canonical upper representative and restore the requested orientation. -/
@[expose]
def canonicalRep? (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) (hzero : p ≠ ZPoly.X) :
    Option {r : OrientedIsolation p //
      IsCanonical p squarefree r.base ∧ r.rep.sameRoot rep = true} := do
  let side := sideOf rep
  let target := if side = .lower then rep.conj else rep
  let base ← rawRep? p squarefree target hzero
  match horient : orient? base.1 side with
  | none => none
  | some r =>
    if hmatch : r.rep.sameRoot rep = true then
      some ⟨r, by rw [orient?_base horient]; exact base.2.1, hmatch⟩
    else none

end AlgebraicNumber

/-- A canonical algebraic number. Construction is sealed so each normalized
polynomial/root pair receives one fixed representative. -/
structure AlgebraicNumber where
  private mk ::
  /-- The normalized minimal integer polynomial of the represented value. -/
  p : ZPoly
  /-- `p` has unit content. -/
  prim : ZPoly.Primitive p
  /-- `p` has positive leading coefficient. -/
  pos_lc : 0 < p.leadingCoeff
  /-- `p` has positive degree. -/
  pos_degree : 0 < p.natDegree
  /-- The Boolean irreducibility checker accepted `p`. -/
  checked : ZPoly.CheckedIrreducible p
  /-- `p` has only simple roots. -/
  squarefree : HasOnlySimpleRoots p
  /-- The canonical base isolation and the selected orientation. -/
  isolation : AlgebraicNumber.OrientedIsolation p
  /-- The base comes from the deterministic isolation pipeline or explicit zero. -/
  canonical : AlgebraicNumber.IsCanonical p squarefree isolation.base

namespace AlgebraicNumber

/-- The certified isolation of the selected complex root. -/
@[expose] def rep (a : AlgebraicNumber) : RefinedIsolation a.p := a.isolation.rep

/-- The half plane of the represented number. -/
@[expose] def side (a : AlgebraicNumber) : RootSide := a.isolation.side

/-- Complex conjugation shares the canonical base and only changes orientation. -/
def conj (a : AlgebraicNumber) : AlgebraicNumber :=
  .mk a.p a.prim a.pos_lc a.pos_degree a.checked a.squarefree a.isolation.conj
    (by rw [OrientedIsolation.conj_base]; exact a.canonical)

/-- Conjugation is an involution on the stored data. -/
@[simp] theorem conj_conj (a : AlgebraicNumber) : a.conj.conj = a := by
  rcases a with ⟨p, prim, pos, degree, checked, squarefree, ⟨base, side, valid⟩, hc⟩
  cases side <;> rfl

@[simp] theorem conj_p (a : AlgebraicNumber) : a.conj.p = a.p := by rfl

/-- Conjugation exposes the reflected isolation without exposing the sealed constructor. -/
theorem conj_rep (a : AlgebraicNumber) : HEq a.conj.rep a.isolation.conj.rep := by rfl

/-- Conjugation preserves the canonical base square. -/
@[simp] theorem conj_base_square (a : AlgebraicNumber) :
    a.conj.isolation.base.1.square = a.isolation.base.1.square := by
  rcases a with ⟨p, prim, pos, degree, checked, squarefree, ⟨base, side, valid⟩, hc⟩
  cases side <;> rfl

/-- Conjugation flips precisely the two nonreal sides. -/
@[simp] theorem conj_side (a : AlgebraicNumber) : a.conj.side =
    match a.side with | .real => .real | .upper => .lower | .lower => .upper := by
  rcases a with ⟨p, prim, pos, degree, checked, squarefree, ⟨base, side, valid⟩, hc⟩
  cases side <;> rfl

/-- Real values are fixed by conjugation. -/
theorem conj_of_side_real (a : AlgebraicNumber) (h : a.side = .real) : a.conj = a := by
  rcases a with ⟨p, prim, pos, degree, checked, squarefree, ⟨base, side, valid⟩, hc⟩
  change side = .real at h
  cases h
  rfl

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
    · rw [ite_eq_right hn]
      rw [ZPoly.X, DensePoly.coeff_monomial, ite_eq_right hn]
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
    · rw [ite_eq_right hn, ite_eq_right (by omega : n + 1 ≠ 1)]
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
    ⟨zero_isIrreducible, by decide⟩ zero_squarefree ⟨zeroRep, .real, by decide⟩
    (Or.inl ⟨rfl, HEq.rfl⟩)

-- Keep executable evidence that the ordinary isolator also meets its stated
-- completeness bound on `X`; the explicit zero path makes totality independent
-- of this bounded computation.
#guard (ZPoly.isolateComplexRoots? ZPoly.X zero_squarefree
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

/-- The canonical zero carries its explicit square centred on the real axis. -/
@[simp] theorem zero_square : (0 : AlgebraicNumber).rep.1.square =
    ⟨0, 0, (separationDepth ZPoly.X : Int)⟩ := by
  rfl

/-- Zero lies on the real axis. -/
@[simp] theorem zero_side : (0 : AlgebraicNumber).side = .real := by rfl

/-- Re-isolate an already normalized irreducible polynomial with the fixed
default strategy and retain the unique canonical disc matching `rep`.

The normalized polynomial `X` takes the explicit canonical-zero fast path, so
the total `Zero` instance does not depend on success of a bounded driver. For
all other inputs this is the implementation boundary used by later smart
constructors. It is checked because failure of the bounded isolation driver is
retired only by the Mathlib companion's completeness proof. -/
def ofNormalized?
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree)
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
    (pos_degree : 0 < p.natDegree)
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
    (pos_degree : 0 < p.natDegree)
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
    (pos_degree : 0 < p.natDegree)
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
    (hisolation : HEq a.isolation b.isolation) : a = b := by
  cases a
  cases b
  cases hp
  cases eq_of_heq hisolation
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
  /-- The recorded root. -/
  root : AlgebraicRoot
  /-- The multiplicity of the root in the polynomial being solved. -/
  multiplicity : Nat
  /-- Roots are recorded only with positive multiplicity. -/
  multiplicity_pos : 0 < multiplicity

/-- A polynomial root set; `.all` is reserved for the zero polynomial. -/
inductive RootSet where
  | all
  | finite (roots : Array RootCount)

namespace RootSet

/-- The recorded roots of a nonzero polynomial, or `none` for the zero
polynomial, every number being a root of that. -/
@[expose]
def finite? : RootSet → Option (Array RootCount)
  | .finite roots => some roots
  | .all => none

/-- The recorded roots, with the zero polynomial giving the empty array. -/
@[expose]
def toArray (roots : RootSet) : Array RootCount :=
  roots.finite?.getD #[]

@[simp] theorem finite?_finite (roots : Array RootCount) :
    (RootSet.finite roots).finite? = some roots := rfl

@[simp] theorem finite?_all : RootSet.all.finite? = none := rfl

@[simp] theorem toArray_finite (roots : Array RootCount) :
    (RootSet.finite roots).toArray = roots := rfl

@[simp] theorem toArray_all : RootSet.all.toArray = #[] := rfl

end RootSet

end Hex
