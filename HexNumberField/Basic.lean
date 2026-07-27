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
modules re-runs the fixed root isolator and selects its canonical disc.
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
  degree_lt : coeffs.degree? < p.degree?

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

/-- A canonical algebraic number. Construction is sealed so every value can
be normalized and re-isolated through the fixed deterministic strategy. -/
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

/-- Re-isolate an already normalized irreducible polynomial with the fixed
default strategy and retain the unique canonical disc matching `rep`.

This is the implementation boundary used by later smart constructors. It is
checked because failure of the bounded isolation driver is retired only by the
Mathlib companion's completeness proof. -/
def ofNormalized?
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) : Option AlgebraicNumber := do
  let isolations ← isolate p squarefree (separationDepth p : Int)
  let refined ← isolations.mapM DyadicRootIsolation.toRefined?
  let canonical ← refined.toList.find? fun r => r.sameRoot rep
  some (.mk p prim pos_lc pos_degree checked squarefree (SimpleRoot.mk canonical)
    canonical rfl)

private def zeroSquare : DyadicSquare :=
  ⟨0, 0, (mahlerPrec ZPoly.X : Int)⟩

/-- A small explicit representative of the root of `X`, used only to select
the default isolator's canonical representative. -/
private def zeroRep : RefinedIsolation ZPoly.X :=
  ⟨⟨zeroSquare, by
      left
      decide⟩,
    by simp [zeroSquare]⟩

private theorem zero_isIrreducible : ZPoly.isIrreducible ZPoly.X = true := by
  sorry

private theorem zero_squarefree : HasOnlySimpleRoots ZPoly.X := by
  sorry

private def zeroCandidate : Option AlgebraicNumber :=
  ofNormalized? ZPoly.X (by rfl) (by decide) (by decide)
    ⟨zero_isIrreducible, by decide⟩ zero_squarefree zeroRep

#guard ZPoly.isIrreducible ZPoly.X
#guard decide (HasOnlySimpleRoots ZPoly.X)
#guard zeroCandidate.isSome

private theorem zeroCandidate_isSome : zeroCandidate.isSome := by
  sorry

/-- The canonical algebraic number zero, represented by the default isolated
root of the normalized polynomial `X`. -/
def zero : AlgebraicNumber :=
  Option.get zeroCandidate zeroCandidate_isSome

instance : Zero AlgebraicNumber := ⟨zero⟩

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
  a.p == (DensePoly.monomial 1 1 : ZPoly)

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
