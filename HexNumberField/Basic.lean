/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexMatrix
public import HexResultant
public import HexRoots
public import HexRowReduce

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
  checked : ZPoly.CheckedIrreducible p
  squarefree : HasOnlySimpleRoots p
  x : SimpleRoot p
  rep : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x

namespace AlgebraicNumber

set_option backward.privateInPublic true in
/-- Re-isolate an already normalized irreducible polynomial with the fixed
default strategy and retain the unique canonical disc matching `rep`.

This is the implementation boundary used by later smart constructors. It is
checked because failure of the bounded isolation driver is retired only by the
Mathlib companion's completeness proof. -/
@[expose]
def ofNormalized?
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) : Option AlgebraicNumber := do
  let isolations ← isolate p squarefree (separationDepth p : Int)
  let refined ← isolations.mapM DyadicRootIsolation.toRefined?
  let canonical ← refined.toList.find? fun r => r.sameRoot rep
  some (.mk p prim pos_lc checked squarefree (SimpleRoot.mk canonical)
    canonical rfl)

end AlgebraicNumber

/-- Closed-disc membership test for zero, including boundary contact. -/
@[expose]
def RefinedIsolation.containsZero {p : ZPoly} (r : RefinedIsolation p) : Bool :=
  let s := r.1.square
  let radiusSq : Dyadic := (2 : Dyadic) * Dyadic.ofIntWithPrec 1 (2 * s.prec)
  decide (GaussDyadic.distSq s.center (0, 0) ≤ radiusSq)

/-- Canonical equality: compare minimal polynomials, then the selected roots. -/
@[expose]
def AlgebraicNumber.beq (a b : AlgebraicNumber) : Bool :=
  if h : a.p = b.p then
    RefinedIsolation.sameRoot
      (cast (congrArg RefinedIsolation h) a.rep) b.rep
  else
    false

instance : BEq AlgebraicNumber := ⟨AlgebraicNumber.beq⟩

/-- A canonical algebraic number is zero exactly when its minimal polynomial
is `X`. -/
@[expose]
def AlgebraicNumber.isZero (a : AlgebraicNumber) : Bool :=
  a.p == (DensePoly.monomial 1 1 : ZPoly)

/-- The selected lazy root is zero exactly when its polynomial has zero
constant coefficient and its closed isolating disc contains zero. -/
@[expose]
def AlgebraicRoot.isZero (a : AlgebraicRoot) : Bool :=
  a.p.coeff 0 == 0 && a.rep.containsZero

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
