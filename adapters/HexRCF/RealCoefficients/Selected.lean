/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexNumberFieldMathlib.Exact

public section

/-! Reconstruct a canonical algebraic number from a checked selected root. -/

namespace Hex.RCF.RealCoefficients.Selected

open Hex

private theorem cast_root {p q : ZPoly} (h : p = q)
    (r : AlgebraicNumber.OrientedIsolation p) :
    (h ▸ r).rep.root = r.rep.root := by
  cases h
  rfl

def algebraic (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized p prim pos_lc pos_degree checked squarefree
    (Field.literalRep p s hw hp)
    (AlgebraicNumber.ofNormalized?_isSome p prim pos_lc pos_degree checked
      squarefree (Field.literalRep p s hw hp))

theorem algebraic_toComplex (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) :
    (algebraic p s hw hp prim pos_lc pos_degree checked squarefree).toComplex =
      (Field.literalRep p s hw hp).root := by
  unfold algebraic AlgebraicNumber.ofNormalized
  let h := AlgebraicNumber.ofNormalized?_isSome p prim pos_lc pos_degree
    checked squarefree (Field.literalRep p s hw hp)
  have hr := AlgebraicNumber.ofNormalized?_toComplex p prim pos_lc pos_degree
    checked squarefree (Field.literalRep p s hw hp) (Option.some_get h).symm
  let a := (AlgebraicNumber.ofNormalized? p prim pos_lc pos_degree checked
    squarefree (Field.literalRep p s hw hp)).get h
  let hpoly : a.p = p := AlgebraicNumber.ofNormalized?_p p prim pos_lc pos_degree
    checked squarefree (Field.literalRep p s hw hp) (Option.some_get h).symm
  change (hpoly ▸ a.isolation).rep.root = _
  exact (cast_root hpoly a.isolation).trans hr

/-- The real version retains the selected complex root, rather than taking
an arbitrary conjugate or projecting a nonreal value. -/
def real (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true) :
    RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic
    (algebraic p s hw hp prim pos_lc pos_degree checked squarefree) (by
      rw [AlgebraicNumber.isReal_iff, algebraic_toComplex]
      exact Field.literalRep_real p s hw hp hreal)

theorem real_toReal (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true) :
    (real p s hw hp prim pos_lc pos_degree checked squarefree hreal).toReal =
      (Field.literalRep p s hw hp).root.re := by
  apply Complex.ofReal_injective
  rw [RealAlgebraicNumber.ofReal_toReal]
  change (algebraic p s hw hp prim pos_lc pos_degree checked squarefree).toComplex = _
  rw [algebraic_toComplex]
  exact Complex.ext rfl (Field.literalRep_real p s hw hp hreal)

end Hex.RCF.RealCoefficients.Selected
