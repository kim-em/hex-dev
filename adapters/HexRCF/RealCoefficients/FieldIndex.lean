/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SignIndex
public import HexRCF.RealCoefficients.FieldBuild
public section

/-! Positional lookup preserves the fixed-field replay checker. -/

namespace Hex.RCF.RealCoefficients
open Hex

namespace Field

/-- Lexicographic coordinate order routes finite keys. It is not the real
order on represented values and does not run algebraic sign computations. -/
@[expose] def keyOrder {p : ZPoly} {root : SimpleRoot p}
    (left right : PolyQuot p root) : Ordering :=
  compare left.coeffs.toArray.toList right.coeffs.toArray.toList

/-- Indexed hits obey exactly the same selected-root and table bindings. -/
theorem checkSignTable_index (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (compare : PolyQuot p (SimpleRoot.ofSquare p s hw hp) →
      PolyQuot p (SimpleRoot.ofSquare p s hw hp) → Ordering)
    (index : LiteralSign.Index) (checked : checkSignTable p s hw hp table = true)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    table.signIndex compare index (value (literalRep p s hw hp)) a =
      (SignType.sign (value (literalRep p s hw hp) a) : Int) := by
  simp only [checkSignTable, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨hhead, hlower⟩, hupper⟩, hreal⟩, htable⟩ := checked
  have hx : (LiteralSign.realPoly table.head).IsRoot
      (literalRep p s hw hp).root.re := by
    rw [hhead]
    exact literalRep_root p s hw hp hreal
  have hl : (table.lower : ℝ) < (literalRep p s hw hp).root.re := by
    rw [hlower]
    exact (literalRep_bounds p s hw hp).1
  have hu : (literalRep p s hw hp).root.re < (table.upper : ℝ) := by
    rw [hupper]
    exact (literalRep_bounds p s hw hp).2
  exact table.signIndex_spec PolyQuot.coeffs compare index (value (literalRep p s hw hp))
    (literalRep p s hw hp).root.re hx hl hu
    (fun a => value_realPoly (literalRep p s hw hp) a) htable a

end Field

namespace FieldBuild.Result

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable [ZPoly.CheckedIrreducible p] {Ctx : Type u} [DecidableEq Ctx]

local notation "Element" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- A positional cache changes only retrieval from the original sign table. -/
@[expose] noncomputable def signIndex (data : Result p s hw hp Ctx n)
    (compare : Element → Element → Ordering) (index : LiteralSign.Index) : Element → Int :=
  data.signs.signIndex compare index (Field.value (Field.literalRep p s hw hp))

omit [ZPoly.CheckedIrreducible p] [DecidableEq Ctx] in
theorem signIndex_eq (data : Result p s hw hp Ctx n)
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (signed : Field.checkSignTable p s hw hp data.signs = true) :
    data.signIndex compare index = data.sign := by
  funext a
  exact (Field.checkSignTable_index p s hw hp data.signs compare index signed a).trans
    (Field.checkSignTable_spec p s hw hp data.signs signed a).symm

/-- The same evidence envelope, with positional retrieval for its field signs. -/
@[expose] noncomputable def checkEvidenceIndex (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx) : Bool :=
  Field.checkSignTable p s hw hp data.signs &&
    data.radical.check context (FieldCarrier.product values formula) &&
    data.isolation.check (data.signIndex compare index) FieldDecision.point context data.radical.core &&
    data.rootSigns.check (data.signIndex compare index) FieldDecision.point context data.radical.core
      (FieldReplay.intervals data.isolation) (FieldSpecialize.literalPolynomial values) formula

@[expose] noncomputable def checkForallIndex (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx) : Bool :=
  data.checkEvidenceIndex compare index values formula context &&
    OptionFold.allArray (Cell.all data.isolation.isolations.intervals.size)
      (fun cell => formula.evalSigns
        (FieldDecision.cellSign (data.signIndex compare index) values data.isolation
          (data.rootSigns.value data.isolation.total) cell)) == some true

@[expose] noncomputable def checkExistsIndex (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx) : Bool :=
  data.checkEvidenceIndex compare index values formula context &&
    OptionFold.anyArray (Cell.all data.isolation.isolations.intervals.size)
      (fun cell => formula.evalSigns
        (FieldDecision.cellSign (data.signIndex compare index) values data.isolation
          (data.rootSigns.value data.isolation.total) cell)) == some true

omit [ZPoly.CheckedIrreducible p] in
theorem checkForallIndex_signTable (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (accepted : data.checkForallIndex compare index values formula context = true) :
    Field.checkSignTable p s hw hp data.signs = true := by
  simp only [checkForallIndex, checkEvidenceIndex, Bool.and_eq_true] at accepted
  exact accepted.1.1.1.1

omit [ZPoly.CheckedIrreducible p] in
theorem checkExistsIndex_signTable (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (accepted : data.checkExistsIndex compare index values formula context = true) :
    Field.checkSignTable p s hw hp data.signs = true := by
  simp only [checkExistsIndex, checkEvidenceIndex, Bool.and_eq_true] at accepted
  exact accepted.1.1.1.1

omit [ZPoly.CheckedIrreducible p] in
/-- After the original sign authentication, the indexed universal checker is
the existing checker, including its strict Boolean fold and source carrier. -/
theorem checkForallIndex_eq (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (signed : Field.checkSignTable p s hw hp data.signs = true) :
    data.checkForallIndex compare index values formula context =
      data.checkForall values formula context := by
  unfold checkForallIndex checkEvidenceIndex checkForall
  rw [signIndex_eq data compare index signed]

omit [ZPoly.CheckedIrreducible p] in
/-- The existential checker retains the same evidence and selected sections. -/
theorem checkExistsIndex_eq (data : Result p s hw hp Ctx (n + 1))
    (compare : Element → Element → Ordering) (index : LiteralSign.Index)
    (values : Fin n → Element) (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (signed : Field.checkSignTable p s hw hp data.signs = true) :
    data.checkExistsIndex compare index values formula context =
      data.checkExists values formula context := by
  unfold checkExistsIndex checkEvidenceIndex checkExists
  rw [signIndex_eq data compare index signed]

end FieldBuild.Result
end Hex.RCF.RealCoefficients
