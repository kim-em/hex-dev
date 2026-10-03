/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldBuildProgress

public section

namespace Hex.RCF.RealCoefficients.FieldBuild.Result

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable [ZPoly.CheckedIrreducible p] {Ctx : Type u} [DecidableEq Ctx]

/-- Executable finite lookup. Decision laws below require all sample keys to
be recorded, so the missing-key default cannot determine a verdict. -/
@[expose] def finiteSign (data : Result p s hw hp Ctx n)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) : Int :=
  (data.signs.lookup? a).getD 0

/-- The strict universal fold used by compiled presentation preview. -/
@[expose] def allValue (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) : Option Bool :=
  OptionFold.allArray (Cell.all data.isolation.isolations.intervals.size)
    (fun cell => formula.evalSigns (FieldDecision.cellSign data.finiteSign values
      data.isolation (data.rootSigns.value data.isolation.total) cell))

/-- The strict existential fold used by compiled presentation preview. -/
@[expose] def anyValue (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) : Option Bool :=
  OptionFold.anyArray (Cell.all data.isolation.isolations.intervals.size)
    (fun cell => formula.evalSigns (FieldDecision.cellSign data.finiteSign values
      data.isolation (data.rootSigns.value data.isolation.total) cell))

omit [ZPoly.CheckedIrreducible p] [DecidableEq Ctx] in
private theorem formula_agree (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1))
    (recorded : ∀ key ∈ signKeys values formula data.radical.core data.isolation data.rootSigns,
      (data.signs.lookup? key).isSome = true)
    (cell : Cell data.isolation.isolations.intervals.size) :
    formula.evalSigns (FieldDecision.cellSign data.finiteSign values data.isolation
      (data.rootSigns.value data.isolation.total) cell) =
    formula.evalSigns (FieldDecision.cellSign data.sign values data.isolation
      (data.rootSigns.value data.isolation.total) cell) := by
  apply RealFormula.QF.evalSigns_congr
  intro atom present
  cases cell with
  | root i => rfl
  | «open» cut =>
    let key := (FieldSpecialize.literalPolynomial values atom).eval
      (FieldDecision.point (data.isolation.isolations.openPoint cut))
    have sample : key ∈ SignInputs.openSamples FieldDecision.point data.isolation
        (formula.polys.map (FieldSpecialize.literalPolynomial values)) := by
      apply List.mem_flatMap.mpr
      refine ⟨Cell.open cut, ?_, ?_⟩
      · exact Array.mem_toList_iff.mpr (Cell.mem_all _)
      · apply List.mem_map.mpr
        refine ⟨FieldSpecialize.literalPolynomial values atom,
          List.mem_map.mpr ⟨atom, present, rfl⟩, rfl⟩
    have wanted : key ∈ signKeys values formula data.radical.core data.isolation data.rootSigns := by
      simp only [signKeys, List.mem_append, List.not_mem_nil, or_false]
      exact Or.inr sample
    have hit := recorded key wanted
    have same : data.finiteSign key = data.sign key := by
      cases found : data.signs.lookup? key with
      | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at hit
      | some value => simp only [finiteSign, sign, LiteralSign.Table.sign, found, Option.getD_some]
    exact congrArg (fun value => some (Sign.ofInt value)) same

private theorem cells (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (checked : data.checkEvidence values formula context = true) :
    ∃ roots : Fin data.isolation.isolations.intervals.size → ℝ,
      StrictMono roots ∧
      ∀ cell x, Cell.Region roots cell x → ∀ atom ∈ formula.polys, ∃ observed,
        FieldDecision.cellSign data.sign values data.isolation
          (data.rootSigns.value data.isolation.total) cell atom = some observed ∧
        SignType.sign (((observed.toInt : Int) : ℝ)) =
          SignType.sign (atom.eval (RealFormula.append
            (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x)) := by
  simp only [checkEvidence, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨table, radical⟩, isolation⟩, queries⟩ := checked
  have real : s.meetsRealAxis = true := by
    simp only [Field.checkSignTable, Bool.and_eq_true] at table
    exact table.1.2
  apply FieldDecision.cellSign_spec (Field.literalRep p s hw hp)
    (Field.literalRep_mk p s hw hp) (Field.literalRep_real p s hw hp real)
    data.sign (Field.checkSignTable_spec p s hw hp data.signs table)
    values formula context data.radical radical data.isolation isolation
    (data.rootSigns.value data.isolation.total) (data.rootSigns.evidence data.isolation.total)
  intro i atom present
  have interval : (FieldReplay.intervals data.isolation)[i] =
      data.isolation.isolations.intervals[i] := by simp [FieldReplay.intervals]
  simpa only [interval] using
    data.rootSigns.query_checked data.sign FieldDecision.point context data.radical.core
      (FieldReplay.intervals data.isolation) (FieldSpecialize.literalPolynomial values)
      formula queries i atom present data.isolation.total

/-- An accepted envelope and complete finite hits give a total compiled
universal decision, including accepted false as a diagnostic verdict. -/
theorem forall_decision (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (checked : data.checkEvidence values formula context = true)
    (recorded : ∀ key ∈ signKeys values formula data.radical.core data.isolation data.rootSigns,
      (data.signs.lookup? key).isSome = true) :
    ∃ value, data.allValue values formula = some value ∧
      (value = true ↔ ∀ x, formula.toProp (RealFormula.append
        (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x)) := by
  obtain ⟨roots, monotone, lookup⟩ := cells data values formula context checked
  obtain ⟨value, folded, semantic⟩ := RealCoefficients.forall_decision roots monotone formula
    (fun x => RealFormula.append (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x)
    (FieldDecision.cellSign data.sign values data.isolation
      (data.rootSigns.value data.isolation.total)) lookup
  refine ⟨value, ?_, semantic⟩
  simpa only [allValue, formula_agree data values formula recorded] using folded

/-- The same finite envelope gives a total compiled existential decision.
No symbolic infinitesimal is used as a real witness. -/
theorem exists_decision (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (checked : data.checkEvidence values formula context = true)
    (recorded : ∀ key ∈ signKeys values formula data.radical.core data.isolation data.rootSigns,
      (data.signs.lookup? key).isSome = true) :
    ∃ value, data.anyValue values formula = some value ∧
      (value = true ↔ ∃ x, formula.toProp (RealFormula.append
        (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x)) := by
  obtain ⟨roots, monotone, lookup⟩ := cells data values formula context checked
  obtain ⟨value, folded, semantic⟩ := RealCoefficients.exists_decision roots monotone formula
    (fun x => RealFormula.append (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x)
    (FieldDecision.cellSign data.sign values data.isolation
      (data.rootSigns.value data.isolation.total)) lookup
  refine ⟨value, ?_, semantic⟩
  simpa only [anyValue, formula_agree data values formula recorded] using folded

end Hex.RCF.RealCoefficients.FieldBuild.Result
