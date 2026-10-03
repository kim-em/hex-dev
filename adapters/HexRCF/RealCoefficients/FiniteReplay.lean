/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldDecisionProgress
public section

/-! Replay fixed-field certificates with explicitly recorded finite signs. -/
namespace Hex.RCF.RealCoefficients

namespace IsolationReplay
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Recorded operand agreement preserves every total and interval count. -/
theorem check_congr (left right : E → Int) (point : Dyadic → E) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (agree : ∀ key ∈ SignInputs.isolation point head cert, left key = right key) :
    cert.check left point context head = cert.check right point context head := by
  have total := SignInputs.certificate_check_congr left right context head 1
    .negInf .posInf cert.isolations.intervals.size cert.total (fun key present =>
      agree key (by simp only [SignInputs.isolation, List.mem_append]; exact Or.inl present))
  have counts := List.all_congr (l₁ := List.finRange cert.isolations.intervals.size) rfl
    (p := fun i =>
      let interval := cert.isolations.intervals[i]
      Sturm.check left context head 1 (.finite (point interval.lower))
        (.finite (point interval.upper)) 1 cert.counts[i])
    (q := fun i =>
      let interval := cert.isolations.intervals[i]
      Sturm.check right context head 1 (.finite (point interval.lower))
        (.finite (point interval.upper)) 1 cert.counts[i]) (fun i => by
      apply SignInputs.certificate_check_congr
      intro key present
      apply agree key
      simp only [SignInputs.isolation, List.mem_append]
      right
      exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, present⟩)
  simp only [check, total, counts]

end IsolationReplay

namespace FieldRootSigns.Table
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Finite agreement on the stored query operands preserves root-atom replay,
including rejected missing rows. No root search or new query is evaluated. -/
theorem check_congr (left right : E → Int) (point : Dyadic → E) (context : Ctx)
    (head : DensePoly E) (isolation : IsolationReplay E Ctx)
    (table : Table E Ctx n isolation.isolations.intervals.size)
    (query : RealFormula.Poly n → DensePoly E) (formula : RealFormula.QF n)
    (agree : ∀ key ∈ SignInputs.rootQueries point head isolation
      (table.entries.map fun row i => row.evidence[i]), left key = right key) :
    table.check left point context head (isolation.isolations.intervals.toVector) query formula =
      table.check right point context head (isolation.isolations.intervals.toVector) query formula := by
  unfold check
  apply List.all_congr rfl
  intro atom
  cases found : table.entries.find? (sameAtom atom) with
  | none => rfl
  | some row =>
    apply List.all_congr rfl
    intro i
    apply SignInputs.certificate_check_congr
    intro key present
    apply agree key
    unfold SignInputs.rootQueries
    apply List.mem_flatMap.mpr
    refine ⟨(fun j => row.evidence[j]), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨row, List.mem_of_find?_eq_some found, rfl⟩
    · apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_finRange i, ?_⟩
      have interval : (isolation.isolations.intervals.toVector)[i] = isolation.isolations.intervals[i] := by
        simp
      simpa only [interval] using present

end FieldRootSigns.Table
namespace FieldBuild.Result

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx]

/-- Every operand required by finite replay, including the original divisors,
must have a recorded sign. A missing entry rejects before any verdict. -/
@[expose] def recorded (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1))
    (guards : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := []) : Bool :=
  (signKeys values formula data.radical.core data.isolation data.rootSigns guards).all
    (fun key => (data.signs.lookup? key).isSome)

/-- Executable replay of the same evidence envelope. The sign operation reads
only the supplied table; it performs no root or sign search. -/
@[expose] def checkFinite (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (guards : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := []) : Bool :=
  data.recorded values formula guards &&
    Field.checkSignTable p s hw hp data.signs &&
    data.radical.check context (FieldCarrier.product values formula) &&
    data.isolation.check data.finiteSign FieldDecision.point context data.radical.core &&
    data.rootSigns.check data.finiteSign FieldDecision.point context data.radical.core
      (FieldReplay.intervals data.isolation)
      (FieldSpecialize.literalPolynomial values) formula

omit [DecidableEq Ctx] in
theorem recorded_spec (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (guards)
    (h : data.recorded values formula guards = true) :
    ∀ key ∈ signKeys values formula data.radical.core data.isolation data.rootSigns guards,
      (data.signs.lookup? key).isSome = true := List.all_eq_true.mp h

omit [DecidableEq Ctx] in
private theorem finiteSign_eq (data : Result p s hw hp Ctx (n + 1))
    (key : PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (hit : (data.signs.lookup? key).isSome = true) :
    data.finiteSign key = data.sign key := by
  cases found : data.signs.lookup? key with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at hit
  | some value => simp only [finiteSign, sign, LiteralSign.Table.sign, found, Option.getD_some]

/-- Complete recorded operands make executable finite replay identical to the
original evidence checker, without assuming any oracle's signs. -/
theorem checkFinite_eq (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx) (guards)
    (h : data.recorded values formula guards = true) :
    data.checkFinite values formula context guards = data.checkEvidence values formula context := by
  have hits := data.recorded_spec values formula guards h
  have isolation := IsolationReplay.check_congr data.finiteSign data.sign
    FieldDecision.point context data.radical.core data.isolation (fun key present => by
      apply finiteSign_eq data key
      apply hits key
      simp only [signKeys, List.mem_append]
      exact Or.inl (Or.inl (Or.inl present)))
  have roots := FieldRootSigns.Table.check_congr data.finiteSign data.sign
    FieldDecision.point context data.radical.core data.isolation data.rootSigns
    (FieldSpecialize.literalPolynomial values) formula (fun key present => by
      apply finiteSign_eq data key
      apply hits key
      simp only [signKeys, List.mem_append]
      exact Or.inl (Or.inl (Or.inr present)))
  simp only [checkFinite, h, Bool.true_and, checkEvidence, FieldReplay.intervals,
    isolation, roots]

/-- Acceptance establishes the mathematical envelope rather than assuming it. -/
theorem checkFinite_sound (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx) (guards)
    (h : data.checkFinite values formula context guards = true) :
    data.checkEvidence values formula context = true := by
  have recorded : data.recorded values formula guards = true := by
    simp only [checkFinite, Bool.and_eq_true] at h
    exact h.1.1.1.1
  rwa [data.checkFinite_eq values formula context guards recorded] at h

end FieldBuild.Result
end Hex.RCF.RealCoefficients
