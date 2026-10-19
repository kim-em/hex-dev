/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public import HexRCF.RealCoefficients.Replay
public import HexRealClosureTheory.FinitePoint
public import HexRealClosureTheory.TransportPower

public section

/-! Evaluate an entire guarded matrix at one selected real point. The owner's
finite descriptor and replay data interpret every guard and atom at that same
point. This is an existential witness check, not complete root/cell search. -/
namespace Hex.RCF.RealCoefficients.FiniteSigns
open Hex Hex.RealClosure Hex.SignDet HexPolyTheory.Interpret

namespace Row
/-- Strict signed guard and matrix evaluation. Missing atoms are invalid evidence. -/
@[expose] def check (guardSigns : List Int) (formula : RealFormula.QF n) (row : List Int) :
    Except Hex.RCF.RealCoefficients.Replay.Error Bool :=
  if guardSigns.all (fun z => Decidable.decide (z ≠ 0)) = true then
    match Samples.Row.eval formula row with
    | none => .error .binding
    | some verdict => .ok verdict
  else .error .divisor

theorem domains (guardSigns : List Int) (formula : RealFormula.QF n) (row : List Int)
    (divisors : List ℝ) (verdict : Bool)
    (exactGuards : guardSigns = divisors.map (fun x => (SignType.sign x : Int)))
    (accepted : check guardSigns formula row = .ok verdict) : ∀ d ∈ divisors, d ≠ 0 := by
  have valid : guardSigns.all (fun z => Decidable.decide (z ≠ 0)) = true := by
    by_contra absent
    simp only [check, ite_eq_right absent] at accepted
    cases accepted
  intro d member vanished
  rw [exactGuards] at valid
  have present : (SignType.sign d : Int) ∈ divisors.map (fun x => (SignType.sign x : Int)) :=
    List.mem_map_of_mem member
  have nonzero : (SignType.sign d : Int) ≠ 0 := of_decide_eq_true ((List.all_eq_true.mp valid) _ present)
  apply nonzero
  simp [vanished]

theorem eval_of_check (guardSigns : List Int) (formula : RealFormula.QF n) (values : List Int)
    (verdict : Bool) (accepted : check guardSigns formula values = .ok verdict) :
    Samples.Row.eval formula values = some verdict := by
  unfold check at accepted
  split at accepted
  · cases found : Samples.Row.eval formula values with
    | none => simp only [found] at accepted; cases accepted
    | some value => simp only [found] at accepted; cases accepted; rfl
  · cases accepted
end Row

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable (context : Algebraic.Context E Ctx coeffSign parent)
variable (read : E → ℝ) (zero : read 0 = 0) (unit : read 1 = 1)
variable (data : Transport.Finite.DescriptorData read coeffSign
  (fun x : ℝ => (SignType.sign x : Int)) context.root.raw context.root.evidence)
variable (guards : List E) (queries : List (DensePoly E))
variable (signs : SelectedSigns context.root (guards.map DensePoly.C ++ queries))
variable (replay : Transport.Finite.ReplayData read coeffSign
  (fun x : ℝ => (SignType.sign x : Int)) context.root.raw.head context.root.raw.lower
  context.root.raw.upper (context.root.raw.queries ++ (guards.map DensePoly.C ++ queries)) signs.evidence)

@[expose] def guardSigns : List Int := signs.values.toList.take guards.length
@[expose] def row : List Int := signs.values.toList.drop guards.length

include zero unit data replay in
theorem guards_exact : guardSigns context guards queries signs =
    guards.map (fun d => (SignType.sign (read d) : Int)) := by
  have observed := context.finitePoint_signs read zero unit data (guards.map DensePoly.C ++ queries) signs replay
  unfold guardSigns
  rw [← observed]
  simp [signsAt, List.map_append, List.map_map, Function.comp_def,
    Transport.polynomial_C read zero, interpret_C, Polynomial.eval_C]

variable (source : Fin n → ℝ) (formula : RealFormula.QF (n+1))
variable (binding : ∀ x : ℝ, queries.map (fun q =>
  (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read q)).eval x) =
  formula.polys.map (fun q => q.eval (RealFormula.append source x)))

include replay binding in
theorem row_exact : row context guards queries signs = formula.polys.map (fun q =>
    (SignType.sign (q.eval (RealFormula.append source
      (context.finitePoint read zero unit data))) : Int)) := by
  have observed := context.finitePoint_signs read zero unit data (guards.map DensePoly.C ++ queries) signs replay
  unfold row
  rw [← observed]
  simp only [signsAt, List.map_append, List.map_map, Function.comp_def]
  simp only [Transport.polynomial_C read zero, interpret_C, Polynomial.eval_C]
  rw [← List.length_map (as := guards) (fun d => (SignType.sign (read d) : Int)), List.drop_left]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (fun a : ℝ => (SignType.sign a : Int)))
    (binding (context.finitePoint read zero unit data))

/-- All original divisor signs are checked before the strict matrix fold.
A false result describes this point only. -/
@[expose] def check : Except Hex.RCF.RealCoefficients.Replay.Error Bool :=
  Row.check (guardSigns context guards queries signs) formula (row context guards queries signs)

include zero unit data replay in
/-- Accepted rows have no vanishing supplied divisor. Source quotation must
retain the complete list of original divisors. -/
theorem check_domains (verdict : Bool)
    (accepted : check context guards queries signs formula = .ok verdict) :
    ∀ d ∈ guards, read d ≠ 0 := by
  have nonzero := Row.domains (guardSigns context guards queries signs) formula
    (row context guards queries signs) (guards.map read) verdict
    (by simpa only [List.map_map, Function.comp_def] using
      guards_exact context read zero unit data guards queries signs replay) accepted
  intro d member
  exact nonzero (read d) (List.mem_map_of_mem member)

include zero unit data replay binding in
/-- Exact polynomial evaluation binding and finite replay give one ordinary
real witness for the whole matrix. This theorem treats `binding` as a proved
hypothesis. Source quotation must separately authenticate its valuation and
that `guards` contains every original divisor. -/
theorem check_sound (accepted : check context guards queries signs formula = .ok true) :
    ∃ x : ℝ, formula.toProp (RealFormula.append source x) := by
  refine ⟨context.finitePoint read zero unit data, ?_⟩
  exact (Hex.RCF.RealCoefficients.Samples.Row.eval_true formula _ _
    (row_exact context read zero unit data guards queries signs replay source formula binding)).mp
    (Row.eval_of_check _ _ _ true accepted)

include zero unit data replay binding in
/-- A false row gives one point where the matrix fails. It does not refute an
existential sentence or establish complete cell coverage. -/
theorem check_false (accepted : check context guards queries signs formula = .ok false) :
    ∃ x : ℝ, ¬ formula.toProp (RealFormula.append source x) := by
  refine ⟨context.finitePoint read zero unit data, ?_⟩
  have exactRow := row_exact context read zero unit data guards queries signs replay source formula binding
  have observed := Row.eval_of_check _ _ _ false accepted
  intro truth
  have passed := (Samples.Row.eval_true formula _ _ exactRow).mpr truth
  rw [observed] at passed
  cases passed

end Hex.RCF.RealCoefficients.FiniteSigns
