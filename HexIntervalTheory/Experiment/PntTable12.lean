/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntTable12
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Real semantics for the PNT+ Table 12 row batch

The representative batch checks all five cells of the ordinary `b = 25` row.
Four Taylor enclosures are computed once at `-1/2`, `-2/3`, `-3/4`, and
`-4/5`, then natural-power range reduction supplies the row's four exponential
terms.  Exact rational arithmetic projects the resulting shared row bound into
the five tabulated columns.
-/

namespace Hex.Interval.Experiment.PntTable12

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-- The `k`-independent factor in the `b = 25`, `c = 0.88`, `C = 0.86`
Table 12 row. -/
noncomputable def row25S : ℝ :=
  ((0.86 : ℝ) + 1) * Real.exp (-(25 : ℝ) / 2) +
    1.03883 * Real.exp (-(50 : ℝ) / 3) +
    0.88 * Real.exp (-(75 : ℝ) / 4) +
    1.03883 * Real.exp (-(20 : ℝ))

/-- The first coefficient is exactly `C + 1` from the pinned `C_bk_S`
definition, with the row-25 source value `C = 0.86`. -/
theorem row25CapitalCoefficient : ((0.86 : ℝ) + 1) = 1.86 := by
  norm_num [OfScientific.ofScientific]

noncomputable def row25Value (column : Nat) : ℝ :=
  (25 : ℝ) ^ column * row25S

/-- Mathematical meaning of the five tabulated upper cuts. -/
def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .row25k1, x => x ≤ 175002 / 1000000000
  | .row25k2, x => x ≤ 437505 / 100000000
  | .row25k3, x => x ≤ 109377 / 1000000
  | .row25k4, x => x ≤ 273441 / 100000
  | .row25k5, x => x ≤ 683601 / 10000
  | .empty, _ => False

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun inputs _ => inputs = [] }

/-- The row anchor relates its five argument nodes to the five mathematical
cell values.  Its result is an irrelevant row token. -/
def rowModel : OperationSemantics.Model ℝ :=
  { operation := rowOperation
    relation := fun inputs _ =>
      match inputs with
      | [cell1, cell2, cell3, cell4, cell5] =>
          cell1 = row25Value 1 ∧ cell2 = row25Value 2 ∧
            cell3 = row25Value 3 ∧ cell4 = row25Value 4 ∧
            cell5 = row25Value 5
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, rowModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem meetIntersection (program : Program) (node : NodeId)
    (previous proposed : Bound) :
    ∀ valuation, semantics.models program valuation →
      (semantics.holds program valuation
          { node, fact := previous.meet proposed } ↔
        semantics.holds program valuation { node, fact := previous } ∧
          semantics.holds program valuation { node, fact := proposed }) := by
  intro valuation _
  change Contains (previous.meet proposed) (valuation node) ↔
    Contains previous (valuation node) ∧ Contains proposed (valuation node)
  cases previous <;> cases proposed <;>
    simp [Bound.meet, Contains] <;> norm_num
  all_goals intro h; exact le_trans h (by norm_num)

theorem Bound.eq_of_code_eq {left right : Bound}
    (equal : left.code = right.code) : left = right := by
  cases left <;> cases right <;> simp_all [Bound.code]

def boundSchema : FactDomainSchema semantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun program node previous proposed installed =>
      if equal : installed.code = (previous.meet proposed).code then
        some
          { proof := by
              have installedEq : installed = previous.meet proposed :=
                Bound.eq_of_code_eq equal
              subst installed
              exact meetIntersection program node previous proposed }
      else none }

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

private theorem halfWindow :
    (0.606530 : ℝ) < Real.exp (-(1 : ℝ) / 2) ∧
      Real.exp (-(1 : ℝ) / 2) < 0.606530660 := by
  have remainder := Real.exp_bound
    (x := (-(1 : ℝ) / 2)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  constructor <;> linarith

private theorem twoThirdsWindow :
    (0.513417 : ℝ) < Real.exp (-(2 : ℝ) / 3) ∧
      Real.exp (-(2 : ℝ) / 3) < 0.513417120 := by
  have remainder := Real.exp_bound
    (x := (-(2 : ℝ) / 3)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  constructor <;> linarith

private theorem threeQuartersWindow :
    (0.472366 : ℝ) < Real.exp (-(3 : ℝ) / 4) ∧
      Real.exp (-(3 : ℝ) / 4) < 0.472366553 := by
  have remainder := Real.exp_bound
    (x := (-(3 : ℝ) / 4)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  constructor <;> linarith

private theorem fourFifthsWindow :
    (0.449328 : ℝ) < Real.exp (-(4 : ℝ) / 5) ∧
      Real.exp (-(4 : ℝ) / 5) < 0.449328965 := by
  have remainder := Real.exp_bound
    (x := (-(4 : ℝ) / 5)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  constructor <;> linarith

private theorem expTermsUpper :
    Real.exp (-(25 : ℝ) / 2) < (0.606530660 : ℝ) ^ 25 ∧
      Real.exp (-(50 : ℝ) / 3) < (0.513417120 : ℝ) ^ 25 ∧
      Real.exp (-(75 : ℝ) / 4) < (0.472366553 : ℝ) ^ 25 ∧
      Real.exp (-(20 : ℝ)) < (0.449328965 : ℝ) ^ 25 := by
  have h1 := pow_lt_pow_left₀ halfWindow.2
    (Real.exp_pos (-(1 : ℝ) / 2)).le (by norm_num : 25 ≠ 0)
  have h2 := pow_lt_pow_left₀ twoThirdsWindow.2
    (Real.exp_pos (-(2 : ℝ) / 3)).le (by norm_num : 25 ≠ 0)
  have h3 := pow_lt_pow_left₀ threeQuartersWindow.2
    (Real.exp_pos (-(3 : ℝ) / 4)).le (by norm_num : 25 ≠ 0)
  have h4 := pow_lt_pow_left₀ fourFifthsWindow.2
    (Real.exp_pos (-(4 : ℝ) / 5)).le (by norm_num : 25 ≠ 0)
  rw [← Real.exp_nat_mul] at h1 h2 h3 h4
  change Real.exp ((25 : ℝ) * (-(1 : ℝ) / 2)) < (0.606530660 : ℝ) ^ 25 at h1
  change Real.exp ((25 : ℝ) * (-(2 : ℝ) / 3)) < (0.513417120 : ℝ) ^ 25 at h2
  change Real.exp ((25 : ℝ) * (-(3 : ℝ) / 4)) < (0.472366553 : ℝ) ^ 25 at h3
  change Real.exp ((25 : ℝ) * (-(4 : ℝ) / 5)) < (0.449328965 : ℝ) ^ 25 at h4
  rw [show (25 : ℝ) * (-(1 : ℝ) / 2) = -(25 : ℝ) / 2 by norm_num] at h1
  rw [show (25 : ℝ) * (-(2 : ℝ) / 3) = -(50 : ℝ) / 3 by norm_num] at h2
  rw [show (25 : ℝ) * (-(3 : ℝ) / 4) = -(75 : ℝ) / 4 by norm_num] at h3
  rw [show (25 : ℝ) * (-(4 : ℝ) / 5) = -(20 : ℝ) by norm_num] at h4
  exact ⟨h1, h2, h3, h4⟩

private theorem expTermsLower :
    (0.606530 : ℝ) ^ 25 < Real.exp (-(25 : ℝ) / 2) ∧
      (0.513417 : ℝ) ^ 25 < Real.exp (-(50 : ℝ) / 3) ∧
      (0.472366 : ℝ) ^ 25 < Real.exp (-(75 : ℝ) / 4) ∧
      (0.449328 : ℝ) ^ 25 < Real.exp (-(20 : ℝ)) := by
  have h1 := pow_lt_pow_left₀ halfWindow.1 (by norm_num)
    (by norm_num : 25 ≠ 0)
  have h2 := pow_lt_pow_left₀ twoThirdsWindow.1 (by norm_num)
    (by norm_num : 25 ≠ 0)
  have h3 := pow_lt_pow_left₀ threeQuartersWindow.1 (by norm_num)
    (by norm_num : 25 ≠ 0)
  have h4 := pow_lt_pow_left₀ fourFifthsWindow.1 (by norm_num)
    (by norm_num : 25 ≠ 0)
  rw [← Real.exp_nat_mul] at h1 h2 h3 h4
  change (0.606530 : ℝ) ^ 25 < Real.exp ((25 : ℝ) * (-(1 : ℝ) / 2)) at h1
  change (0.513417 : ℝ) ^ 25 < Real.exp ((25 : ℝ) * (-(2 : ℝ) / 3)) at h2
  change (0.472366 : ℝ) ^ 25 < Real.exp ((25 : ℝ) * (-(3 : ℝ) / 4)) at h3
  change (0.449328 : ℝ) ^ 25 < Real.exp ((25 : ℝ) * (-(4 : ℝ) / 5)) at h4
  rw [show (25 : ℝ) * (-(1 : ℝ) / 2) = -(25 : ℝ) / 2 by norm_num] at h1
  rw [show (25 : ℝ) * (-(2 : ℝ) / 3) = -(50 : ℝ) / 3 by norm_num] at h2
  rw [show (25 : ℝ) * (-(3 : ℝ) / 4) = -(75 : ℝ) / 4 by norm_num] at h3
  rw [show (25 : ℝ) * (-(4 : ℝ) / 5) = -(20 : ℝ) by norm_num] at h4
  exact ⟨h1, h2, h3, h4⟩

/-- Shared row certificate: the four point enclosures and range reductions are
performed once, then exact arithmetic closes all five coordinates. -/
theorem row25Bounds :
    row25Value 1 ≤ 175002 / 1000000000 ∧
      row25Value 2 ≤ 437505 / 100000000 ∧
      row25Value 3 ≤ 109377 / 1000000 ∧
      row25Value 4 ≤ 273441 / 100000 ∧
      row25Value 5 ≤ 683601 / 10000 := by
  have shared : row25S <
      (1.86 : ℝ) * 0.606530660 ^ 25 +
        1.03883 * 0.513417120 ^ 25 +
        0.88 * 0.472366553 ^ 25 +
        1.03883 * 0.449328965 ^ 25 := by
    unfold row25S
    nlinarith [expTermsUpper.1, expTermsUpper.2.1,
      expTermsUpper.2.2.1, expTermsUpper.2.2.2]
  constructor
  · unfold row25Value
    calc
      (25 : ℝ) ^ 1 * row25S ≤ 25 ^ 1 *
          ((1.86 : ℝ) * 0.606530660 ^ 25 +
            1.03883 * 0.513417120 ^ 25 +
            0.88 * 0.472366553 ^ 25 +
            1.03883 * 0.449328965 ^ 25) :=
        mul_le_mul_of_nonneg_left shared.le (by positivity)
      _ ≤ 175002 / 1000000000 := by norm_num
  constructor
  · unfold row25Value
    calc
      (25 : ℝ) ^ 2 * row25S ≤ 25 ^ 2 *
          ((1.86 : ℝ) * 0.606530660 ^ 25 +
            1.03883 * 0.513417120 ^ 25 +
            0.88 * 0.472366553 ^ 25 +
            1.03883 * 0.449328965 ^ 25) :=
        mul_le_mul_of_nonneg_left shared.le (by positivity)
      _ ≤ 437505 / 100000000 := by norm_num
  constructor
  · unfold row25Value
    calc
      (25 : ℝ) ^ 3 * row25S ≤ 25 ^ 3 *
          ((1.86 : ℝ) * 0.606530660 ^ 25 +
            1.03883 * 0.513417120 ^ 25 +
            0.88 * 0.472366553 ^ 25 +
            1.03883 * 0.449328965 ^ 25) :=
        mul_le_mul_of_nonneg_left shared.le (by positivity)
      _ ≤ 109377 / 1000000 := by norm_num
  constructor
  · unfold row25Value
    calc
      (25 : ℝ) ^ 4 * row25S ≤ 25 ^ 4 *
          ((1.86 : ℝ) * 0.606530660 ^ 25 +
            1.03883 * 0.513417120 ^ 25 +
            0.88 * 0.472366553 ^ 25 +
            1.03883 * 0.449328965 ^ 25) :=
        mul_le_mul_of_nonneg_left shared.le (by positivity)
      _ ≤ 273441 / 100000 := by norm_num
  · unfold row25Value
    calc
      (25 : ℝ) ^ 5 * row25S ≤ 25 ^ 5 *
          ((1.86 : ℝ) * 0.606530660 ^ 25 +
            1.03883 * 0.513417120 ^ 25 +
            0.88 * 0.472366553 ^ 25 +
            1.03883 * 0.449328965 ^ 25) :=
        mul_le_mul_of_nonneg_left shared.le (by positivity)
      _ ≤ 683601 / 10000 := by norm_num

/-- The paper's original fifth entry is not a weaker enclosure: it is false. -/
theorem rejectPaperCell : ¬ row25Value 5 ≤ 6.65350e1 := by
  have shared :
      (1.86 : ℝ) * 0.606530 ^ 25 +
          1.03883 * 0.513417 ^ 25 +
          0.88 * 0.472366 ^ 25 +
          1.03883 * 0.449328 ^ 25 < row25S := by
    unfold row25S
    nlinarith [expTermsLower.1, expTermsLower.2.1,
      expTermsLower.2.2.1, expTermsLower.2.2.2]
  have lower : (66535 / 1000 : ℝ) < row25Value 5 := by
    unfold row25Value
    calc
      (66535 / 1000 : ℝ) < 25 ^ 5 *
          ((1.86 : ℝ) * 0.606530 ^ 25 +
            1.03883 * 0.513417 ^ 25 +
            0.88 * 0.472366 ^ 25 +
            1.03883 * 0.449328 ^ 25) := by
        norm_num
      _ < 25 ^ 5 * row25S := mul_lt_mul_of_pos_left shared (by positivity)
  norm_num [OfScientific.ofScientific] at lower ⊢
  linarith

private theorem rowValues
    (graph : Program) (valuation : NodeId → ℝ)
    (model : OperationSemantics.Models operationModels graph valuation)
    (anchor : NodeId) (instruction : Node)
    (cell1 cell2 cell3 cell4 cell5 : NodeId)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [cell1, cell2, cell3, cell4, cell5]) :
    valuation cell1 = row25Value 1 ∧ valuation cell2 = row25Value 2 ∧
      valuation cell3 = row25Value 3 ∧ valuation cell4 = row25Value 4 ∧
      valuation cell5 = row25Value 5 := by
  obtain ⟨meaning, meaningAt, related⟩ := model.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  simpa [rowModel, arguments, List.map] using related

theorem cell1Entails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (cell1 cell2 cell3 cell4 cell5 : NodeId)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [cell1, cell2, cell3, cell4, cell5])
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := cell1, fact := .row25k1 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .row25k1 (valuation cell1)
  intro valuation model _
  change valuation cell1 ≤ 175002 / 1000000000
  rw [(rowValues graph valuation model anchor instruction cell1 cell2 cell3 cell4 cell5
    found operation arguments).1]
  exact row25Bounds.1

theorem cell2Entails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (cell1 cell2 cell3 cell4 cell5 : NodeId)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [cell1, cell2, cell3, cell4, cell5])
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := cell2, fact := .row25k2 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .row25k2 (valuation cell2)
  intro valuation model _
  change valuation cell2 ≤ 437505 / 100000000
  rw [(rowValues graph valuation model anchor instruction cell1 cell2 cell3 cell4 cell5
    found operation arguments).2.1]
  exact row25Bounds.2.1

theorem cell3Entails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (cell1 cell2 cell3 cell4 cell5 : NodeId)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [cell1, cell2, cell3, cell4, cell5])
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := cell3, fact := .row25k3 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .row25k3 (valuation cell3)
  intro valuation model _
  change valuation cell3 ≤ 109377 / 1000000
  rw [(rowValues graph valuation model anchor instruction cell1 cell2 cell3 cell4 cell5
    found operation arguments).2.2.1]
  exact row25Bounds.2.2.1

theorem cell4Entails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (cell1 cell2 cell3 cell4 cell5 : NodeId)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [cell1, cell2, cell3, cell4, cell5])
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := cell4, fact := .row25k4 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .row25k4 (valuation cell4)
  intro valuation model _
  change valuation cell4 ≤ 273441 / 100000
  rw [(rowValues graph valuation model anchor instruction cell1 cell2 cell3 cell4 cell5
    found operation arguments).2.2.2.1]
  exact row25Bounds.2.2.2.1

theorem cell5Entails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (cell1 cell2 cell3 cell4 cell5 : NodeId)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [cell1, cell2, cell3, cell4, cell5])
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := cell5, fact := .row25k5 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .row25k5 (valuation cell5)
  intro valuation model _
  change valuation cell5 ≤ 683601 / 10000
  rw [(rowValues graph valuation model anchor instruction cell1 cell2 cell3 cell4 cell5
    found operation arguments).2.2.2.2]
  exact row25Bounds.2.2.2.2

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Replay authenticates one row payload and projects the matching coordinate
from the row anchor's five argument nodes. -/
def batchFactSchema : PackedFactSchema semantics where
  rule := batchRuleKey
  schema := 1
  Certificate := RowCertificate
  decode := decodeCertificate?
  replay := fun _ action context certificate =>
    if certificateShape : certificate = rowCertificate then
      match found : context.program.node? action.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 1 } : OpId) then
            match arguments : instruction.args with
            | [cell1, cell2, cell3, cell4, cell5] =>
                if noAssumptions : context.assumptions = [] then
                  match proposedFact : context.proposed.fact with
                  | .row25k1 =>
                      if target : context.proposed.node = cell1 then
                        some
                          { proof := by
                              have proposedEq : context.proposed =
                                  { node := cell1, fact := .row25k1 } := by
                                rw [factWith context.proposed proposedFact, target]
                              rw [proposedEq]
                              exact cell1Entails context.program context.assumptions
                                action.node instruction cell1 cell2 cell3 cell4 cell5
                                found operation arguments noAssumptions }
                      else none
                  | .row25k2 =>
                      if target : context.proposed.node = cell2 then
                        some
                          { proof := by
                              have proposedEq : context.proposed =
                                  { node := cell2, fact := .row25k2 } := by
                                rw [factWith context.proposed proposedFact, target]
                              rw [proposedEq]
                              exact cell2Entails context.program context.assumptions
                                action.node instruction cell1 cell2 cell3 cell4 cell5
                                found operation arguments noAssumptions }
                      else none
                  | .row25k3 =>
                      if target : context.proposed.node = cell3 then
                        some
                          { proof := by
                              have proposedEq : context.proposed =
                                  { node := cell3, fact := .row25k3 } := by
                                rw [factWith context.proposed proposedFact, target]
                              rw [proposedEq]
                              exact cell3Entails context.program context.assumptions
                                action.node instruction cell1 cell2 cell3 cell4 cell5
                                found operation arguments noAssumptions }
                      else none
                  | .row25k4 =>
                      if target : context.proposed.node = cell4 then
                        some
                          { proof := by
                              have proposedEq : context.proposed =
                                  { node := cell4, fact := .row25k4 } := by
                                rw [factWith context.proposed proposedFact, target]
                              rw [proposedEq]
                              exact cell4Entails context.program context.assumptions
                                action.node instruction cell1 cell2 cell3 cell4 cell5
                                found operation arguments noAssumptions }
                      else none
                  | .row25k5 =>
                      if target : context.proposed.node = cell5 then
                        some
                          { proof := by
                              have proposedEq : context.proposed =
                                  { node := cell5, fact := .row25k5 } := by
                                rw [factWith context.proposed proposedFact, target]
                              rw [proposedEq]
                              exact cell5Entails context.program context.assumptions
                                action.node instruction cell1 cell2 cell3 cell4 cell5
                                found operation arguments noAssumptions }
                      else none
                  | _ => none
                else none
            | _ => none
          else none
      | none => none
    else none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }

def rowEmit : EmitPackage Lean.Name :=
  { schemas := [{ key := batchFactSchema.key, handle := ``batchFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := sourceEmit }

def rowProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[batchFactSchema] }
    emit := rowEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, rowProof]

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all },
    { node := node 2, fact := .all }, { node := node 3, fact := .all },
    { node := node 4, fact := .all }, { node := node 5, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all, .all, .all, .all, .all, .all]
    target := { node := node 4, fact := .row25k5 } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => row25Value 1
  | ⟨1⟩ => row25Value 2
  | ⟨2⟩ => row25Value 3
  | ⟨3⟩ => row25Value 4
  | ⟨4⟩ => row25Value 5
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, sourceModel, rowModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, sourceInstruction] at found
          subst instruction
          exact ⟨sourceModel, by rfl, by rfl⟩
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, program, sourceInstruction] at found
              subst instruction
              exact ⟨sourceModel, by rfl, by rfl⟩
          | succ index =>
              cases index with
              | zero =>
                  simp [Program.node?, program, sourceInstruction] at found
                  subst instruction
                  exact ⟨sourceModel, by rfl, by rfl⟩
              | succ index =>
                  cases index with
                  | zero =>
                      simp [Program.node?, program, sourceInstruction] at found
                      subst instruction
                      exact ⟨sourceModel, by rfl, by rfl⟩
                  | succ index =>
                      cases index with
                      | zero =>
                          simp [Program.node?, program, rowInstruction] at found
                          subst instruction
                          exact ⟨rowModel, by rfl, by simp [rowModel, valuation, node]⟩
                      | succ index =>
                          simp [Program.node?, program] at found

/-- Close five projections from one replayed row chronology. -/
theorem closeRow25
    (cell1 : Evidence (semantics.Entails program baseFacts
      { node := node 0, fact := .row25k1 }))
    (cell2 : Evidence (semantics.Entails program baseFacts
      { node := node 1, fact := .row25k2 }))
    (cell3 : Evidence (semantics.Entails program baseFacts
      { node := node 2, fact := .row25k3 }))
    (cell4 : Evidence (semantics.Entails program baseFacts
      { node := node 3, fact := .row25k4 }))
    (cell5 : Evidence (semantics.Entails program baseFacts
      { node := node 4, fact := .row25k5 })) :
    row25Value 1 ≤ 175002 / 1000000000 ∧
      row25Value 2 ≤ 437505 / 100000000 ∧
      row25Value 3 ≤ 109377 / 1000000 ∧
      row25Value 4 ≤ 273441 / 100000 ∧
      row25Value 5 ≤ 683601 / 10000 := by
  have holds : ∀ fact, fact ∈ baseFacts → Contains fact.fact (valuation fact.node) := by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have h1 := cell1.proof valuation valuationModels holds
  have h2 := cell2.proof valuation valuationModels holds
  have h3 := cell3.proof valuation valuationModels holds
  have h4 := cell4.proof valuation valuationModels holds
  have h5 := cell5.proof valuation valuationModels holds
  change valuation (node 0) ≤ 175002 / 1000000000 at h1
  change valuation (node 1) ≤ 437505 / 100000000 at h2
  change valuation (node 2) ≤ 109377 / 1000000 at h3
  change valuation (node 3) ≤ 273441 / 100000 at h4
  change valuation (node 4) ≤ 683601 / 10000 at h5
  simpa [valuation, node] using And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 h5)))

/-- Kernel-checked correspondence between the fixed certificate identity fields
and the exact scientific-decimal row in the pinned source. -/
theorem row25CertificateMatchesSource :
    rowCertificate.row = 25 ∧
      (rowCertificate.cell1Mantissa : ℝ) / 10 ^ rowCertificate.cell1Scale =
        1.750020e-4 ∧
      (rowCertificate.cell2Mantissa : ℝ) / 10 ^ rowCertificate.cell2Scale =
        4.375050e-3 ∧
      (rowCertificate.cell3Mantissa : ℝ) / 10 ^ rowCertificate.cell3Scale =
        1.093770e-1 ∧
      (rowCertificate.cell4Mantissa : ℝ) / 10 ^ rowCertificate.cell4Scale =
        2.734410e0 ∧
      (rowCertificate.cell5Mantissa : ℝ) / 10 ^ rowCertificate.cell5Scale =
        6.836010e1 ∧
      (rowCertificate.cNumerator : ℝ) / rowCertificate.cDenominator = 0.88 ∧
      (rowCertificate.capitalNumerator : ℝ) /
          rowCertificate.capitalDenominator = 0.86 ∧
      (rowCertificate.cZeroNumerator : ℝ) /
          rowCertificate.cZeroDenominator = 1.03883 ∧
      ((rowCertificate.capitalNumerator : ℝ) /
          rowCertificate.capitalDenominator + 1) = 1.86 ∧
      (rowCertificate.mMantissa : ℝ) * 10 ^ rowCertificate.mExponent = 32e12 := by
  norm_num [rowCertificate, OfScientific.ofScientific]

end Hex.Interval.Experiment.PntTable12
