/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexInterval.Experiment.PntFks2Family
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof00
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof01
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof02
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof03
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof04
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof05
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof06
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof07
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof08
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof09
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof10
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof12
public import HexIntervalMathlib.Experiment.PntFks2FamilyProof13
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Checked semantics for the full pinned FKS2 family

Thirteen generated shard wrappers and the retained shard-11 wrapper reuse one
analytic provider theorem.  The family fold dispatches only by shard; it does
not duplicate a theorem for each literal cell.
-/

namespace Hex.Interval.Experiment.PntFks2Family

open Propagator SemanticReplay OperationSemantics
open PntFks2Shard (Bound Cell CellHolds checkCell cellHolds_of_check
  Cell.margin margin_nonnegative_of_check cells11_checked cells11_holds)

theorem shard_checked (shard : Nat) (valid : shard < shardCount) :
    (shardCells shard).all checkCell = true := by
  norm_num [shardCount] at valid
  interval_cases shard <;> simp only [shardCells]
  · exact cells00_checked
  · exact cells01_checked
  · exact cells02_checked
  · exact cells03_checked
  · exact cells04_checked
  · exact cells05_checked
  · exact cells06_checked
  · exact cells07_checked
  · exact cells08_checked
  · exact cells09_checked
  · exact cells10_checked
  · exact cells11_checked
  · exact cells12_checked
  · exact cells13_checked

/-- Source-shaped Boolean check for all 13,590 exact tuples. -/
theorem allCells_checked : allCells.all checkCell = true := by
  exact List.all_eq_true.mpr fun cell member => by
    rw [allCells, List.mem_flatMap] at member
    obtain ⟨shard, shardMember, cellMember⟩ := member
    exact List.all_eq_true.mp (shard_checked shard (List.mem_range.mp shardMember))
      cell cellMember

/-- Arbitrary-membership semantic wrapper for the complete pinned family. -/
theorem allCells_holds (cell : Cell) (member : cell ∈ allCells) :
    CellHolds cell :=
  cellHolds_of_check cell (List.all_eq_true.mp allCells_checked cell member)

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .nonnegative, value => 0 ≤ value

noncomputable def cellMargins : List ℝ := allCells.map Cell.margin

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := PntFks2Shard.sourceOperation,
    relation := fun inputs _ => inputs = [] }

def batchModel : OperationSemantics.Model ℝ :=
  { operation := batchOperation, relation := fun inputs _ => inputs = cellMargins }

def operationModels : Array (OperationSemantics.Model ℝ) := #[sourceModel, batchModel]
def semantics : Semantics Bound := OperationSemantics.semantics operationModels Contains

private theorem marginsForall (cells : List Cell)
    (checked : ∀ cell ∈ cells, checkCell cell = true) :
    List.Forall₂ (fun value (_ : Cell) => 0 ≤ value)
      (cells.map Cell.margin) cells := by
  induction cells with
  | nil => exact .nil
  | cons head tail induction =>
    exact .cons (margin_nonnegative_of_check head (checked head (by simp)))
      (induction (by
        intro cell member
        exact checked cell (by simp [member])))

theorem cellsMarginsNonnegative :
    List.Forall₂ (fun value (_ : Cell) => 0 ≤ value) cellMargins allCells := by
  exact marginsForall allCells (List.all_eq_true.mp allCells_checked)

private theorem forall₂_right_get? {relation : α → β → Prop}
    {left : List α} {right : List β} (related : List.Forall₂ relation left right)
    (index : Nat) (value : β) (found : right[index]? = some value) :
    ∃ input, left[index]? = some input ∧ relation input value := by
  induction index generalizing left right with
  | zero =>
      cases related with
      | nil => simp at found
      | cons head tail =>
          simp at found
          subst value
          exact ⟨_, by simp, head⟩
  | succ index induction =>
      cases related with
      | nil => simp at found
      | cons head tail =>
          simp at found ⊢
          exact induction tail found

private theorem marginEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (target : NodeId) (cell : Cell)
    (index : Nat) (found : graph.node? anchor = some instruction)
    (operation : instruction.op = ({ index := 1 } : OpId))
    (targetFound : instruction.args[index]? = some target)
    (cellFound : allCells[index]? = some cell) (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := target, fact := .nonnegative } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .nonnegative (valuation target)
  intro valuation models _
  obtain ⟨meaning, meaningAt, related⟩ := models.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have values : instruction.args.map valuation = cellMargins := by
    change instruction.args.map valuation = cellMargins at related
    exact related
  obtain ⟨input, inputFound, inputNonnegative⟩ :=
    forall₂_right_get? cellsMarginsNonnegative index cell cellFound
  have mappedTarget : (instruction.args.map valuation)[index]? =
      some (valuation target) := by simp [targetFound]
  have targetValue : cellMargins[index]? = some (valuation target) := by
    rw [← values]
    exact mappedTarget
  have targetInput : valuation target = input :=
    Option.some.inj (targetValue.symm.trans inputFound)
  simpa [Contains, targetInput] using inputNonnegative

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- One indexed kernel replay schema serves all 680 bounded actions. -/
def batchFactSchema (chunkIndex : Nat) : PackedFactSchema semantics where
  rule := ruleKey chunkIndex
  schema := 1
  Certificate := Unit
  decode := decodeChunk? chunkIndex
  replay := fun _ action context _ =>
    match found : context.program.node? action.node with
    | some instruction =>
        if operation : instruction.op = ({ index := 1 } : OpId) then
          if noAssumptions : context.assumptions = [] then
            if writesExact : action.writes = chunkNodes chunkIndex then
              match proposedFact : context.proposed.fact with
              | .nonnegative =>
                  let index := context.proposed.node.index
                  match cellFound : allCells[index]? with
                  | some cell =>
                      if targetAllowed :
                          (chunkNodes chunkIndex).contains context.proposed.node then
                        if targetFound :
                            instruction.args[index]? = some context.proposed.node then
                          some
                            { proof := by
                                have proposedEq : context.proposed =
                                    { node := context.proposed.node,
                                      fact := .nonnegative } :=
                                  factWith context.proposed proposedFact
                                rw [proposedEq]
                                exact marginEntails context.program context.assumptions
                                  action.node instruction context.proposed.node cell index
                                  found operation targetFound cellFound noAssumptions }
                        else none
                      else none
                  | none => none
              | .all => none
            else none
          else none
        else none
    | none => none

end Hex.Interval.Experiment.PntFks2Family
