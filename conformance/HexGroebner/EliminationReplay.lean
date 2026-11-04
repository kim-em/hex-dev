/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.EliminationDispatchProof
public import HexGroebner.MatrixStateSchedule

public section

namespace Hex.Groebner.EliminationReplay

/-- Public-import replay of actual empty-matrix completion. It works for every
field, budget, provider and quantum, without a platform-word-size hypothesis. -/
theorem empty_example (field : PrimeField) (limits : MatrixLimits) (independent : Bool)
    (quantum : Nat) (native : Bool) :
    MatrixState.finishWith quantum (MatrixState.start field limits 0 #[] #[] #[] independent) native =
      (.ok (⟨#[],0,#[]⟩,#[]),{}) := by
  rw [MatrixState.finish_reference,Elimination.reference_empty]

/-- The public API permits completing a suspended input against the full
reference contract, including exact errors and charged prefix counters. -/
theorem resumed_example (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool)
    (steps quantum : Nat) (native : Bool) :
    let initial := MatrixState.start field limits columns reducers targets sugars independent
    let expected := Elimination.reference field limits columns reducers targets sugars independent
    MatrixState.finishWith quantum (MatrixState.advance initial steps) native =
      (expected.result,expected.stats) := by
  exact (MatrixState.finishWith_resume _ steps quantum native (MatrixState.start_geometry ..)).trans
    (MatrixState.finish_reference field limits columns reducers targets sugars independent quantum native)

/-- The production dispatcher inherits successful empty output and zero
counters, whichever native frame is available. -/
theorem dispatch_example (field : PrimeField) (limits : MatrixLimits) (independent : Bool) :
    Elimination.run field limits 0 #[] #[] false #[] true independent =
      ⟨.ok (⟨#[],0,#[]⟩,#[]),{}⟩ := by
  rw [Elimination.run_spec,Elimination.reference_empty]

/-- info: 'Hex.Groebner.EliminationReplay.empty_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms empty_example
/-- info: 'Hex.Groebner.EliminationReplay.resumed_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resumed_example
/-- info: 'Hex.Groebner.EliminationReplay.dispatch_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dispatch_example

end Hex.Groebner.EliminationReplay
