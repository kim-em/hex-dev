/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.RootReplay
import HexRCF.RootReplayLiterals
import HexRCF.SelectedRoot.Data
import HexRCF.SelectedRoot.KernelCheck
import Lean.Elab.Tactic.Decide

/-! Frozen graph acceptance is checked in the ordinary kernel, independently of
the proposal producer. These concrete fixtures use ordinary non-module imports
to expose the pinned toolchain's private decoder bodies. -/
namespace Hex.RCF.RealCoefficients.RootReplayConformance
open Hex Hex.SignDet Hex.RealClosure Hex.RCF.SelectedRootTests
open scoped Hex

meta section
open Lean Elab Command Term Meta
elab "#root_check " proposition:term " => " name:ident : command => do
  liftTermElabM do
    let type ← elabTermEnsuringType proposition (mkSort .zero)
    synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let dictionary ← synthInstance (mkApp (mkConst ``Decidable) type)
    let reflexive ← mkEqRefl (mkConst ``Bool.true)
    let proof := mkAppN (mkConst ``of_decide_eq_true) #[type, dictionary, reflexive]
    KernelCheck.addChecked ((← getCurrNamespace) ++ name.getId) type proof #[``Descriptor.buildRoots, ``Descriptor.ofReplay?]
end

def polynomial : Data.base.Poly := #p[-2,0,1]
def positive := RootReplay.read Data.base.codec [1] polynomial (.finite 1) (.finite 2)
  RootReplayLiterals.positive
def whole := RootReplay.read Data.base.codec [] polynomial .negInf .posInf RootReplayLiterals.whole
def constant := RootReplay.read Data.base.codec [] (1 : Data.base.Poly) .negInf .posInf
  RootReplayLiterals.constant
def empty := RootReplay.read Data.base.codec [] (#p[1,0,1] : Data.base.Poly) .negInf .posInf
  RootReplayLiterals.empty

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check positive.toOption.isSome = true => positive_accepted
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check whole.toOption.isSome = true => whole_accepted
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check constant.toOption.isSome = true => constant_accepted
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check empty.toOption.isSome = true => empty_accepted

def positiveResult := positive.toOption.get positive_accepted
def wholeResult := whole.toOption.get whole_accepted
def constantResult := constant.toOption.get constant_accepted
def emptyResult := empty.toOption.get empty_accepted

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check (positiveResult.roots.map fun d => d.raw.signs) = [[1,1]] => positive_words
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check (wholeResult.roots.map fun d => d.raw.signs) = [[-1,1],[1,1]] => whole_words
set_option maxRecDepth 32768 in
#root_check constantResult.roots.length = 0 => constant_empty
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check emptyResult.roots.length = 0 => empty_empty

private theorem positive_read : positive = .ok positiveResult := by
  have accepted := positive_accepted
  cases h : positive with
  | error error => simp [h, Except.toOption] at accepted
  | ok result => simp [positiveResult, h, Except.toOption]

theorem guards : ∀ d ∈ ([1] : List Data.base.Value), Data.rational.value d ≠ 0 :=
  RootReplay.read_domains Data.rational _ _ _ _ _ _ positiveResult
    positive_read

open HexPolyTheory.Interpret HexRealRootsTheory in
theorem emitted_roots (d : Descriptor Data.base.Value Tower.Signature Data.base.sign Data.base.signature)
    (member : d ∈ wholeResult.roots) :
    d.root Data.rational.value Data.rational.zero_iff Data.rational.one Data.rational.add
      Data.rational.sub Data.rational.mul Data.rational.nat Data.rational.sign ∈
      Tarski.rootsIn (interpret Data.rational.value Data.rational.zero_iff polynomial)
        .negInf .posInf :=
  wholeResult.root_spec Data.rational d member

/-- A zero guard wins over malformed data even for a zero polynomial. -/
theorem zero_before_parse : RootReplay.read Data.base.codec [0] (0 : Data.base.Poly)
    .negInf .posInf (.number 0) = .error Replay.Error.divisor :=
  RootReplay.read_zero _ _ _ _ _ _ 0 (by simp) rfl

set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] polynomial (.finite 0) (.finite 2)
  RootReplayLiterals.positive).map (fun _ => ()) = .error Replay.Error.evidence => changed_domain
set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] (#p[-3,0,1] : Data.base.Poly) .negInf .posInf
  RootReplayLiterals.whole).map (fun _ => ()) = .error Replay.Error.evidence => changed_polynomial

/-- Mutations retain all other frozen fields so the intended binding or graph
validation gate must reject them. -/
private def field (record : Codec.Json) (index : Nat) (value : Codec.Json) : Codec.Json :=
  match record.getArr? with
  | .error _ => .null
  | .ok fields => .arr (fields.set! index value)
private def rootEntry (graph : Codec.Json) (change : Codec.Json → Codec.Json) : Codec.Json :=
  match graph.getArr? with
  | .error _ => .null
  | .ok fields => match fields[2]!.getArr? with
    | .error _ => .null
    | .ok entries => field graph 2 (.arr (entries.set! 2 (change entries[2]!)))
private def rootNode (change : Codec.Json → Codec.Json) : Codec.Json :=
  rootEntry RootReplayLiterals.whole fun entry =>
    match entry.getArr? with
    | .error _ => .null
    | .ok fields => field entry 0 (change fields[0]!)
private def contextSwap := rootNode fun node =>
  field node 0 (.arr #[.arr #[], .number 1, .arr #[]])
private def missingSupport := rootNode fun node =>
  match node.getArr? with
  | .error _ => .null
  | .ok fields => field node 6 (field fields[6]! 1 (.arr #[.arr #[.number 1, .number 1]]))
private def cyclic := rootEntry RootReplayLiterals.whole fun entry =>
  field entry 1 (.arr #[.arr #[.number 2, .number 2]])
private def oldVersion := field RootReplayLiterals.whole 0 (.number 0)
private def partialQueries := field RootReplayLiterals.whole 1 (.number 0)
private def partialGraphRead := Codec.readGraph Data.base.codec Tower.Signature.codec
  Data.base.signature polynomial .negInf .posInf partialQueries

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check partialGraphRead.toOption.isSome = true => partial_graph_parsed
private def partialGraph := partialGraphRead.toOption.get partial_graph_parsed
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check (partialGraph.validate? Data.base.sign Data.base.signature polynomial
  .negInf .posInf).isSome = true => partial_graph_valid
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check ((partialGraph.validate? Data.base.sign Data.base.signature polynomial .negInf .posInf).bind
  fun memo => Dag.select? Data.base.sign Data.base.signature polynomial .negInf .posInf memo
    partialGraph.root ((RootReplay.subject polynomial .negInf .posInf).full []).queries).isNone = true
  => partial_selection_rejected

#guard contextSwap.getArr?.toOption.isSome
#guard missingSupport.getArr?.toOption.isSome
#guard cyclic.getArr?.toOption.isSome
#guard oldVersion.getArr?.toOption.isSome
#guard partialQueries.getArr?.toOption.isSome

set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] polynomial .negInf .posInf contextSwap).map (fun _ => ())
  = .error Replay.Error.evidence => swapped_context
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] polynomial .negInf .posInf missingSupport).map (fun _ => ())
  = .error Replay.Error.evidence => missing_bkr_support
set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] polynomial .negInf .posInf cyclic).map (fun _ => ())
  = .error Replay.Error.evidence => cyclic_graph
set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] polynomial .negInf .posInf oldVersion).map (fun _ => ())
  = .error Replay.Error.evidence => stale_version

/- Entry zero is a valid child replay for just the first derivative. Graph
validation succeeds, but it is not the canonical full-query root table. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
#root_check (RootReplay.read Data.base.codec [] polynomial .negInf .posInf partialQueries).map (fun _ => ())
  = .error Replay.Error.evidence => partial_queries

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``positive_accepted, ``whole_accepted, ``constant_accepted, ``empty_accepted,
      ``positive_words, ``whole_words, ``constant_empty, ``empty_empty, ``positive_read,
      ``guards, ``emitted_roots, ``zero_before_parse, ``changed_domain, ``changed_polynomial,
      ``swapped_context, ``missing_bkr_support, ``cyclic_graph, ``stale_version,
      ``partial_graph_parsed, ``partial_graph_valid, ``partial_selection_rejected, ``partial_queries,
      ``RootReplay.extract_eq, ``RootReplay.read_guards, ``RootReplay.read_domains,
      ``RootReplay.read_zero, ``RootReplay.Result.words, ``RootReplay.Result.unique_words,
      ``RootReplay.Result.fields,
      ``RootReplay.Result.sorted, ``RootReplay.Result.domain, ``RootReplay.Result.root_spec,
      ``RootReplay.Result.coverage, ``RootReplay.Result.ordered] do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in {name}"
    logInfo m!"{name}: {axioms}"

end Hex.RCF.RealCoefficients.RootReplayConformance
