/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.RuntimeController
public import HexIntervalMathlib.RuntimeProof

@[expose] public section

/-!
# Typed runtime terminals

This module seals target and refutation settlement to the same typed runtime,
retained search tree, theorem registry, and proof input later consumed by
`RuntimeProof.replayTree`. A target must be the exact current target fact. A
refutation must resolve its exact package-owned schema and certificate against
the exact current fact before the inert search record is retained; recursive
replay independently invokes the theorem schema again at the theorem boundary.

The callback used by a refutation schema is arbitrary pure Lean code and is
therefore non-preemptible. Structural body and retained-tree limits are checked
before it runs. Complete runtime quotation limits are checked transactionally
when `Lineage.quoteWithin` creates a checked bundle.

There is deliberately no split adapter here. `Proof.seedChild` preserves the
parent proof equality table and its compact identities, while
`Runtime.State.startWithin` deliberately restarts every child with an empty
runtime equality arena and identity zero. After a parent equality, the first
child equality would consequently have runtime identity zero but proof identity
`parent.equalities.count`. Until the Mathlib-free restart contract can import
an authenticated equality arena (or proof replay changes its identity model),
a general typed split adapter is not representable without weakening an exact
correlation invariant.
-/

namespace Hex.Interval.RuntimeTerminal

variable {Fact Cause Plan : Type} {semantics : Proof.Semantics Fact}

inductive Error where
  | proof (error : Proof.Error)
  | result (error : Search.Result.Error)
  | controller (error : Runtime.Controller.Error)
  | runtimeProof (error : RuntimeProof.Error)
  | inheritedEqualities
  | mismatch
  deriving DecidableEq, Repr

private def liftOption.{u, v} {α : Type u} (value : Option α) :
    Option (ULift.{v} α) :=
  value.map ULift.up

private def liftExcept.{u, v} {E : Type u} {A : Type v} (map : E → Error)
    (value : Except E A) : Except Error (ULift.{1} A) :=
  match value with
  | .error error => .error (map error)
  | .ok result => .ok ⟨result⟩

/-- One exact live runtime/search lineage, theorem registry, and immutable
proof input. Its private constructor prevents replacing any component after
root and current-source alignment have been checked. -/
structure Active (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type) where
  private mk ::
  registry : RuntimeProof.Registry Fact semantics Cause Plan
  input : Proof.Input Fact
  controller : Runtime.Controller.State Fact Cause Plan Proof.Key

/-- A retained lineage after one exact target or refutation settlement. It may
still have another split child pending. Resumption always starts a controller
against this token's retained tree, so a sibling tree cannot be substituted. -/
structure Lineage (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type) where
  private mk ::
  registry : RuntimeProof.Registry Fact semantics Cause Plan
  input : Proof.Input Fact
  tree : Search.Result.Tree Fact Cause Plan Proof.Key

/-- A full transactional runtime quotation carrying the admitted proof input.
Ordinary imports cannot fabricate the record directly. `replayWithin` performs
the exact input equality check exposed in its result type, while the nested
`RuntimeProof.Bundle` independently retains the exact theorem registry used by
quotation. -/
structure Checked (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type) where
  private mk ::
  input : Proof.Input Fact
  bundle : RuntimeProof.Bundle Fact semantics Cause Plan

private def rootMatches [DecidableEq Fact]
    (registry : RuntimeProof.Registry Fact semantics Cause Plan)
    (input : Proof.Input Fact)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key) : Bool :=
  match tree.nodes[0]? with
  | none => false
  | some root =>
      let source := root.source
      input.program.check && input.facts.size == input.program.nodes.size &&
        input.target.node.index < input.program.nodes.size &&
        registry.assembly.program == input.program &&
        source.scope == input.scope && source.branch.baseProgram == input.program &&
        source.branch.initialFacts == input.facts

/-- Public `Runtime.Controller.State.startWithin` and `runWithin` already
preserve these equalities, and their private state constructor makes individual
projection-splice counterexamples unconstructible under ordinary imports. This
defensive repetition binds the visible controller projections at this separate
theorem adapter edge; conformance tests the constructible whole-runtime and
whole-input transplant paths instead of fabricating impossible field updates. -/
private def liveMatches [DecidableEq Fact] [DecidableEq Cause]
    (controller : Runtime.Controller.State Fact Cause Plan Proof.Key) : Bool :=
  match Search.Result.current? controller.tree with
  | none => false
  | some (_, source) =>
      controller.runtime.branch == source.branch &&
        controller.runtime.branch == controller.session.branch &&
        controller.runtime.serial == controller.session.serial &&
        controller.runtime.assembly.program == source.branch.program &&
        controller.session.scope == source.scope

private def hasEquality (applied : Runtime.Applied Fact Cause) : Bool :=
  applied.events.any fun event => match event with
    | .equality _ => true
    | .fact _ | .transport _ | .instance _ => false

/-- Whether an exact ancestor of `current` retained an equality event. The
current node and sibling chronologies are deliberately excluded. A checked
tree has one acyclic parent edge per non-root node, so `nodes.size` is a total
structural bound for this walk. -/
private def inheritsEquality
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (current : Search.Result.Id) : Bool :=
  let transitions := tree.transitions
  let rec walk : Nat → Search.Result.Id → Bool
    | 0, _ => false
    | fuel + 1, child =>
        match tree.nodes[child.index]? with
        | none => false
        | some node => match node.source.parent with
          | none => false
          | some parent =>
              if transitions.any fun entry => entry.1 == parent && hasEquality entry.2 then
                true
              else walk fuel parent
  walk tree.nodes.size current

/-- Admit an already sealed live controller only when its root belongs to the
exact registry/input pair and its current typed runtime remains aligned with
the retained pending source. `Runtime.Controller.State.startWithin` has already
authenticated retained callback serial and offer state; the checks here bind
that state to theorem replay. -/
opaque Active.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (registry : RuntimeProof.Registry Fact semantics Cause Plan)
    (input : Proof.Input Fact)
    (controller : Runtime.Controller.State Fact Cause Plan Proof.Key) :
    Except Error (Active Fact semantics Cause Plan) := do
  if !rootMatches registry input controller.tree || !liveMatches controller then
    throw .mismatch
  pure { registry, input, controller }

/-- Settle the exact current target fact. Neither node identity nor the current
fact is inferred from a raw terminal record supplied by the caller. -/
opaque Active.targetWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Search.Result.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (active : Active Fact semantics Cause Plan) (seen : SeenVersion) :
    Except Error (Lineage Fact semantics Cause Plan) := do
  let some current := liftOption.{0, 1} (Search.Result.current? active.controller.tree)
    | throw Error.mismatch
  let source := current.down.2
  let some fact := source.branch.factAt? seen | throw Error.mismatch
  if seen.node != active.input.target.node || fact != active.input.target.fact then
    throw Error.mismatch
  let entry : Search.Result.Target :=
    { scope := source.scope, programVersion := source.branch.programVersion, seen }
  let tree := (← liftExcept Error.result
    (Search.Result.settleWithin limits measure active.controller.tree (.target entry))).down
  pure { registry := active.registry, input := active.input, tree }

/-- Retain one exact package-owned refutation. Decoding and the theorem callback
run against the current runtime program and current fact before settlement;
the evidence is intentionally not exported. Full recursive replay later proves
the terminal again from the reconstructed chronology. -/
opaque Active.refuteWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : RuntimeProof.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (active : Active Fact semantics Cause Plan) (seen : SeenVersion)
    (key : Proof.Key) (body : List Nat) :
    Except Error (Lineage Fact semantics Cause Plan) := do
  let _ := (← liftExcept Error.proof
    (Proof.bodyCheck limits.proof key .refute body)).down
  if !active.controller.tree.check limits.result measure then
    throw (Error.result .malformed)
  let some current := liftOption.{0, 1} (Search.Result.current? active.controller.tree)
    | throw Error.mismatch
  let source := current.down.2
  if source.branch.versions[seen.node.index]? != some seen.version then
    throw Error.mismatch
  let some fact := source.branch.factAt? seen | throw Error.mismatch
  let some schema := active.registry.proof.refuter? key
    | throw (Error.proof .missingSchema)
  let some certificate := schema.decode body | throw (Error.proof .malformedBody)
  let context : Proof.RefuteContext semantics :=
    { scope := source.scope, programVersion := source.branch.programVersion,
      program := source.branch.program,
      node := seen.node, fact }
  let some _ := schema.prove context certificate | throw (Error.proof .malformedBody)
  let entry : Search.Result.Refute Proof.Key :=
    { scope := source.scope, programVersion := source.branch.programVersion,
      seen, schema := key, body }
  let tree := (← liftExcept Error.result
    (Search.Result.settleWithin limits.result measure active.controller.tree (.refute entry))).down
  pure { registry := active.registry, input := active.input, tree }

/-- Restart the next retained child using a runtime already created from that
child's exact version-zero branch. Before consulting the runtime, this rejects
an ancestor equality chronology which `Proof.seedChild` would inherit but the
runtime restart would reset. The controller constructor then authenticates the
branch and reset serial against this token's tree; using the retained tree here
prevents cross-lineage splicing.

Assembly generation is not a second inherited-proof identity: runtime restart
authenticates its supplied assembly as the child's generation base, and full
`RuntimeProof` quotation reconstructs the parent's post-chronology assembly and
checks every child's exact before/after generation, bindings, and applications.
A wrong same-program assembly can therefore produce no checked event bundle;
with no child events, no proof evidence depends on that assembly metadata. -/
opaque Lineage.resumeWithin [DecidableEq Fact] [DecidableEq Cause]
    (controllerLimits : Runtime.Controller.Limits) (envelope : Search.Envelope)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (lineage : Lineage Fact semantics Cause Plan)
    (runtime : Runtime.State Fact Cause) :
    Except Error (Active Fact semantics Cause Plan) := do
  if !lineage.tree.check controllerLimits.result measure then
    throw (Error.result .malformed)
  let some current := liftOption.{0, 1} (Search.Result.current? lineage.tree)
    | throw Error.mismatch
  if inheritsEquality lineage.tree current.down.1 then
    throw Error.inheritedEqualities
  let controller ← Runtime.Controller.State.startWithin controllerLimits envelope measure
    runtime lineage.tree |>.mapError Error.controller
  if !rootMatches lineage.registry lineage.input lineage.tree || !liveMatches controller then
    throw .mismatch
  pure { registry := lineage.registry, input := lineage.input, controller }

/-- Transactionally quote the complete retained runtime tree. No partial
terminal or event recipe escapes on a later failure. -/
opaque Lineage.quoteWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : RuntimeProof.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (lineage : Lineage Fact semantics Cause Plan) :
    Except Error (Checked Fact semantics Cause Plan) := do
  let bundle ← RuntimeProof.quoteTreeWithin limits measure lineage.registry lineage.tree
    |>.mapError Error.runtimeProof
  pure { input := lineage.input, bundle }

/-- Replay the exact checked quotation against the input sealed into it. -/
def Checked.replay [DecidableEq Fact] [DecidableEq Cause] [DecidableEq Plan]
    (limits : RuntimeProof.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (domain : Proof.Domain semantics) (laws : Proof.Laws semantics)
    (checked : Checked Fact semantics Cause Plan) :
    Except Error
      (Proof.Evidence (semantics.Entails checked.input.program
        (Proof.initialBase checked.input) checked.input.target)) :=
  RuntimeProof.replayTree limits measure domain laws checked.input checked.bundle
    |>.mapError Error.runtimeProof

/-- Replay while exposing an expected input in the result type. The equality
check is an exact anti-transplant guard, not a compatibility-key comparison. -/
opaque Checked.replayWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq Plan]
    (limits : RuntimeProof.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (domain : Proof.Domain semantics) (laws : Proof.Laws semantics)
    (input : Proof.Input Fact) (checked : Checked Fact semantics Cause Plan) :
    Except Error
      (Proof.Evidence (semantics.Entails input.program
        (Proof.initialBase input) input.target)) := do
  if h : input = checked.input then
    h.symm ▸ checked.replay limits measure domain laws
  else throw .mismatch

end Hex.Interval.RuntimeTerminal
