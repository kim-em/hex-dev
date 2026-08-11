/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Chronological semantic replay

This module begins the forward trace checker above package-owned theorem
dispatch.  Its first checked transition composes three independent claims for
one retained rule event:

* every resolved rule input follows from the caller's base assumptions;
* the package-owned recipe proves the proposed fact from those inputs; and
* the fact-domain schema proves that the installed fact is the intersection of
  the previous and proposed facts.

The caller still has to resolve `previous` and every action input from the
already-checked event prefix.  Keeping that obligation explicit prevents this
transition from accidentally consulting a future fact or the engine's final
mutable fact table.
-/

namespace Hex.Interval.Experiment.ChronologicalReplay

open Propagator PayloadArena SemanticReplay

/-- Exact evidence that two equality endpoints exist in the current program
and have the same semantic domain. -/
structure SameDomain (program : Program) (left right : NodeId) : Type where
  leftNode : Node
  rightNode : Node
  leftAt : program.node? left = some leftNode
  rightAt : program.node? right = some rightNode
  domainEq : leftNode.domain = rightNode.domain

/-- Check endpoint existence and domain compatibility without interpreting the
operation at either endpoint. -/
def sameDomain? (program : Program) (left right : NodeId) :
    Option (SameDomain program left right) :=
  match leftAt : program.node? left, rightAt : program.node? right with
  | some leftNode, some rightNode =>
      if domainEq : leftNode.domain = rightNode.domain then
        some { leftNode, rightNode, leftAt, rightAt, domainEq }
      else
        none
  | _, _ => none

/-- Semantic laws needed by generic chronological composition rather than by
an individual function theorem. -/
structure Laws (semantics : Semantics Fact) : Type where
  /-- Facts depend on the semantic value, so a checked equality transports the
  same fact between its endpoints.  Structural replay separately checks that
  an admitted edge has compatible endpoint domains. -/
  holdsEq :
    ∀ (program : Program) (valuation : NodeId -> semantics.Value)
      (left right : NodeId) (fact : Fact),
      SameDomain program left right ->
      semantics.models program valuation ->
      valuation left = valuation right ->
      (semantics.holds program valuation { node := left, fact } ↔
        semantics.holds program valuation { node := right, fact })

/-- The semantic interpretation of an append-only program step is stable on
the old node prefix.  This is deliberately supplied by the semantics adapter,
not inferred from an operation key or from a package's executable behavior.

The package-owned instance theorem proves the converse existence statement
`Semantics.Extends`: every old model can be extended.  `StableStep` supplies
the restriction and fact-transport statements needed to keep already-proved
facts usable after the step.  Fact stability assumes agreement on the complete
old program because `Semantics.holds` may inspect more than the fact's node. -/
structure StableStep (semantics : Semantics Fact) (before after : Program) :
    Type where
  programPrefix : ProgramPrefix before after
  modelsBefore :
    ∀ valuation, semantics.models after valuation ->
      semantics.models before valuation
  holdsOld :
    ∀ (oldValue newValue : NodeId -> semantics.Value)
      (fact : NodeFact Fact),
      fact.node.index < before.nodes.size ->
      semantics.models before oldValue ->
      semantics.models after newValue ->
      semantics.AgreeOn before oldValue newValue ->
      (semantics.holds before oldValue fact ↔
        semantics.holds after newValue fact)

/-- Every node mentioned by a fact list belongs to the given program. -/
def FactsWithin (program : Program) (facts : List (NodeFact Fact)) : Prop :=
  ∀ fact, fact ∈ facts -> fact.node.index < program.nodes.size

/-- Every fact in one exact rule-input list follows from the same caller-owned
base assumptions. -/
def InputsSound (semantics : Semantics Fact) (program : Program)
    (base inputs : List (NodeFact Fact)) : Prop :=
  ∀ input, input ∈ inputs -> semantics.Entails program base input

/-- One exact fact version resolved from an already-checked prefix. -/
structure Resolved (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) (seen : SeenVersion) where
  fact : Fact
  within : seen.node.index < program.nodes.size
  sound :
    Evidence
      (semantics.Entails program base { node := seen.node, fact })

/-- Ordered action inputs and their common soundness proof after prefix-only
resolution. -/
structure ResolvedInputs (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) where
  facts : List (NodeFact Fact)
  sound : Evidence (InputsSound semantics program base facts)

/-- Resolve an ordered action-input list without changing its nodes or
consulting any fact not exposed by the supplied prefix resolver. -/
def resolveInputs {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    (resolve : (seen : SeenVersion) -> Option (Resolved semantics program base seen)) :
    List SeenVersion -> Option (ResolvedInputs semantics program base)
  | [] =>
      some
        { facts := []
          sound :=
            { proof := by
                intro input member
                simp at member } }
  | seen :: rest =>
      match resolve seen, resolveInputs resolve rest with
      | some head, some tail =>
          some
            { facts := { node := seen.node, fact := head.fact } :: tail.facts
              sound :=
                { proof := by
                    intro input member
                    rcases List.mem_cons.mp member with equal | member
                    · subst input
                      exact head.sound.proof
                    · exact tail.sound.proof input member } }
      | _, _ => none

/-- The resolved fact list must preserve the action's declared input-node
order.  Exact versions are checked by the chronological prefix resolver which
constructs the list. -/
def inputNodesMatch (action : Action) (inputs : List (NodeFact Fact)) : Bool :=
  action.inputs.map (fun seen => seen.node) == inputs.map (fun input => input.node)

/-- Reflexive semantic program extension. -/
def extendRefl (semantics : Semantics Fact) (program : Program) :
    Evidence (semantics.Extends program program) :=
  { proof := by
      intro valuation model
      exact ⟨valuation, model, fun _ _ => rfl⟩ }

/-- Compose two conservative program extensions.  The structural prefix proof
supplies the size relation needed to carry agreement on the original nodes
through the intermediate program. -/
def extendTrans {Fact : Type} {semantics : Semantics Fact}
    {base before after : Program}
    (basePrefix : ProgramPrefix base before)
    (first : Evidence (semantics.Extends base before))
    (second : Evidence (semantics.Extends before after)) :
    Evidence (semantics.Extends base after) :=
  { proof := by
      intro valuation model
      obtain ⟨middle, middleModel, firstAgreement⟩ :=
        first.proof valuation model
      obtain ⟨extended, extendedModel, secondAgreement⟩ :=
        second.proof middle middleModel
      refine ⟨extended, extendedModel, ?_⟩
      intro node within
      exact Eq.trans (firstAgreement node within)
        (secondAgreement node (Nat.lt_of_lt_of_le within basePrefix.nodeSize)) }

/-- Compose two exact structural program-prefix witnesses. -/
theorem prefixTrans {base before after : Program}
    (first : ProgramPrefix base before)
    (second : ProgramPrefix before after) :
    ProgramPrefix base after :=
  { operationSize := Nat.le_trans first.operationSize second.operationSize
    nodeSize := Nat.le_trans first.nodeSize second.nodeSize
    operationAt := by
      intro index within
      exact Eq.trans
        (second.operationAt index
          (Nat.lt_of_lt_of_le within first.operationSize))
        (first.operationAt index within)
    nodeAt := by
      intro index within
      exact Eq.trans
        (second.nodeAt index (Nat.lt_of_lt_of_le within first.nodeSize))
        (first.nodeAt index within) }

/-- Transport a checked consequence across an append-only semantic step.
Both the assumptions and conclusion must refer to old nodes. -/
def liftEntails {Fact : Type} {semantics : Semantics Fact}
    {before after : Program} {assumptions : List (NodeFact Fact)}
    {conclusion : NodeFact Fact}
    (step : StableStep semantics before after)
    (assumptionsWithin : FactsWithin before assumptions)
    (conclusionWithin : conclusion.node.index < before.nodes.size)
    (sound : Evidence (semantics.Entails before assumptions conclusion)) :
    Evidence (semantics.Entails after assumptions conclusion) :=
  { proof := by
      intro valuation afterModel afterAssumptions
      have beforeModel := step.modelsBefore valuation afterModel
      have beforeAssumptions :
          ∀ assumption, assumption ∈ assumptions ->
            semantics.holds before valuation assumption := by
        intro assumption member
        have agreement : semantics.AgreeOn before valuation valuation := by
          intro _ _
          rfl
        exact
          (step.holdsOld valuation valuation assumption
            (assumptionsWithin assumption member) beforeModel afterModel
            agreement).mpr
            (afterAssumptions assumption member)
      have beforeConclusion :=
        sound.proof valuation beforeModel beforeAssumptions
      have agreement : semantics.AgreeOn before valuation valuation := by
        intro _ _
        rfl
      exact
        (step.holdsOld valuation valuation conclusion conclusionWithin
          beforeModel afterModel agreement).mp
          beforeConclusion }

/-- Compose a package rule theorem and a checked meet theorem into soundness of
the exact installed fact. -/
def installRule {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base inputs : List (NodeFact Fact)}
    {node : NodeId} {installed proposed previous : Fact}
    (rule :
      Evidence (semantics.Entails program inputs { node, fact := proposed }))
    (meet :
      Evidence
        (∀ (valuation : NodeId -> semantics.Value),
          semantics.models program valuation ->
          (semantics.holds program valuation { node, fact := installed } ↔
            semantics.holds program valuation { node, fact := previous } ∧
              semantics.holds program valuation { node, fact := proposed })))
    (previousSound :
      Evidence (semantics.Entails program base { node, fact := previous }))
    (inputsSound : Evidence (InputsSound semantics program base inputs)) :
    Evidence (semantics.Entails program base { node, fact := installed }) :=
  { proof := by
      intro valuation model baseHolds
      have resolved :
          ∀ input, input ∈ inputs ->
            semantics.holds program valuation input := by
        intro input member
        exact (inputsSound.proof input member) valuation model baseHolds
      have proposedHolds := rule.proof valuation model resolved
      have previousHolds := previousSound.proof valuation model baseHolds
      exact (meet.proof valuation model).mpr ⟨previousHolds, proposedHolds⟩ }

/-- Replay one rule-caused fact event after a chronological prefix resolver has
supplied its exact previous fact and ordered input facts.

The transition rejects a program-version mismatch, a malformed previous-node
reference, or a reordered input list before package dispatch.  It then follows
the event's payload through the immutable arena, checks the complete action
origin, runs the package theorem, independently checks the fact-domain meet,
and returns a theorem for the installed fact.  Equality transport has a
separate transition because it consumes an equality theorem rather than a
package fact recipe. -/
def replayRuleStep {Fact : Type} {semantics : Semantics Fact}
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (arena : Arena)
    (event : FactEvent Fact) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base assumptions : List (NodeFact Fact)) (previous : Fact)
    (previousSound :
      Evidence
        (semantics.Entails program base { node := event.node, fact := previous }))
    (assumptionsSound :
      Evidence (InputsSound semantics program base assumptions)) :
    Option
      (Evidence
        (semantics.Entails program base { node := event.node, fact := event.fact })) :=
  match event.cause with
  | .transport _ _ => none
  | .rule action proposed payload => do
      if action.programVersion != event.programVersion ||
          event.previous.node != event.node ||
          !inputNodesMatch action assumptions then
        none
      else
        let rule ←
          registry.replayRule input arena action proposed payload program
            basePrefix assumptions event.node
        let meet ←
          domain.proveMeet program event.node previous proposed event.fact
        pure (installRule rule meet previousSound assumptionsSound)

/-- Resolve the previous fact and complete action-input list from one
prefix-only resolver before replaying a rule event. -/
def replayResolvedRule {Fact : Type} {semantics : Semantics Fact}
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (arena : Arena)
    (event : FactEvent Fact) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base : List (NodeFact Fact))
    (resolve : (seen : SeenVersion) ->
      Option (Resolved semantics program base seen)) :
    Option
      (Evidence
        (semantics.Entails program base { node := event.node, fact := event.fact })) :=
  match event.cause with
  | .transport _ _ => none
  | .rule action _ _ => do
      let previous ← resolve event.previous
      let assumptions ← resolveInputs resolve action.inputs
      if nodeProof : event.previous.node = event.node then
        let exactPrevious :
            Evidence
              (semantics.Entails program base
                { node := event.node, fact := previous.fact }) := by
          simpa [nodeProof] using previous.sound
        replayRuleStep registry domain input arena event program basePrefix
          base assumptions.facts previous.fact exactPrevious assumptions.sound
      else
        none

/-- A fixed-program, forward-only fact prefix.  The constructor is private:
version-zero seeds enter through `start`, and positive versions enter only
through a successfully replayed event. -/
structure Prefix (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) where
  private mk ::
  baseWithin : FactsWithin program base
  resolve :
    (seen : SeenVersion) -> Option (Resolved semantics program base seen)

namespace Prefix

private def make {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    (baseWithin : FactsWithin program base)
    (resolve :
      (seen : SeenVersion) -> Option (Resolved semantics program base seen)) :
    Prefix semantics program base :=
  { baseWithin, resolve }

/-- Start a checked prefix from a resolver which is callable only for version
zero.  Even if the callback was written without inspecting its argument, this
wrapper cannot expose it at a positive version. -/
opaque start {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    (baseWithin : FactsWithin program base)
    (resolveZero :
      (seen : SeenVersion) -> seen.version = 0 ->
        seen.node.index < program.nodes.size ->
        Option (Resolved semantics program base seen)) :
    Prefix semantics program base :=
  make baseWithin fun seen =>
      if versionProof : seen.version = 0 then
        if within : seen.node.index < program.nodes.size then
          resolveZero seen versionProof within
        else
          none
      else
        none

/-- Extend a checked prefix by the exact positive version proved for one
accepted event. -/
private def push {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    (checked : Prefix semantics program base)
    (event : FactEvent Fact)
    (within : event.node.index < program.nodes.size)
    (sound :
      Evidence
        (semantics.Entails program base { node := event.node, fact := event.fact })) :
    Prefix semantics program base :=
  make checked.baseWithin fun seen =>
      let current : SeenVersion := { node := event.node, version := event.version }
      if exact : seen = current then
        some
          { fact := event.fact
            within := by
              subst seen
              exact within
            sound := by
              subst seen
              exact sound }
      else
        checked.resolve seen

/-- Result of one accepted rule event. -/
structure Step {Fact : Type} (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) (event : FactEvent Fact) where
  next : Prefix semantics program base
  sound :
    Evidence
      (semantics.Entails program base { node := event.node, fact := event.fact })

/-- Replay and append one rule event.  The exact new `(node, version)` must be
fresh, and its version must be the successor of the resolved previous fact.
These checks turn a prefix-only resolver into an append-only chronological
state rather than a general fact oracle. -/
opaque replayRule {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    (checked : Prefix semantics program base)
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (arena : Arena)
    (event : FactEvent Fact)
    (basePrefix : ProgramPrefix input.baseProgram program) :
    Option (Step semantics program base event) := do
  if within : event.node.index < program.nodes.size then
    if event.version != event.previous.version + 1 then none else pure ()
    let current : SeenVersion := { node := event.node, version := event.version }
    if (checked.resolve current).isSome then none else pure ()
    let sound ←
      replayResolvedRule registry domain input arena event program basePrefix
        base checked.resolve
    pure { next := checked.push event within sound, sound }
  else
    none

/-- Carry a checked fact prefix across a semantics-stable program extension.
Old versions retain their proofs.  Any newly appended node is available at
version zero with the fact-domain top fact, proved independently of packages.
The old resolver is consulted first, so caller-supplied version-zero facts are
never replaced by top. -/
opaque lift {Fact : Type} {semantics : Semantics Fact}
    {before after : Program} {base : List (NodeFact Fact)}
    (checked : Prefix semantics before base)
    (step : StableStep semantics before after)
    (domain : FactDomainSchema semantics) :
    Prefix semantics after base :=
  make
    (fun fact member =>
      Nat.lt_of_lt_of_le
        (checked.baseWithin fact member) step.programPrefix.nodeSize)
    fun seen =>
      match checked.resolve seen with
      | some resolved =>
          some
            { fact := resolved.fact
              within :=
                Nat.lt_of_lt_of_le resolved.within step.programPrefix.nodeSize
              sound :=
                liftEntails step checked.baseWithin resolved.within
                  resolved.sound }
      | none =>
          if versionProof : seen.version = 0 then
            if appended : before.nodes.size ≤ seen.node.index then
              if within : seen.node.index < after.nodes.size then
                match nodeProof : after.node? seen.node with
                | some instruction =>
                    some
                      { fact := domain.top instruction.domain
                        within
                        sound :=
                          { proof := by
                              intro valuation model _
                              exact
                                domain.topSound after valuation seen.node
                                  instruction nodeProof model } }
                | none => none
              else
                none
            else
              none
          else
            none

end Prefix

/-- Replay one chronological expression-program extension and compose it with
the already-checked conservative extension from the caller's base program.
Pure-equality or pure-scope instances may have `before = after`; the semantic
claim remains reflexive while the program version still advances. -/
def replayInstanceStep {Fact : Type} {semantics : Semantics Fact}
    (registry : SemanticReplay.Registry semantics)
    (input : CheckerInput Fact) (arena : Arena)
    (event : InstanceEvent) (before after : Program)
    (basePrefix : ProgramPrefix input.baseProgram before)
    (stepPrefix : ProgramPrefix before after)
    (sameOperations : before.operations = after.operations)
    (checked : Evidence (semantics.Extends input.baseProgram before)) :
    Option (Evidence (semantics.Extends input.baseProgram after)) := do
  if event.programVersion != event.origin.programVersion + 1 then
    none
  else
    let step ←
      registry.replayInstance input arena event before after basePrefix
        stepPrefix sameOperations
    pure (extendTrans basePrefix checked step)

/-- The proof state of chronological replay at one exact expression-program
version.  Its constructor is private so a caller cannot pair facts proved for
one program with another program or skip a version. -/
structure Cursor (semantics : Semantics Fact) (input : CheckerInput Fact)
    (base : List (NodeFact Fact)) (version : Nat) (program : Program) where
  private mk ::
  basePrefix : ProgramPrefix input.baseProgram program
  extension : Evidence (semantics.Extends input.baseProgram program)
  facts : Prefix semantics program base

namespace Cursor

private def make {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    {version : Nat} {program : Program}
    (basePrefix : ProgramPrefix input.baseProgram program)
    (extension : Evidence (semantics.Extends input.baseProgram program))
    (facts : Prefix semantics program base) :
    Cursor semantics input base version program :=
  { basePrefix, extension, facts }

/-- Start chronological replay at the caller's exact base program. -/
opaque start {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    (facts : Prefix semantics input.baseProgram base) :
    Cursor semantics input base 0 input.baseProgram :=
  make (ProgramPrefix.refl input.baseProgram)
    (extendRefl semantics input.baseProgram) facts

/-- Replay one package-owned expression instantiation at the current cursor.
Besides package replay, this checks the cursor-relative versions and verifies
that the event's claimed fresh nodes are exactly the appended program suffix.
The returned cursor owns the lifted old facts and proved top facts for that
suffix. -/
opaque replayInstance {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    {version : Nat} {before : Program}
    (checked : Cursor semantics input base version before)
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (arena : Arena)
    (event : InstanceEvent) (after : Program)
    (stepPrefix : ProgramPrefix before after)
    (sameOperations : before.operations = after.operations)
    (stable : StableStep semantics before after) :
    Option (Cursor semantics input base event.programVersion after) := do
  if event.origin.programVersion != version ||
      event.programVersion != version + 1 ||
      event.newNodes !=
        Propagator.newNodeIds before.nodes.size after.nodes.size then
    none
  else
    let extension ←
      replayInstanceStep registry input arena event before after
        checked.basePrefix stepPrefix sameOperations checked.extension
    pure
      (make (prefixTrans checked.basePrefix stepPrefix) extension
        (checked.facts.lift stable domain))

/-- Replay one rule event at the exact current program version and append its
proved fact version to the cursor-owned prefix. -/
opaque replayRule {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    {version : Nat} {program : Program}
    (checked : Cursor semantics input base version program)
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (arena : Arena)
    (event : FactEvent Fact) :
    Option (Cursor semantics input base version program) := do
  if event.programVersion != version then none else pure ()
  let step ←
    Prefix.replayRule checked.facts registry domain input arena event
      checked.basePrefix
  pure
    (make checked.basePrefix checked.extension step.next)

end Cursor

/-- Compose a checked equality, its resolved conditional assumptions, the
source fact, and the target's previous fact into soundness of one installed
equality-transport event. -/
def installTransport {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base equalityAssumptions : List (NodeFact Fact)}
    {target source : NodeId} {installed previous transported : Fact}
    (laws : Laws semantics) (edge : EqualityEdge)
    (compatible : SameDomain program edge.left edge.right)
    (orientation :
      (target = edge.left ∧ source = edge.right) ∨
        (target = edge.right ∧ source = edge.left))
    (equality :
      Evidence
        (semantics.EntailsEq program equalityAssumptions edge.left edge.right))
    (meet :
      Evidence
        (∀ (valuation : NodeId -> semantics.Value),
          semantics.models program valuation ->
          (semantics.holds program valuation { node := target, fact := installed } ↔
            semantics.holds program valuation { node := target, fact := previous } ∧
              semantics.holds program valuation { node := target, fact := transported })))
    (previousSound :
      Evidence (semantics.Entails program base { node := target, fact := previous }))
    (sourceSound :
      Evidence (semantics.Entails program base { node := source, fact := transported }))
    (assumptionsSound :
      Evidence
        (InputsSound semantics program base equalityAssumptions)) :
    Evidence (semantics.Entails program base { node := target, fact := installed }) :=
  { proof := by
      intro valuation model baseHolds
      have resolved :
          ∀ input, input ∈ equalityAssumptions ->
            semantics.holds program valuation input := by
        intro input member
        exact (assumptionsSound.proof input member) valuation model baseHolds
      have endpoints := equality.proof valuation model resolved
      have sourceHolds := sourceSound.proof valuation model baseHolds
      have transportedHolds :
          semantics.holds program valuation { node := target, fact := transported } := by
        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (laws.holdsEq program valuation edge.left edge.right transported
            compatible model endpoints).mpr sourceHolds
        · exact (laws.holdsEq program valuation edge.left edge.right transported
            compatible model endpoints).mp sourceHolds
      have previousHolds := previousSound.proof valuation model baseHolds
      exact (meet.proof valuation model).mpr ⟨previousHolds, transportedHolds⟩ }

/-- Replay one equality-caused fact event after the chronological resolver has
supplied the exact edge, source fact, target previous fact, and equality
assumptions.  The edge recipe remains package-owned even though the transport
step itself is generic. -/
def replayTransportStep {Fact : Type} {semantics : Semantics Fact}
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (input : CheckerInput Fact) (arena : Arena)
    (event : FactEvent Fact) (edge : EqualityEdge) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base equalityAssumptions : List (NodeFact Fact))
    (previous sourceFact : Fact)
    (previousSound :
      Evidence
        (semantics.Entails program base { node := event.node, fact := previous }))
    (sourceSound :
      Evidence
        (semantics.Entails program base
          { node :=
              match event.cause with
              | .transport _ source => source.node
              | .rule _ _ _ => event.node
            fact := sourceFact }))
    (assumptionsSound :
      Evidence
        (InputsSound semantics program base equalityAssumptions)) :
    Option
      (Evidence
        (semantics.Entails program base { node := event.node, fact := event.fact })) :=
  match causeProof : event.cause with
  | .rule _ _ _ => none
  | .transport equality source =>
      if event.previous.node != event.node ||
          !inputNodesMatch edge.origin equalityAssumptions then
        none
      else if orientation :
          (event.node = edge.left ∧ source.node = edge.right) ∨
            (event.node = edge.right ∧ source.node = edge.left) then
        do
          let compatible ← sameDomain? program edge.left edge.right
          let equalityProof ←
            registry.replayEquality input arena equality edge program basePrefix
              equalityAssumptions
          let meet ←
            domain.proveMeet program event.node previous sourceFact event.fact
          let exactSource :
              Evidence
                (semantics.Entails program base
                  { node := source.node, fact := sourceFact }) := by
            simpa [causeProof] using sourceSound
          pure
            (installTransport laws edge compatible orientation equalityProof meet
              previousSound exactSource assumptionsSound)
      else
        none

end Hex.Interval.Experiment.ChronologicalReplay
