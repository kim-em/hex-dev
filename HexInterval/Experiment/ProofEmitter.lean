/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.ChronologicalReplay

@[expose] public section

/-!
# Kernel-facing proof emission

The interval search may be opaque and may run through compiled code.  Its
return value is therefore not itself evidence: the kernel cannot reduce an
opaque search, and a proof recovered from the evaluator would put that
evaluator in the trusted base.

The tactic boundary instead quotes the search output as plain data.  This
module provides transparent replay for the three proof-producing event shapes
a tactic must quote: expression instantiation, a rule fact, and equality
transport.  Each transition selects a package-owned theorem schema supplied
by the caller, checks its replay address and the event's structural links, and
composes the resulting theorem with generic semantic lemmas.

The schemas remain abstract: neither these quote types nor their replay
functions enumerate operations or supported mathematical functions.  A
tactic may emit these applications directly in dependency order or quote a
complete trace for a transparent fold over the same transitions.
-/

namespace Hex.Interval.Experiment.ProofEmitter

open Propagator PayloadArena SemanticReplay ChronologicalReplay

/-- Plain data quoted by the tactic for one rule-caused fact event.

`payload` names the entry copied from the search arena.  Keeping the entry in
the quote, rather than retaining the opaque arena lookup, is what makes the
proof-side reduction independent of the compiled search implementation. -/
structure RuleStep (Fact : Type) where
  event : FactEvent Fact
  payload : PayloadId
  entry : Entry
  assumptions : List (NodeFact Fact)
  previous : Fact

/-- Plain data quoted for one expression-instantiation event. -/
structure InstanceQuote where
  event : InstanceEvent
  payload : PayloadId
  entry : Entry

/-- Plain data quoted for one equality-caused fact improvement. -/
structure TransportStep (Fact : Type) where
  event : FactEvent Fact
  equality : EqualityId
  edge : EqualityEdge
  payload : PayloadId
  entry : Entry
  assumptions : List (NodeFact Fact)
  previous : Fact
  sourceFact : Fact

/-! ## Generic dependency assembly -/

/-- Evidence for each fact in an exact ordered input list.  A tactic builds
this value from the versioned facts it has already replayed; `sound` below
turns the list into the single premise expected by rule and equality replay.

This type is independent of operations and theorem packages.  In particular,
adding a new function propagator does not add a constructor here. -/
inductive EntailsList {Fact : Type} (semantics : Semantics Fact)
    (program : Program) (base : List (NodeFact Fact)) :
    List (NodeFact Fact) -> Type where
  | nil : EntailsList semantics program base []
  | cons {input inputs} :
      Evidence (semantics.Entails program base input) ->
      EntailsList semantics program base inputs ->
      EntailsList semantics program base (input :: inputs)

namespace EntailsList

/-- Empty dependency evidence with explicit semantic parameters, convenient
for an elaborator which will extend the list from right to left. -/
def empty {Fact : Type} (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) : EntailsList semantics program base [] :=
  .nil

/-- Combine separately replayed dependencies into the exact ordered
`InputsSound` proposition consumed by a proof-emitter transition. -/
def sound {Fact : Type} {semantics : Semantics Fact} {program : Program}
    {base : List (NodeFact Fact)} :
    {inputs : List (NodeFact Fact)} ->
      EntailsList semantics program base inputs ->
      Evidence (InputsSound semantics program base inputs)
  | [], .nil =>
      { proof := by
          intro _ member
          simp at member }
  | _ :: _, .cons head tail =>
      { proof := by
          intro input member
          rcases List.mem_cons.mp member with equal | member
          · subst input
            exact head.proof
          · exact tail.sound.proof input member }

/-- The common one-input case, convenient for direct tactic emission. -/
def singleton {Fact : Type} {semantics : Semantics Fact} {program : Program}
    {base : List (NodeFact Fact)} {input : NodeFact Fact}
    (head : Evidence (semantics.Entails program base input)) :
    Evidence (InputsSound semantics program base [input]) :=
  (EntailsList.cons head EntailsList.nil).sound

end EntailsList

/-- A caller-owned base fact entails itself in every program.  The tactic uses
this to seed its versioned evidence table from the exact base-assumption list. -/
def assumed {Fact : Type} {semantics : Semantics Fact} {program : Program}
    {base : List (NodeFact Fact)} {fact : NodeFact Fact}
    (member : fact ∈ base) :
    Evidence (semantics.Entails program base fact) :=
  { proof := by
      intro _ _ assumptions
      exact assumptions fact member }

theorem memOfGet? {Item : Type} (items : List Item) (index : Nat)
    (item : Item) (found : items[index]? = some item) : item ∈ items := by
  induction items generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at found
          subst head
          simp
      | succ index =>
          simp at found
          exact List.mem_cons_of_mem head (ih index found)

/-- Seed one caller-owned fact by its checked position in the base list.

This form is convenient for a tactic: it can quote the fact and numeric index,
then close `found` by reduction.  The resulting theorem still depends only on
ordinary membership in the caller's exact assumption list. -/
def assumedAt {Fact : Type} {semantics : Semantics Fact} (program : Program)
    (base : List (NodeFact Fact)) (index : Nat) (fact : NodeFact Fact)
    (found : base[index]? = some fact) :
    Evidence (semantics.Entails program base fact) :=
  assumed (memOfGet? base index fact found)

/-- The node of a caller fact selected by `assumedAt` is within the current
program whenever the complete base list is. -/
theorem factWithinAt {Fact : Type} (program : Program)
    (base : List (NodeFact Fact)) (within : FactsWithin program base)
    (index : Nat) (fact : NodeFact Fact) (found : base[index]? = some fact) :
    fact.node.index < program.nodes.size :=
  within fact (memOfGet? base index fact found)

/-- A successful exact node lookup proves the corresponding size bound. -/
theorem nodeWithin (program : Program) (node : NodeId) (instruction : Node)
    (found : program.node? node = some instruction) :
    node.index < program.nodes.size := by
  by_cases within : node.index < program.nodes.size
  · exact within
  · simp [Program.node?, within] at found

/-- Old node membership remains valid across an append-only prefix. -/
theorem liftNode {before after : Program} (step : ProgramPrefix before after)
    {node : NodeId} (within : node.index < before.nodes.size) :
    node.index < after.nodes.size :=
  Nat.lt_of_lt_of_le within step.nodeSize

/-- A complete base context remains within every append-only program. -/
theorem liftFacts {Fact : Type} {before after : Program}
    (step : ProgramPrefix before after) {facts : List (NodeFact Fact)}
    (within : FactsWithin before facts) : FactsWithin after facts :=
  fun fact member => liftNode step (within fact member)

/-- Transport one table entry to an enlarged program. -/
def liftFact {Fact : Type} {semantics : Semantics Fact}
    {before after : Program} {base : List (NodeFact Fact)}
    {fact : NodeFact Fact} (step : StableStep semantics before after)
    (baseWithin : FactsWithin before base)
    (sound : Evidence (semantics.Entails before base fact))
    (factWithin : fact.node.index < before.nodes.size) :
    Evidence (semantics.Entails after base fact) :=
  liftEntails step baseWithin factWithin sound

/-- Prove the domain's top fact for any exactly checked node.  The chronology
emitter uses this theorem to seed generated nodes at version zero; that
generated/version condition belongs to its evidence-table discipline, not to
this semantic lemma.  The explicit lookup prevents attaching top soundness to
a nonexistent node or to a fact for a different domain. -/
def topFact {Fact : Type} {semantics : Semantics Fact}
    (domain : FactDomainSchema semantics) (program : Program)
    (base : List (NodeFact Fact)) (node : NodeId) (instruction : Node)
    (nodeAt : program.node? node = some instruction) :
    Evidence
      (semantics.Entails program base
        { node, fact := domain.top instruction.domain }) :=
  { proof := by
      intro valuation model _
      exact domain.topSound program valuation node instruction nodeAt model }

/-! ## Package-contributed tactic schema handles -/

/-- Tactic-side address of one package-owned replay schema.  The core leaves
`Handle` abstract: a Lean elaborator may use declaration names, while another
frontend may use typed closures or indices.  A handle is never dynamically
invoked by the trusted checker.  The emitted application must still typecheck
and the replay transition rechecks `key` against the payload entry. -/
structure SchemaRef (Handle : Type) where
  key : ReplayKey
  handle : Handle

/-- The theorem schemas one function package exposes to a tactic frontend.
Packages contribute these fragments independently; the frontend does not
enumerate mathematical functions. -/
structure EmitPackage (Handle : Type) where
  schemas : List (SchemaRef Handle)

/-- Check that no two tactic schema declarations claim one replay address. -/
def uniqueSchemas {Handle : Type} : List (SchemaRef Handle) -> Bool
  | [] => true
  | schema :: rest =>
      !(rest.any fun other => other.key == schema.key) && uniqueSchemas rest

/-- Exact schema-name lookup table with a proof that replay addresses are
unambiguous. -/
structure SchemaTable (Handle : Type) where
  entries : List (SchemaRef Handle)
  unique : uniqueSchemas entries = true

namespace SchemaTable

/-- Assemble independently contributed emitter packages.  A duplicate full
replay address is ambiguous and fails closed, even when both entries name the
same declaration. -/
def build {Handle : Type} (packages : List (EmitPackage Handle)) :
    Option (SchemaTable Handle) :=
  let entries := packages.flatMap (fun package => package.schemas)
  if unique : uniqueSchemas entries then some ⟨entries, unique⟩ else none

/-- Resolve one exact `(rule, role, schema)` address with no fallback. -/
def find? (table : SchemaTable Handle) (key : ReplayKey) : Option Handle :=
  (table.entries.find? fun schema => schema.key == key).map
    (fun schema => schema.handle)

end SchemaTable

/-- Transparently replay one quoted expression instantiation and compose its
package-owned conservative-extension theorem with the extension accumulated
for the preceding program prefix. -/
def replayInstance {Fact : Type} {semantics : Semantics Fact}
    (schema : PackedInstanceSchema semantics) (input : CheckerInput Fact)
    (version : Nat) (before after : Program)
    (basePrefix : ProgramPrefix input.baseProgram before)
    (stepPrefix : ProgramPrefix before after)
    (sameOperations : before.operations = after.operations)
    (step : InstanceQuote)
    (previous : Evidence (semantics.Extends input.baseProgram before)) :
    Option (Evidence (semantics.Extends input.baseProgram after)) := do
  if step.event.payload != step.payload ||
      step.event.origin.programVersion != version ||
      step.event.programVersion != version + 1 ||
      step.event.newNodes !=
        Propagator.newNodeIds before.nodes.size after.nodes.size ||
      schema.key != step.entry.replayKey then
    none
  else if originProof : step.event.origin = step.entry.origin then
    let context : InstanceContext input step.entry.origin :=
      { before
        after
        basePrefix
        stepPrefix
        sameOperations
        event := step.event
        origin := originProof }
    let certificate <- schema.decode step.entry.body
    let extension <- schema.replay input step.entry.origin context certificate
    pure (extendTrans basePrefix previous extension)
  else
    none

/-- Transparently replay one quoted rule step.

The caller supplies soundness of facts resolved from the already-replayed
prefix.  The selected schema must match the entry's full `(rule, role,
schema)` address.  Even a malicious emitter cannot manufacture the result:
the only successful branch contains the package schema's proof and the
fact-domain intersection proof, both checked by Lean's kernel. -/
def replayRule {Fact : Type} {semantics : Semantics Fact}
    (schema : PackedFactSchema semantics)
    (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base : List (NodeFact Fact)) (step : RuleStep Fact)
    (previousSound :
      Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.previous }))
    (assumptionsSound :
      Evidence
        (InputsSound semantics program base step.assumptions)) :
    Option
      (Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.event.fact })) :=
  match causeProof : step.event.cause with
  | .transport _ _ => none
  | .rule action proposed payload => do
      if payload != step.payload ||
          action.programVersion != step.event.programVersion ||
          step.event.version != step.event.previous.version + 1 ||
          step.event.previous.node != step.event.node ||
          !action.writes.contains step.event.node ||
          !inputNodesMatch action step.assumptions ||
          schema.key != step.entry.replayKey then
        none
      else if originProof : action = step.entry.origin then
        let context : RuleFactContext input action :=
          { program
            basePrefix
            assumptions := step.assumptions
            proposed := { node := step.event.node, fact := proposed } }
        let certificate ← schema.decode step.entry.body
        let rule ← schema.replay input action context certificate
        let meet ←
          domain.proveMeet program step.event.node step.previous proposed
            step.event.fact
        let exactRule :
            Evidence
              (semantics.Entails program step.assumptions
                { node := step.event.node, fact := proposed }) := by
          simpa using rule
        pure
          (installRule exactRule meet previousSound assumptionsSound)
      else
        none

/-- Transparently replay one equality transport.  The preceding proof terms
must supply the target's previous fact, the exact source fact, and every
conditional equality assumption; an emitted application therefore cannot use
a fact before its proof has appeared in the dependency chain. -/
def replayTransport {Fact : Type} {semantics : Semantics Fact}
    (schema : PackedEqualitySchema semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (input : CheckerInput Fact) (version : Nat) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base : List (NodeFact Fact)) (step : TransportStep Fact)
    (previousSound :
      Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.previous }))
    (sourceSound :
      Evidence
        (semantics.Entails program base
          { node :=
              match step.event.cause with
              | .transport _ source => source.node
              | .rule _ _ _ => step.event.node
            fact := step.sourceFact }))
    (assumptionsSound :
      Evidence (InputsSound semantics program base step.assumptions)) :
    Option
      (Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.event.fact })) :=
  match causeProof : step.event.cause with
  | .rule _ _ _ => none
  | .transport equality source => do
      if step.event.programVersion != version ||
          step.event.version != step.event.previous.version + 1 ||
          step.event.previous.node != step.event.node ||
          equality != step.equality ||
          step.edge.payload != step.payload ||
          !inputNodesMatch step.edge.origin step.assumptions ||
          schema.key != step.entry.replayKey then
        none
      else if originProof : step.edge.origin = step.entry.origin then
        let context : EqualityContext input step.entry.origin :=
          { program
            basePrefix
            assumptions := step.assumptions
            equality := step.equality
            edge := step.edge
            origin := originProof }
        let certificate <- schema.decode step.entry.body
        let equalityProof <-
          schema.replay input step.entry.origin context certificate
        let compatible <- sameDomain? program step.edge.left step.edge.right
        if orientation :
            (step.event.node = step.edge.left ∧ source.node = step.edge.right) ∨
              (step.event.node = step.edge.right ∧ source.node = step.edge.left) then
          let meet <-
            domain.proveMeet program step.event.node step.previous
              step.sourceFact step.event.fact
          let exactSource :
              Evidence
                (semantics.Entails program base
                  { node := source.node, fact := step.sourceFact }) := by
            simpa [causeProof] using sourceSound
          pure
            (installTransport laws step.edge compatible orientation equalityProof
              meet previousSound exactSource assumptionsSound)
        else
          none
      else
        none

/-! ## Proof-producing solver splits -/

/-- Package-owned proof boundary for one domain cut.

The executable policy may propose a cut and the branch manager may compute
candidate child facts, but neither is evidence that the children cover the
parent.  A domain companion accepts the exact quoted parent, cut, and children
only when it can prove that every value satisfying the parent lies in at least
one child.  Disjointness and interiority are useful search invariants, but are
not needed for the logical join and remain branch-manager checks. -/
structure SplitSchema (semantics : Semantics Fact) (Cut : Type) where
  proveCover :
    (program : Program) -> (node : NodeId) -> (parent : Fact) -> Cut ->
      (left right : Fact) ->
      Option
        (Evidence
          (forall valuation, semantics.models program valuation ->
            semantics.holds program valuation { node, fact := parent } ->
              semantics.holds program valuation { node, fact := left } \/
                semantics.holds program valuation { node, fact := right }))

/-- Join two conditional branch theorems using a checked coverage theorem.

The child fact is an additional branch assumption, not an unconditional fact
in the caller's context.  Facts proved before the split remain in `base` and
are supplied identically to both children. -/
def installSplit {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    {node : NodeId} {parent left right : Fact} {target : NodeFact Fact}
    (cover :
      Evidence
        (forall valuation, semantics.models program valuation ->
          semantics.holds program valuation { node, fact := parent } ->
            semantics.holds program valuation { node, fact := left } \/
              semantics.holds program valuation { node, fact := right }))
    (parentSound :
      Evidence
        (semantics.Entails program base { node, fact := parent }))
    (leftSound :
      Evidence
        (semantics.Entails program ({ node, fact := left } :: base) target))
    (rightSound :
      Evidence
        (semantics.Entails program ({ node, fact := right } :: base) target)) :
    Evidence (semantics.Entails program base target) :=
  { proof := by
      intro valuation model baseHolds
      have parentHolds := parentSound.proof valuation model baseHolds
      rcases cover.proof valuation model parentHolds with leftHolds | rightHolds
      · apply leftSound.proof valuation model
        intro assumption member
        rcases List.mem_cons.mp member with equal | member
        · subst assumption
          exact leftHolds
        · exact baseHolds assumption member
      · apply rightSound.proof valuation model
        intro assumption member
        rcases List.mem_cons.mp member with equal | member
        · subst assumption
          exact rightHolds
        · exact baseHolds assumption member }

/-- Transparently replay one solver split from exact quoted children.

The branch searches may be arbitrary and opaque.  Their outputs enter this
transition only as ordinary kernel evidence under the corresponding child
assumption.  The domain schema independently authenticates coverage of the
quoted children before the generic join is constructed. -/
def replaySplit {Fact Cut : Type} {semantics : Semantics Fact}
    (schema : SplitSchema semantics Cut) (program : Program)
    (base : List (NodeFact Fact)) (node : NodeId) (parent : Fact) (cut : Cut)
    (left right : Fact) (target : NodeFact Fact)
    (parentSound :
      Evidence
        (semantics.Entails program base { node, fact := parent }))
    (leftSound :
      Evidence
        (semantics.Entails program ({ node, fact := left } :: base) target))
    (rightSound :
      Evidence
        (semantics.Entails program ({ node, fact := right } :: base) target)) :
    Option (Evidence (semantics.Entails program base target)) := do
  let cover <- schema.proveCover program node parent cut left right
  pure (installSplit cover parentSound leftSound rightSound)

/-! ## Provenance-safe branch roots -/

/-- An established parent fact remains established after adding one child
case assumption. -/
def inheritSplit {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    (side fact : NodeFact Fact)
    (sound : Evidence (semantics.Entails program base fact)) :
    Evidence (semantics.Entails program (side :: base) fact) :=
  { proof := by
      intro valuation model branchHolds
      apply sound.proof valuation model
      intro assumption member
      exact branchHolds assumption (List.mem_cons_of_mem side member) }

/-- The exact child case is available as the sole new branch assumption. -/
def assumeSplit {Fact : Type} {semantics : Semantics Fact}
    (program : Program) (base : List (NodeFact Fact)) (side : NodeFact Fact) :
    Evidence (semantics.Entails program (side :: base) side) :=
  assumed (by simp)

/-- Proof table for every version-zero fact of a restarted child session.

The exact array is runtime data, but each entry must already have an ordinary
proof under the child context.  Inherited parent consequences therefore cannot
be silently reclassified as caller assumptions. -/
structure BranchSeed {Fact : Type} (semantics : Semantics Fact)
    (input : CheckerInput Fact) (base : List (NodeFact Fact))
    (side : NodeFact Fact) where
  size : input.initialFacts.size = input.baseProgram.nodes.size
  sound :
    (node : NodeId) -> (fact : Fact) ->
      input.initialFacts[node.index]? = some fact ->
        Evidence
          (semantics.Entails input.baseProgram (side :: base) { node, fact })

namespace BranchSeed

/-- Select one child-root fact while explicitly pinning the exact checker
input and complete child assumption list used by the frontend. -/
def get {Fact : Type} (semantics : Semantics Fact) (input : CheckerInput Fact)
    (childBase : List (NodeFact Fact)) {base : List (NodeFact Fact)}
    {side : NodeFact Fact} (seed : BranchSeed semantics input base side)
    (same : childBase = side :: base) (node : NodeId) (fact : Fact)
    (found : input.initialFacts[node.index]? = some fact) :
    Evidence
      (semantics.Entails input.baseProgram childBase { node, fact }) := by
  subst childBase
  exact seed.sound node fact found

/-- Assemble a branch root from the one new case assumption and exact proofs
of all unchanged parent facts. -/
def make {Fact : Type} {semantics : Semantics Fact}
    (input : CheckerInput Fact) {base : List (NodeFact Fact)}
    (side : NodeFact Fact)
    (size : input.initialFacts.size = input.baseProgram.nodes.size)
    (sideAt : input.initialFacts[side.node.index]? = some side.fact)
    (inherited :
      (node : NodeId) -> node ≠ side.node -> (fact : Fact) ->
        input.initialFacts[node.index]? = some fact ->
          Evidence
            (semantics.Entails input.baseProgram base { node, fact })) :
    BranchSeed semantics input base side :=
  { size
    sound := by
      intro node fact found
      if same : node = side.node then
        subst node
        have factEq : fact = side.fact :=
          Option.some.inj (found.symm.trans sideAt)
        subst fact
        exact assumeSplit input.baseProgram base side
      else
        exact inheritSplit side { node, fact } (inherited node same fact found) }

end BranchSeed

/-- Close a requested fact from a stronger established fact at the same node.
The independent fact-domain theorem must prove that intersecting `actual` with
`requested` leaves `actual` unchanged.  Runtime target detection is not used
as evidence. -/
def closeFact {Fact : Type} {semantics : Semantics Fact}
    (domain : FactDomainSchema semantics) (program : Program)
    (base : List (NodeFact Fact)) (node : NodeId) (actual requested : Fact)
    (actualSound :
      Evidence
        (semantics.Entails program base { node, fact := actual })) :
    Option
      (Evidence
        (semantics.Entails program base { node, fact := requested })) := do
  let meet <- domain.proveMeet program node actual requested actual
  pure
    { proof := by
        intro valuation model baseHolds
        have established := actualSound.proof valuation model baseHolds
        exact ((meet.proof valuation model).mp established).2 }

/-- Project a proposition from any successfully replayed proof object. -/
theorem evidenceOfReplay {P : Prop} (result : Option (Evidence P))
    (success : result.isSome) : P :=
  (result.get success).proof

/-- A successful transparent replay is an ordinary kernel theorem.  This
eliminator is intentionally tiny: the substantial trust argument lives in
`replayRule`; `Option` only represents rejection of malformed quoted data. -/
theorem proofOfReplay {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    {conclusion : NodeFact Fact}
    (result : Option (Evidence (semantics.Entails program base conclusion)))
    (success : result.isSome) :
    semantics.Entails program base conclusion :=
  evidenceOfReplay result success

end Hex.Interval.Experiment.ProofEmitter
