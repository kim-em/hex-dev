/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Rule

@[expose] public section

/-!
# Programmatic arithmetic frontend

This module is the supported, tactic-independent frontend boundary. It
recursively reifies a small arithmetic term language into the exact supported
SSA `Program`, resolves operations by stable key, constructs version-zero
source facts, invokes the supported Rule/Proof replay, and closes interval
membership to ordinary bounds, conjunctions, or singleton equality. A checked
result also derives its exact `Program.Models` witness from caller source values
and authenticates that the retained root denotes the original target term, so
the caller does not assemble one semantic relation proof per SSA node.

It intentionally contains no syntax elaborator. Turning arbitrary Lean
expressions and local hypotheses into this programmatic input additionally
requires a supported quotation bridge for `Program`, `Interval`, replay events,
and caller proof terms. The existing bridge is experimental and uses different
certificate types, so importing or aliasing it here would reverse the intended
production boundary. This module accepts one flat event chronology; it does not
derive proof recipes from retained search or split trees.
-/

namespace Hex.Interval.Frontend

open Proof

/-- Function-generic arithmetic syntax. Literal values and power exponents are
explicit authenticated rows rather than package-global configuration. -/
inductive Term where
  | source (index : Nat)
  | dyadic (value : Dyadic)
  | natural (value : Nat)
  | neg (input : Term)
  | add (left right : Term)
  | sub (left right : Term)
  | mul (left right : Term)
  | pow (input : Term) (exponent : Nat)
  | abs (input : Term)
  | min (left right : Term)
  | max (left right : Term)
  | inv (input : Term)
  | div (left right : Term)
  | regularize (input : Term)
  deriving DecidableEq

/-- Reification caps are independent of interval arithmetic and proof replay
caps. `maxSources` also bounds caller fact-array traversal. `maxOperations`
admits the already-constructed configured meaning array before stable-key
lookup; it does not preempt construction of `Rule.Config` or structural
equality on caller `Term` values. `maxDepth` stops recursive descent beyond the
admitted depth, but does not itself bound the number of constructors in an
already-built branching `Term`; `maxNodes` bounds retained SSA rows, not that
caller-side construction. -/
structure Limits where
  maxSources : Nat
  maxOperations : Nat
  maxNodes : Nat
  maxDepth : Nat
  deriving DecidableEq, Repr

/-- Every resource envelope needed by this frontend is explicit. -/
structure Config where
  rule : Rule.Config
  reify : Limits
  proof : Proof.Limits

structure Entry where
  term : Term
  node : NodeId
  deriving DecidableEq

structure State where
  nodes : Array Node := #[]
  entries : Array Entry := #[]
  deriving DecidableEq

structure Result where
  program : Program
  target : NodeId
  term : Term
  entries : Array Entry
  sourceCount : Nat
  deriving DecidableEq

/-- One node-indexed version-zero fact selection. `none` means that the row
starts at domain top; `some fact` is caller-selected data whose semantic
containment must be proved separately through `InitialContext.Contains`. -/
structure InitialRow where
  node : NodeId
  fact : Option Hex.Interval := none
  deriving DecidableEq

/-- Plain node-indexed initial-fact data. The runtime builder revalidates one
row per checked reifier entry and exact node order before materializing absent
facts as `whole`. This record carries no theorem authority. -/
structure InitialContext where
  rows : Array InitialRow
  deriving DecidableEq

inductive Error where
  | sourceLimit
  | operationLimit
  | sourceIndex (index : Nat)
  | depthLimit
  | nodeLimit
  | missingOperation (key : OpKey)
  | malformedProgram
  | malformedResult
  | wrongInitialCount
  | malformedInitial
  | literalResource (node : NodeId)
  | wrongSourceCount
  | missingSource (index : Nat)
  | rule (error : Rule.BuildError)
  | replay (error : Proof.Error)
  deriving Repr

def State.find? (state : State) (term : Term) : Option NodeId :=
  (state.entries.toList.find? fun entry => entry.term == term).map (·.node)

def operationKey : Term → OpKey
  | .source _ => Rule.sourceOp.key
  | .dyadic _ => Rule.dyadicLiteralOp.key
  | .natural _ => Rule.natLiteralOp.key
  | .neg _ => Rule.negOp.key
  | .add _ _ => Rule.addOp.key
  | .sub _ _ => Rule.subOp.key
  | .mul _ _ => Rule.mulOp.key
  | .pow _ _ => Rule.powOp.key
  | .abs _ => Rule.absOp.key
  | .min _ _ => Rule.minOp.key
  | .max _ _ => Rule.maxOp.key
  | .inv _ => Rule.invOp.key
  | .div _ _ => Rule.divOp.key
  | .regularize _ => Rule.regularizeOp.key

/-- Exact built-in operation-table slot for one frontend term. Arbitrary
package meanings remain an authenticated suffix and are not reified by this
arithmetic frontend. -/
protected def Term.opIndex : Term → Nat
  | .source _ => 0
  | .neg _ => 1
  | .add _ _ => 2
  | .sub _ _ => 3
  | .mul _ _ => 4
  | .pow _ _ => 5
  | .abs _ => 6
  | .min _ _ => 7
  | .max _ _ => 8
  | .dyadic _ => 9
  | .inv _ => 10
  | .div _ _ => 11
  | .regularize _ => 12
  | .natural _ => 13

protected def Term.domain : Term → DomainId
  | .natural _ => Rule.natDomain
  | _ => Rule.realDomain

protected def Term.inputs : Term → List Term
  | .source _ | .dyadic _ | .natural _ => []
  | .neg input | .abs input | .inv input | .regularize input => [input]
  | .pow input exponent => [input, .natural exponent]
  | .add left right | .sub left right | .mul left right | .div left right |
      .min left right | .max left right => [left, right]

protected def Term.source? : Term → Option Nat
  | .source index => some index
  | _ => none

/-- Short-circuit before descending beyond the caller's admitted term depth.
This authenticates decoded `Result` terms; `reifyWithin` enforces the same
root-at-depth-zero convention while constructing them. A successful check may
visit the whole already-constructed tree; depth is not a constructor-count
cap. -/
protected def Term.depthWithin : Nat → Term → Bool
  | _, .source _ | _, .dyadic _ | _, .natural _ => true
  | 0, _ => false
  | depth + 1, .neg input | depth + 1, .pow input _ | depth + 1, .abs input |
      depth + 1, .inv input | depth + 1, .regularize input =>
      input.depthWithin depth
  | depth + 1, .add left right | depth + 1, .sub left right |
      depth + 1, .mul left right | depth + 1, .div left right |
      depth + 1, .min left right | depth + 1, .max left right =>
      left.depthWithin depth && right.depthWithin depth

/-- Real evaluation of a frontend term under exact caller source values. -/
noncomputable def Term.eval (config : Rule.Config) (sources : Nat → ℝ) : Term → ℝ
  | .source index => sources index
  | .dyadic value => toReal value
  | .natural value => (value : ℝ)
  | .neg input => -(input.eval config sources)
  | .add left right => left.eval config sources + right.eval config sources
  | .sub left right => left.eval config sources - right.eval config sources
  | .mul left right => left.eval config sources * right.eval config sources
  | .pow input exponent => input.eval config sources ^ exponent
  | .abs input => |input.eval config sources|
  | .min left right => if left.eval config sources ≤ right.eval config sources then
      left.eval config sources else right.eval config sources
  | .max left right => if left.eval config sources ≤ right.eval config sources then
      right.eval config sources else left.eval config sources
  | .inv input => (input.eval config sources)⁻¹
  | .div left right => left.eval config sources / right.eval config sources
  | .regularize input => input.eval config sources

/-- Exact built-in semantic meaning selected by a frontend term. -/
protected def Term.meaning (config : Rule.Config) : Term → Program.Meaning ℝ
  | .source _ => Rule.sourceMeaning
  | .dyadic _ => Rule.dyadicLiteralMeaning
  | .natural _ => Rule.natLiteralMeaning
  | .neg _ => Rule.negMeaning
  | .add _ _ => Rule.addMeaning
  | .sub _ _ => Rule.subMeaning
  | .mul _ _ => Rule.mulMeaning
  | .pow _ _ => Rule.powMeaning
  | .abs _ => Rule.absMeaning
  | .min _ _ => Rule.minMeaning
  | .max _ _ => Rule.maxMeaning
  | .inv _ => Rule.invMeaning
  | .div _ _ => Rule.divMeaning
  | .regularize _ => Rule.regularizeMeaning

theorem Term.meaningAt (config : Rule.Config) (term : Term) :
    (Rule.meanings config)[term.opIndex]? = some (term.meaning config) := by
  cases term <;>
    simp [Term.opIndex, Term.meaning, Rule.meanings, Rule.builtinMeanings,
      Array.getElem?_append]

theorem Term.related (config : Rule.Config) (sources : Nat → ℝ) (term : Term) :
    (term.meaning config).relation (term.inputs.map (Term.eval config sources))
      (term.eval config sources) := by
  cases term <;>
    simp [Term.inputs, Term.eval, Term.meaning, Rule.sourceMeaning, Rule.negMeaning,
      Rule.addMeaning, Rule.subMeaning, Rule.mulMeaning, Rule.powMeaning, Rule.absMeaning,
      Rule.minMeaning, Rule.maxMeaning, Rule.dyadicLiteralMeaning, Rule.natLiteralMeaning,
      Rule.invMeaning, Rule.divMeaning, Rule.regularizeMeaning, min_def, max_def]

def install (config : Config) (term : Term) (reified : List NodeId)
    (state : State) : Except Error (NodeId × State) := do
  if config.reify.maxNodes ≤ state.nodes.size then throw .nodeLimit
  let key := operationKey term
  let emptyProgram : Program :=
    { operations := (Rule.meanings config.rule).map (Program.Meaning.operation)
      nodes := #[] }
  let some (operation, signature) :=
      emptyProgram.operationEntry? key
    | throw (.missingOperation key)
  if signature.inputs.length != reified.length then throw .malformedProgram
  let node : NodeId := { index := state.nodes.size }
  let instruction : Node :=
    { domain := term.domain, op := operation, args := reified }
  pure (node,
    { nodes := state.nodes.push instruction
      entries := state.entries.push { term, node } })

def reifyTerm (config : Config) (sourceCount depth : Nat)
    (term : Term) (state : State) : Except Error (NodeId × State) := do
  if config.reify.maxDepth < depth then throw .depthLimit
  if let some node := state.find? term then return (node, state)
  match term with
  | .source index =>
      if sourceCount ≤ index then throw (.sourceIndex index)
      install config term [] state
  | .dyadic _ | .natural _ => install config term [] state
  | .pow input exponent =>
      let (inputNode, state) ← reifyTerm config sourceCount (depth + 1) input state
      if config.reify.maxDepth < depth + 1 then throw .depthLimit
      let exponentTerm := .natural exponent
      let (exponentNode, state) ← match state.find? exponentTerm with
        | some node => pure (node, state)
        | none => install config exponentTerm [] state
      install config term [inputNode, exponentNode] state
  | .neg input | .abs input | .inv input | .regularize input =>
      let (node, state) ← reifyTerm config sourceCount (depth + 1) input state
      install config term [node] state
  | .add left right | .sub left right | .mul left right | .div left right |
      .min left right | .max left right =>
      let (leftNode, state) ← reifyTerm config sourceCount (depth + 1) left state
      let (rightNode, state) ← reifyTerm config sourceCount (depth + 1) right state
      install config term [leftNode, rightNode] state

/-- Recursively construct a checked SSA program. Failure returns no partial
result. Exact-expression CSE is structural equality on `Term`. -/
def reifyWithin (config : Config) (sourceCount : Nat) (target : Term) :
    Except Error Result := do
  if config.reify.maxSources < sourceCount then throw .sourceLimit
  if config.reify.maxOperations < (Rule.meanings config.rule).size then
    throw .operationLimit
  let (targetNode, state) ← reifyTerm config sourceCount 0 target {}
  let program : Program :=
    { operations := (Rule.meanings config.rule).map (Program.Meaning.operation)
      nodes := state.nodes }
  if !program.check then throw .malformedProgram
  pure { program, target := targetNode, term := target, entries := state.entries, sourceCount }

def Result.sourceNode? (result : Result) (index : Nat) : Option NodeId :=
  (result.entries.toList.find? fun entry => entry.term == .source index).map (·.node)

/-- Default node-indexed initial context: every checked reifier row starts at
domain top. -/
def Result.initialContext (result : Result) : InitialContext :=
  { rows := result.entries.map fun entry => { node := entry.node } }

/-- Replace one node-indexed selection only when the requested node is present
at its exact slot. A mistargeted or out-of-range write refuses rather than
silently leaving a `whole` fact in place. `inputInitialWithin` remains the
authoritative full-context validator. -/
def InitialContext.setFact (initial : InitialContext) (node : NodeId)
    (fact : Hex.Interval) : Except Error InitialContext :=
  match initial.rows[node.index]? with
  | none => throw .malformedInitial
  | some row =>
      if row.node != node then
        throw .malformedInitial
      else
        pure { rows := initial.rows.set! node.index { row with fact := some fact } }

/-- Materialize absent selections as domain top in exact row order. -/
def InitialContext.facts (initial : InitialContext) : Array Hex.Interval :=
  initial.rows.map fun row => row.fact.getD Hex.Interval.whole

/-- One initial row must name the exact reifier node at the same array slot. -/
protected def InitialContext.slotCheck (initial : InitialContext)
    (result : Result) (index : Nat) : Bool :=
  match initial.rows[index]?, result.entries[index]? with
  | some row, some entry => row.node == entry.node
  | _, _ => false

/-- Authenticate exact row count and node order. The caller checks array caps
before invoking this bounded scan. -/
def InitialContext.check (initial : InitialContext) (result : Result) : Bool :=
  initial.rows.size == result.entries.size &&
    (List.range initial.rows.size).all (initial.slotCheck result)

/-- Exact semantic authority for node-indexed initial facts. The relation is
position-for-position with the checked reifier table, pins the named node, and
relates every selected fact to that row's exact `Term.eval`. An absent fact is
the public `whole` value and therefore has a trivial caller proof. -/
def InitialContext.Contains (initial : InitialContext) (config : Rule.Config)
    (values : Nat → ℝ) (result : Result) : Prop :=
  List.Forall₂
    (fun row entry =>
      row.node = entry.node ∧
        (row.fact.getD Hex.Interval.whole).Contains (entry.term.eval config values))
    initial.rows.toList result.entries.toList

protected def Result.inputsMatch (entries : Array Entry) : List Term → List NodeId → Bool
  | [], [] => true
  | term :: terms, node :: nodes =>
      (entries[node.index]?).any (fun entry => entry.term == term) &&
        Result.inputsMatch entries terms nodes
  | _, _ => false

protected def Result.uniqueTerms : List Entry → Bool
  | [] => true
  | entry :: entries =>
      !(entries.any fun other => other.term == entry.term) && Result.uniqueTerms entries

/-- Authenticate the transparent reification record against its exact program.
This pins one entry to every SSA node, structural CSE, operation keys and
ordered child edges. The caller-facing resource checks run before this bounded
scan; structural equality of the already-constructed `Term` values remains a
programmatic-caller cost. -/
protected def Result.slotCheck (result : Result) (index : Nat) : Bool :=
  match result.entries[index]?, result.program.nodes[index]? with
  | some entry, some node =>
      entry.node.index == index &&
        node.op.index == entry.term.opIndex &&
        (result.program.operation? node.op).any
          (fun operation => operation.key == operationKey entry.term) &&
        (match entry.term with
          | .source source => source < result.sourceCount
          | _ => true) &&
        Result.inputsMatch result.entries entry.term.inputs node.args
  | _, _ => false

protected def Result.headerCheck (result : Result) : Bool :=
  result.entries.size == result.program.nodes.size &&
    Result.uniqueTerms result.entries.toList &&
    (result.entries[result.target.index]?).any (fun entry => entry.term == result.term)

def Result.check (result : Result) : Bool :=
  result.headerCheck && (List.range result.entries.size).all result.slotCheck

/-- Every retained recursive term respects the same depth cap used by the
constructor. The array-size preflight must run before this traversal. -/
def Result.depthCheck (result : Result) (maxDepth : Nat) : Bool :=
  result.entries.toList.all (fun entry => entry.term.depthWithin maxDepth)

protected noncomputable def Result.valueAt (config : Rule.Config) (sources : Nat → ℝ)
    (entries : Array Entry) (node : NodeId) : ℝ :=
  (entries[node.index]?).map (fun entry => entry.term.eval config sources) |>.getD 0

/-- Evaluate the exact term retained at one checked SSA node. Out-of-range
values are irrelevant because `Program.Models` quantifies only program nodes. -/
noncomputable def Result.valuation (config : Rule.Config) (sources : Nat → ℝ)
    (result : Result) (node : NodeId) : ℝ :=
  Result.valueAt config sources result.entries node

/-- Version-zero fact selected for one authenticated reifier entry. Source
nodes receive the corresponding caller fact; every computed node receives
domain top. -/
def Result.seed (sources : Array Hex.Interval) (entry : Entry) : Hex.Interval :=
  match entry.term.source? with
  | some index => sources[index]?.getD Hex.Interval.whole
  | none => Hex.Interval.whole

/-- Source-only convenience context retained for the original frontend API.
Source rows select their caller facts and every computed row defaults to
`whole`. -/
def Result.sourceInitial (result : Result)
    (sources : Array Hex.Interval) : InitialContext :=
  { rows := result.entries.map fun entry =>
      { node := entry.node
        fact := entry.term.source?.bind fun index => sources[index]? } }

/-- Checked mixed initial context. Source rows use caller facts; literal rows
use exact singletons; every arithmetic row stays at domain top. Literal
construction failure is transactional. -/
def Result.seedInitialWithin (config : Rule.Config) (result : Result)
    (sources : Array Hex.Interval) : Except Error InitialContext := do
  let mut rows : Array InitialRow := #[]
  for entry in result.entries do
    let fact ← match entry.term with
      | .source index => pure sources[index]?
      | .dyadic value =>
          match Rule.ready? (singletonWithin config.endpoint value) with
          | some fact => pure (some fact)
          | none => throw (.literalResource entry.node)
      | .natural value =>
          match Rule.ready? (singletonWithin config.endpoint (Dyadic.ofInt value)) with
          | some fact => pure (some fact)
          | none => throw (.literalResource entry.node)
      | _ => pure none
    rows := rows.push { node := entry.node, fact }
  pure { rows }

theorem whole_contains (value : ℝ) : Hex.Interval.whole.Contains value := by
  change Raw.Contains Hex.Interval.whole.view value
  rw [Hex.Interval.view_whole]
  exact ⟨trivial, trivial⟩

theorem dyadic_contains {config : Rule.Config} {values : Nat → ℝ} {value : Dyadic}
    {fact : Hex.Interval} (checked : Rule.ready?
      (singletonWithin config.endpoint value) = some fact) :
    fact.Contains ((Term.dyadic value).eval config values) := by
  simpa [Term.eval] using Rule.constant_mem (Rule.ready?_eq checked)

theorem natural_contains {config : Rule.Config} {values : Nat → ℝ} {value : Nat}
    {fact : Hex.Interval} (checked : Rule.ready?
      (singletonWithin config.endpoint (Dyadic.ofInt value)) = some fact) :
    fact.Contains ((Term.natural value).eval config values) := by
  have member := Rule.constant_mem (Rule.ready?_eq checked)
  simpa [Term.eval, Rule.toReal_ofInt] using member

/-- Exact version-zero fact array determined by the retained node/term rows. -/
def Result.facts (result : Result) (sources : Array Hex.Interval) : Array Hex.Interval :=
  result.entries.map (Result.seed sources)

theorem Result.sourceInitial_facts (result : Result) (sources : Array Hex.Interval) :
    (result.sourceInitial sources).facts = result.facts sources := by
  simp only [Result.sourceInitial, InitialContext.facts, Result.facts, Array.map_map]
  have fnEq :
      ((fun row : InitialRow => row.fact.getD Hex.Interval.whole) ∘
          fun entry : Entry =>
            { node := entry.node
              fact := entry.term.source?.bind fun index => sources[index]? }) =
        Result.seed sources := by
    funext entry
    cases found : entry.term.source? <;>
      simp [Result.seed, Function.comp_apply, found]
  rw [fnEq]

private theorem Result.slot_of_check (result : Result) (checked : result.check)
    {index : Nat} (within : index < result.entries.size) : result.slotCheck index := by
  have split : result.headerCheck = true ∧
      (List.range result.entries.size).all result.slotCheck = true := by
    simpa [Result.check, Bool.and_eq_true] using checked
  have all := split.2
  simp only [List.all_eq_true] at all
  exact all index (List.mem_range.mpr within)

private theorem Result.inputs_eval (config : Rule.Config) (sources : Nat → ℝ)
    (entries : Array Entry) {terms : List Term} {nodes : List NodeId}
    (matched : Result.inputsMatch entries terms nodes) :
    nodes.map (Result.valueAt config sources entries) = terms.map (Term.eval config sources) := by
  induction terms generalizing nodes with
  | nil => cases nodes <;> simp [Result.inputsMatch] at matched ⊢
  | cons term terms ih =>
      cases nodes with
      | nil => simp [Result.inputsMatch] at matched
      | cons node nodes =>
          simp only [Result.inputsMatch, Bool.and_eq_true] at matched
          generalize found : entries[node.index]? = entry? at matched
          cases entry? with
          | none => simp at matched
          | some entry =>
              have termEq : entry.term = term := by simpa using matched.1
              simp [Result.valueAt, found, termEq, ih matched.2]

/-- Source containment is the only caller-supplied semantic obligation for the
version-zero facts constructed by `Result.facts`. -/
def SourcesContain (values : Nat → ℝ) (sources : Array Hex.Interval) : Prop :=
  ∀ index (fact : Hex.Interval), sources[index]? = some fact → fact.Contains (values index)

/-- Total lookup used when a Meta caller quotes a finite source-expression
list. Indices outside the list are irrelevant to `SourcesContain`. -/
def valuesAt (values : List ℝ) (index : Nat) : ℝ :=
  values[index]?.getD 0

/-- Convert one membership proof per quoted source into the frontend's exact
array-indexed source obligation. -/
theorem SourcesContain.ofForall₂ {values : List ℝ} {sources : List Hex.Interval}
    (holds : List.Forall₂ (fun value source => source.Contains value) values sources) :
    SourcesContain (valuesAt values) sources.toArray := by
  induction holds with
  | nil =>
      intro index fact found
      simp at found
  | @cons value source values sources member _ ih =>
      intro index fact found
      cases index with
      | zero =>
          simp at found
          subst fact
          simpa [valuesAt] using member
      | succ index =>
          exact ih index fact (by simpa using found)

/-- Meta-facing bridge: one quoted row/entry containment proof per position is
exactly the generalized initial-context authority. -/
theorem InitialContext.Contains.ofForall₂
    {initial : InitialContext} {config : Rule.Config} {values : Nat → ℝ}
    {result : Result}
    (holds : List.Forall₂
      (fun row entry =>
        row.node = entry.node ∧
          (row.fact.getD Hex.Interval.whole).Contains (entry.term.eval config values))
      initial.rows.toList result.entries.toList) :
    initial.Contains config values result :=
  holds

/-- Every materialized initial fact contains the exact value of its node in
the checked reifier valuation. The proof authority is positional
`InitialContext.Contains`; the plain context alone proves nothing. -/
theorem InitialContext.fact_contains
    (initial : InitialContext) (config : Rule.Config) (values : Nat → ℝ)
    (result : Result) (holds : initial.Contains config values result)
    (index : Nat) (within : index < initial.rows.size) :
    initial.facts[index]'(by simpa [InitialContext.facts] using within) |>.Contains
      (result.valuation config values { index }) := by
  let row := initial.rows[index]'within
  have lengths : initial.rows.size = result.entries.size := by
    simpa [InitialContext.Contains] using List.Forall₂.length_eq holds
  have entryWithin : index < result.entries.size := by simpa [lengths] using within
  let entry := result.entries[index]'entryWithin
  have entryFound : result.entries[index]? = some entry := by simp [entry]
  have related := List.Forall₂.get holds (by simpa using within) (by simpa using entryWithin)
  have factEq :
      initial.facts[index]'(by simpa [InitialContext.facts] using within) =
        row.fact.getD Hex.Interval.whole := by
    simp [InitialContext.facts, row]
  have valueEq : result.valuation config values { index } = entry.term.eval config values := by
    simp [Result.valuation, Result.valueAt, entryFound]
  rw [factEq, valueEq]
  simpa [row, entry] using related.2

theorem Result.seed_contains (config : Rule.Config) (values : Nat → ℝ)
    (result : Result) (sources : Array Hex.Interval) (checked : result.check)
    (sourceSize : sources.size = result.sourceCount)
    (sourceHolds : SourcesContain values sources)
    (index : Nat) (within : index < result.entries.size) :
    (result.facts sources)[index]'(by simpa [Result.facts] using within) |>.Contains
      (result.valuation config values { index }) := by
  let entry := result.entries[index]'within
  have entryFound : result.entries[index]? = some entry := by simp [entry]
  have slot := result.slot_of_check checked within
  generalize nodeFound : result.program.nodes[index]? = node? at slot
  cases node? with
  | none => simp [Result.slotCheck, entryFound, nodeFound] at slot
  | some node =>
      simp only [Result.slotCheck, entryFound, nodeFound, Bool.and_eq_true, beq_iff_eq] at slot
      have sourceWithin := slot.1.2
      cases sourceTerm : entry.term.source? with
      | some source =>
          have termEq : entry.term = .source source := by
            cases h : entry.term <;> simp [Term.source?, h] at sourceTerm
            case source index =>
              subst source
              simpa using h
          have sourceLt : source < result.sourceCount := by simpa [termEq] using sourceWithin
          have sourceArrayWithin : source < sources.size := by simpa [sourceSize] using sourceLt
          let sourceFact := sources[source]'sourceArrayWithin
          have sourceFound : sources[source]? = some sourceFact := by simp [sourceFact]
          have member := sourceHolds source sourceFact sourceFound
          have seeded :
              (result.facts sources)[index]'(by simpa [Result.facts] using within) = sourceFact := by
            simp [Result.facts, Result.seed, entry, termEq, Term.source?, sourceFound]
          have valued : result.valuation config values { index } = values source := by
            simp [Result.valuation, Result.valueAt, entryFound, termEq, Term.eval]
          rw [seeded, valued]
          exact member
      | none =>
          have seeded :
              (result.facts sources)[index]'(by simpa [Result.facts] using within) =
                Hex.Interval.whole := by
            simp [Result.facts, Result.seed, entry, sourceTerm]
          rw [seeded]
          change Hex.Interval.whole.Contains _
          change Raw.Contains Hex.Interval.whole.view _
          rw [Hex.Interval.view_whole]
          exact ⟨trivial, trivial⟩

/-- The checked reification record determines a mathematical model from source
values; callers do not reconstruct one semantic relation per SSA node. -/
theorem Result.models (config : Rule.Config) (sources : Nat → ℝ)
    (result : Result) (checked : result.check)
    (operations : result.program.operations =
      (Rule.meanings config).map (Program.Meaning.operation)) :
    Program.Models (Rule.meanings config) result.program
      (result.valuation config sources) := by
  refine ⟨operations, ?_⟩
  intro node instruction found
  have split : result.headerCheck = true ∧
      (List.range result.entries.size).all result.slotCheck = true := by
    simpa [Result.check, Bool.and_eq_true] using checked
  have header := split.1
  simp only [Result.headerCheck, Bool.and_eq_true, beq_iff_eq] at header
  have nodeFound : result.program.nodes[node.index]? = some instruction := by
    simpa [Program.node?] using found
  have nodeWithin : node.index < result.program.nodes.size := by
    by_contra outside
    have none : result.program.nodes[node.index]? = none := by simp [outside]
    rw [none] at nodeFound
    contradiction
  have entryWithin : node.index < result.entries.size := by
    simpa [header.1] using nodeWithin
  let entry := result.entries[node.index]'entryWithin
  have entryFound : result.entries[node.index]? = some entry := by simp [entry]
  have slot := result.slot_of_check checked entryWithin
  simp only [Result.slotCheck, entryFound, nodeFound,
    Bool.and_eq_true, beq_iff_eq] at slot
  have opIndex := slot.1.1.1.2
  have inputs := slot.2
  refine ⟨entry.term.meaning config, ?_, ?_⟩
  · rw [opIndex]
    exact entry.term.meaningAt config
  · have values := Result.inputs_eval config sources result.entries inputs
    have values' : instruction.args.map (result.valuation config sources) =
        entry.term.inputs.map (Term.eval config sources) := by
      change instruction.args.map (Result.valueAt config sources result.entries) =
        entry.term.inputs.map (Term.eval config sources)
      exact values
    have atNode : result.valuation config sources node = entry.term.eval config sources := by
      simp [Result.valuation, Result.valueAt, entryFound]
    rw [values', atNode]
    exact entry.term.related config sources

theorem Result.target_eval (config : Rule.Config) (sources : Nat → ℝ)
    (result : Result) (checked : result.check) :
    result.valuation config sources result.target = result.term.eval config sources := by
  have split : result.headerCheck = true ∧
      (List.range result.entries.size).all result.slotCheck = true := by
    simpa [Result.check, Bool.and_eq_true] using checked
  have header := split.1
  simp only [Result.headerCheck, Bool.and_eq_true, beq_iff_eq] at header
  generalize found : result.entries[result.target.index]? = entry? at header
  cases entry? with
  | none => simp at header
  | some entry =>
      have root := header.2
      simp only [Option.any_some, beq_iff_eq] at root
      have termEq : entry.term = result.term := root
      simp [Result.valuation, Result.valueAt, found, termEq]

/-- Proof-carrying semantic interpretation derived from one checked reifier
result. Its valuation is fixed by the retained term at every node, and the
authenticated root evaluates to the caller's original target term. -/
structure Model (config : Rule.Config) (sources : Nat → ℝ) (result : Result) : Type where
  checked : result.check
  sound : Program.Models (Rule.meanings config) result.program
    (result.valuation config sources)
  target : result.valuation config sources result.target = result.term.eval config sources

/-- Recheck all caps and structural bindings before deriving the semantic
model. Failure returns no partially authenticated model. Caller source values
are an opaque function and are not traversed by this operation. -/
def modelWithin (config : Config) (sources : Nat → ℝ) (result : Result) :
    Except Error (Model config.rule sources result) := do
  if config.reify.maxSources < result.sourceCount then throw .sourceLimit
  let meanings := Rule.meanings config.rule
  if config.reify.maxOperations < meanings.size ||
      config.reify.maxOperations < result.program.operations.size then
    throw .operationLimit
  if config.reify.maxNodes < result.program.nodes.size ||
      config.reify.maxNodes < result.entries.size then throw .nodeLimit
  if !result.depthCheck config.reify.maxDepth then throw .depthLimit
  if result.target.index ≥ result.program.nodes.size || !result.program.check then
    throw .malformedProgram
  if operations : result.program.operations = meanings.map (Program.Meaning.operation) then
    if checked : result.check then
      pure {
        checked
        sound := result.models config.rule sources checked operations
        target := result.target_eval config.rule sources checked }
    else throw .malformedResult
  else throw .malformedProgram

/-- Project the exact semantic model from a transparently successful checked
frontend result. Meta callers construct `success` by kernel reduction of the
quoted configuration and reifier data. -/
def modelOfCheck {config : Config} {sources : Nat → ℝ} {result : Result}
    (checked : Except Error (Model config.rule sources result))
    (success : checked.toOption.isSome = true) : Model config.rule sources result :=
  checked.toOption.get success

/-- Shared bounded validation for proof-input constructors. `initialSize` is
the caller's version-zero row count and is charged before any row scan. -/
def inputCheckWithin (config : Config) (result : Result) (initialSize : Nat) :
    Except Error Unit := do
  if config.reify.maxSources < result.sourceCount then throw .sourceLimit
  let meanings := Rule.meanings config.rule
  if config.reify.maxOperations < meanings.size ||
      config.reify.maxOperations < result.program.operations.size then
    throw .operationLimit
  if config.reify.maxNodes < result.program.nodes.size ||
      config.reify.maxNodes < result.entries.size ||
      config.reify.maxNodes < initialSize then throw .nodeLimit
  if !result.depthCheck config.reify.maxDepth then throw .depthLimit
  if result.target.index ≥ result.program.nodes.size || !result.program.check then
    throw .malformedProgram
  if result.program.operations != meanings.map (Program.Meaning.operation) then
    throw .malformedProgram
  if !result.check then throw .malformedResult
  pure ()

/-- Revalidate every resource cap and structural binding before materializing
one authenticated version-zero fact per reifier node. Caller-selected facts
remain plain data; only `InitialContext.Contains` supplies semantic authority.
Failure returns no partially constructed input. -/
def inputInitialWithin (config : Config) (scope : Policy.ScopeId) (result : Result)
    (initial : InitialContext) (target : Hex.Interval) :
    Except Error (Proof.Input Hex.Interval) := do
  inputCheckWithin config result initial.rows.size
  if initial.rows.size != result.entries.size then throw .wrongInitialCount
  if !initial.check result then throw .malformedInitial
  pure {
    scope
    program := result.program
    facts := initial.facts
    target := { node := result.target, fact := target } }

/-- Source-only convenience wrapper for the original frontend API. It binds
every selected source exactly once and leaves computed rows at domain top. -/
def inputWithin (config : Config) (scope : Policy.ScopeId) (result : Result)
    (sources : Array Hex.Interval) (target : Hex.Interval) :
    Except Error (Proof.Input Hex.Interval) := do
  inputCheckWithin config result result.entries.size
  if sources.size != result.sourceCount then throw .wrongSourceCount
  for index in [0:result.sourceCount] do
    let some _ := result.sourceNode? index | throw (.missingSource index)
  let initial := result.sourceInitial sources
  if initial.rows.size != result.entries.size then throw .wrongInitialCount
  if !initial.check result then throw .malformedInitial
  pure {
    scope
    program := result.program
    facts := initial.facts
    target := { node := result.target, fact := target } }

/-- The exact `Result.facts` seed array discharges every computed top fact;
only caller source containment remains. -/
theorem Result.initial_contains (config : Rule.Config) (values : Nat → ℝ)
    (result : Result) (sourceFacts : Array Hex.Interval) (checked : result.check)
    (sourceSize : sourceFacts.size = result.sourceCount)
    (sourceHolds : SourcesContain values sourceFacts)
    (input : Proof.Input Hex.Interval)
    (facts : input.facts = result.facts sourceFacts) :
    ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config values fact.node) := by
  intro fact member
  rw [Proof.initialBase, List.mem_ofFn] at member
  obtain ⟨index, rfl⟩ := member
  have within : index.val < result.entries.size := by
    have sizeEq : input.facts.size = result.entries.size := by
      rw [facts]
      simp [Result.facts]
    exact sizeEq ▸ index.isLt
  have seeded := result.seed_contains config values sourceFacts checked sourceSize
    sourceHolds index.val within
  simpa [facts] using seeded

/-- Positional containment authority discharges every caller-selected initial
fact, including facts installed on computed nodes. -/
theorem InitialContext.initial_contains (initial : InitialContext)
    (config : Rule.Config) (values : Nat → ℝ) (result : Result)
    (holds : initial.Contains config values result)
    (input : Proof.Input Hex.Interval) (facts : input.facts = initial.facts) :
    ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config values fact.node) := by
  intro fact member
  rw [Proof.initialBase, List.mem_ofFn] at member
  obtain ⟨index, rfl⟩ := member
  have within : index.val < initial.rows.size := by
    have sizeEq : input.facts.size = initial.rows.size := by
      rw [facts]
      simp [InitialContext.facts]
    exact sizeEq ▸ index.isLt
  have selected := initial.fact_contains config values result holds index.val within
  simpa [facts] using selected

/-- Bounded supported registry assembly followed by exact chronological replay.
Neither the reifier nor the caller-supplied event list has proof authority. The
proof layer reauthenticates every event; retained search-tree recipe extraction
is a separate boundary. -/
def replay (config : Config) (input : Proof.Input Hex.Interval)
    (events : List (Proof.Event Hex.Interval)) (finalVersion : Nat)
    (finalProgram : Program) (result : SeenVersion) :
    Except Error (Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target)) := do
  match Rule.buildWithin config.proof config.rule input.program with
  | .error error => throw (.rule error)
  | .ok registry =>
      match Proof.replay config.proof registry (Rule.domain config.rule)
          (Rule.laws config.rule) input events finalVersion finalProgram result with
      | .ok evidence => pure evidence
      | .error error => throw (.replay error)

/-- Eliminate replay evidence at one exact valuation and caller context. -/
theorem close (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node)) :
    input.target.fact.Contains (valuation input.target.node) := by
  exact evidence.proof valuation model (by
    intro fact member
    simpa [Rule.semantics, Proof.Semantics.ofMeanings] using assumptions fact member)

/-- Eliminate replay evidence at the exact model and target root derived from
the checked reification result. The caller supplies source values and proves
only that its version-zero interval facts contain those values. -/
theorem closeTerm (config : Config) (result : Result) (sources : Nat → ℝ)
    (model : Model config.rule sources result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config.rule sources fact.node)) :
    input.target.fact.Contains (result.term.eval config.rule sources) := by
  have programModel : Program.Models (Rule.meanings config.rule) input.program
      (result.valuation config.rule sources) := by
    simpa [program] using model.sound
  have member := close config input evidence (result.valuation config.rule sources)
    programModel assumptions
  rw [target, model.target] at member
  exact member

/-- Close both endpoint predicates at the checked reifier target. -/
theorem closeTermBounds (config : Config) (result : Result) (sources : Nat → ℝ)
    (model : Model config.rule sources result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config.rule sources fact.node))
    (lower : Lower) (upper : Upper)
    (shape : input.target.fact.view = .bounds lower upper) :
    lower.Contains (result.term.eval config.rule sources) ∧
      upper.Contains (result.term.eval config.rule sources) := by
  have member := closeTerm config result sources model input evidence program target assumptions
  change input.target.fact.view.Contains (result.term.eval config.rule sources) at member
  simpa [shape, Raw.Contains] using member

/-- Close a lower endpoint predicate at the checked reifier target. -/
theorem closeTermLower (config : Config) (result : Result) (sources : Nat → ℝ)
    (model : Model config.rule sources result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config.rule sources fact.node))
    (value : Dyadic) (strict : Bool) (upper : Upper)
    (shape : input.target.fact.view = .bounds (.finite value strict) upper) :
    (Lower.finite value strict).Contains (result.term.eval config.rule sources) :=
  (closeTermBounds config result sources model input evidence program target assumptions
    _ _ shape).1

/-- Close an upper endpoint predicate at the checked reifier target. -/
theorem closeTermUpper (config : Config) (result : Result) (sources : Nat → ℝ)
    (model : Model config.rule sources result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config.rule sources fact.node))
    (lower : Lower) (value : Dyadic) (strict : Bool)
    (shape : input.target.fact.view = .bounds lower (.finite value strict)) :
    (Upper.finite value strict).Contains (result.term.eval config.rule sources) :=
  (closeTermBounds config result sources model input evidence program target assumptions
    _ _ shape).2

/-- Close a singleton equality at the checked reifier target. -/
theorem closeTermSingleton (config : Config) (result : Result) (sources : Nat → ℝ)
    (model : Model config.rule sources result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (result.valuation config.rule sources fact.node))
    (value : Dyadic)
    (shape : input.target.fact.view =
      .bounds (.finite value false) (.finite value false)) :
    result.term.eval config.rule sources = toReal value := by
  rcases closeTermBounds config result sources model input evidence program target assumptions
    _ _ shape with ⟨lower, upper⟩
  exact le_antisymm upper lower

/-- Close the target from an exact node-indexed initial context. The context's
plain data is authenticated structurally by `inputInitialWithin`; `holds` is
the separate kernel-checked containment authority consumed here. -/
theorem closeInitial (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (initial : InitialContext)
    (facts : input.facts = initial.facts)
    (holds : initial.Contains config.rule values result) :
    input.target.fact.Contains (result.term.eval config.rule values) :=
  closeTerm config result values model input evidence program target
    (initial.initial_contains config.rule values result holds input facts)

theorem closeInitialBounds (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (initial : InitialContext)
    (facts : input.facts = initial.facts)
    (holds : initial.Contains config.rule values result)
    (lower : Lower) (upper : Upper)
    (shape : input.target.fact.view = .bounds lower upper) :
    lower.Contains (result.term.eval config.rule values) ∧
      upper.Contains (result.term.eval config.rule values) := by
  have member := closeInitial config result values model input evidence program target initial
    facts holds
  change input.target.fact.view.Contains (result.term.eval config.rule values) at member
  simpa [shape, Raw.Contains] using member

theorem closeInitialLower (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (initial : InitialContext)
    (facts : input.facts = initial.facts)
    (holds : initial.Contains config.rule values result)
    (value : Dyadic) (strict : Bool) (upper : Upper)
    (shape : input.target.fact.view = .bounds (.finite value strict) upper) :
    (Lower.finite value strict).Contains (result.term.eval config.rule values) :=
  (closeInitialBounds config result values model input evidence program target initial facts holds
    _ _ shape).1

theorem closeInitialUpper (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (initial : InitialContext)
    (facts : input.facts = initial.facts)
    (holds : initial.Contains config.rule values result)
    (lower : Lower) (value : Dyadic) (strict : Bool)
    (shape : input.target.fact.view = .bounds lower (.finite value strict)) :
    (Upper.finite value strict).Contains (result.term.eval config.rule values) :=
  (closeInitialBounds config result values model input evidence program target initial facts holds
    _ _ shape).2

theorem closeInitialSingleton (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (initial : InitialContext)
    (facts : input.facts = initial.facts)
    (holds : initial.Contains config.rule values result)
    (value : Dyadic)
    (shape : input.target.fact.view =
      .bounds (.finite value false) (.finite value false)) :
    result.term.eval config.rule values = toReal value := by
  rcases closeInitialBounds config result values model input evidence program target initial facts
    holds _ _ shape with ⟨lower, upper⟩
  exact le_antisymm upper lower

/-- Close the target from caller source facts. Computed version-zero nodes are
seeded with `whole` and discharged by `Result.initial_contains`. -/
theorem closeSources (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (sourceFacts : Array Hex.Interval)
    (sourceSize : sourceFacts.size = result.sourceCount)
    (facts : input.facts = result.facts sourceFacts)
    (sourceHolds : SourcesContain values sourceFacts) :
    input.target.fact.Contains (result.term.eval config.rule values) :=
  closeTerm config result values model input evidence program target
    (result.initial_contains config.rule values sourceFacts model.checked sourceSize
      sourceHolds input facts)

theorem closeSourcesBounds (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (sourceFacts : Array Hex.Interval)
    (sourceSize : sourceFacts.size = result.sourceCount)
    (facts : input.facts = result.facts sourceFacts)
    (sourceHolds : SourcesContain values sourceFacts)
    (lower : Lower) (upper : Upper)
    (shape : input.target.fact.view = .bounds lower upper) :
    lower.Contains (result.term.eval config.rule values) ∧
      upper.Contains (result.term.eval config.rule values) := by
  have member := closeSources config result values model input evidence program target sourceFacts
    sourceSize facts sourceHolds
  change input.target.fact.view.Contains (result.term.eval config.rule values) at member
  simpa [shape, Raw.Contains] using member

theorem closeSourcesLower (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (sourceFacts : Array Hex.Interval)
    (sourceSize : sourceFacts.size = result.sourceCount)
    (facts : input.facts = result.facts sourceFacts)
    (sourceHolds : SourcesContain values sourceFacts)
    (value : Dyadic) (strict : Bool) (upper : Upper)
    (shape : input.target.fact.view = .bounds (.finite value strict) upper) :
    (Lower.finite value strict).Contains (result.term.eval config.rule values) :=
  (closeSourcesBounds config result values model input evidence program target sourceFacts
    sourceSize facts sourceHolds _ _ shape).1

theorem closeSourcesUpper (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (sourceFacts : Array Hex.Interval)
    (sourceSize : sourceFacts.size = result.sourceCount)
    (facts : input.facts = result.facts sourceFacts)
    (sourceHolds : SourcesContain values sourceFacts)
    (lower : Lower) (value : Dyadic) (strict : Bool)
    (shape : input.target.fact.view = .bounds lower (.finite value strict)) :
    (Upper.finite value strict).Contains (result.term.eval config.rule values) :=
  (closeSourcesBounds config result values model input evidence program target sourceFacts
    sourceSize facts sourceHolds _ _ shape).2

theorem closeSourcesSingleton (config : Config) (result : Result) (values : Nat → ℝ)
    (model : Model config.rule values result) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (program : input.program = result.program)
    (target : input.target.node = result.target)
    (sourceFacts : Array Hex.Interval)
    (sourceSize : sourceFacts.size = result.sourceCount)
    (facts : input.facts = result.facts sourceFacts)
    (sourceHolds : SourcesContain values sourceFacts)
    (value : Dyadic)
    (shape : input.target.fact.view =
      .bounds (.finite value false) (.finite value false)) :
    result.term.eval config.rule values = toReal value := by
  rcases closeSourcesBounds config result values model input evidence program target sourceFacts
    sourceSize facts sourceHolds _ _ shape with ⟨lower, upper⟩
  exact le_antisymm upper lower

/-- Close both endpoint predicates. This is the conjunction frontend used for
two-sided inequality goals. -/
theorem closeBounds (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (lower : Lower) (upper : Upper)
    (shape : input.target.fact.view = .bounds lower upper) :
    lower.Contains (valuation input.target.node) ∧
      upper.Contains (valuation input.target.node) := by
  have member := close config input evidence valuation model assumptions
  change input.target.fact.view.Contains (valuation input.target.node) at member
  simpa [shape, Raw.Contains] using member

theorem closeLower (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (value : Dyadic) (strict : Bool) (upper : Upper)
    (shape : input.target.fact.view = .bounds (.finite value strict) upper) :
    (Lower.finite value strict).Contains (valuation input.target.node) :=
  (closeBounds config input evidence valuation model assumptions _ _ shape).1

theorem closeUpper (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (lower : Lower) (value : Dyadic) (strict : Bool)
    (shape : input.target.fact.view = .bounds lower (.finite value strict)) :
    (Upper.finite value strict).Contains (valuation input.target.node) :=
  (closeBounds config input evidence valuation model assumptions _ _ shape).2

/-- A closed singleton interval closes an equality goal. -/
theorem closeSingleton (config : Config) (input : Proof.Input Hex.Interval)
    (evidence : Proof.Evidence
      ((Rule.semantics config.rule).Entails input.program
        (Proof.initialBase input) input.target))
    (valuation : NodeId → ℝ)
    (model : Program.Models (Rule.meanings config.rule) input.program valuation)
    (assumptions : ∀ fact, fact ∈ Proof.initialBase input →
      fact.fact.Contains (valuation fact.node))
    (value : Dyadic)
    (shape : input.target.fact.view =
      .bounds (.finite value false) (.finite value false)) :
    valuation input.target.node = toReal value := by
  rcases closeBounds config input evidence valuation model assumptions _ _ shape with
    ⟨lower, upper⟩
  exact le_antisymm upper lower

end Hex.Interval.Frontend
