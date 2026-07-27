/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

@[expose] public section

/-!
# D2 centered-product vertical

This module is a deliberately small, Mathlib-free proof-facing vertical for
bounded expression instantiation.  Starting from `x * (1 - x)`, `centerV1`
adds the centered expression

`1 / 4 - (x - 1 / 2) ^ 2`

in one generation, records a checked equality edge between the two forms, and
checks a finite-closed interval trace ending in `[0, 1 / 4]` at the original
product node.

The program and trace use `List`, rather than `Array`, so ordinary downstream
kernel reduction can inspect every proof-facing definition under the module
system.  All data are untrusted: `checkFixture` recomputes topology, the exact
`centerV1` shape, interval-rule outputs, and equality transport.
-/

namespace Hex.Interval.Experiment.Center

/-! ## Typed expression program -/

/-- Domain tag for the provisional typed expression language. -/
inductive Ty where
  | real
  deriving DecidableEq, Repr

/-- A typed node identifier. -/
structure NodeId (ty : Ty) where
  index : Nat
  deriving DecidableEq, Repr

/-- Operations needed by the centered-product vertical. -/
inductive Prim : Ty → Type where
  | var (source : Nat) : Prim .real
  | lit (value : Dyadic) : Prim .real
  | sub (left right : NodeId .real) : Prim .real
  | mul (left right : NodeId .real) : Prim .real
  | sq (input : NodeId .real) : Prim .real
  deriving DecidableEq

/-- A proof-facing SSA program.  Position `i` defines node `i`. -/
abbrev Program := List (Prim .real)

namespace Prim

/-- Check that every input of an instruction precedes its output. -/
def checkAt (index : Nat) : Prim .real → Bool
  | .var _ | .lit _ => true
  | .sub left right | .mul left right =>
      left.index < index && right.index < index
  | .sq input => input.index < index

end Prim

namespace Program

/-- Exact optional lookup; there is intentionally no default node. -/
def node? (program : Program) (node : NodeId .real) : Option (Prim .real) :=
  program[node.index]?

/-- Tail-recursive topology check with the current output index explicit. -/
def checkFrom : Nat → Program → Bool
  | _, [] => true
  | index, node :: tail => node.checkAt index && checkFrom (index + 1) tail

/-- Check SSA topology for the complete program. -/
def check (program : Program) : Bool := checkFrom 0 program

end Program

/-! ## Trusted structural budgets -/

/-- Trusted bounds on every untrusted certificate collection and on generated
expression depth. These are separate from endpoint arithmetic limits. -/
structure StructureLimit where
  maxNodes : Nat
  maxSources : Nat
  maxEdges : Nat
  maxFacts : Nat
  maxGeneration : Nat
  maxLookupSteps : Nat
  deriving DecidableEq, Repr

/-- Bounded length check that stops after `limit + 1` constructors. Unlike
computing `List.length`, this does not traverse the rest of an oversized
untrusted collection. -/
def lengthWithin {α : Type} : Nat → List α → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: tail => lengthWithin limit tail

/-! ## Centered instantiation and equality edge -/

/-- Node substitution and generated outputs for the `centerV1` recipe.
The last five nodes are admitted at exactly one generation beyond the four
base nodes. -/
structure Center where
  x : NodeId .real
  one : NodeId .real
  gap : NodeId .real
  prod : NodeId .real
  half : NodeId .real
  shift : NodeId .real
  square : NodeId .real
  quarter : NodeId .real
  form : NodeId .real
  baseSize : Nat
  generation : Nat
  deriving DecidableEq

namespace Center

/-- The four trigger nodes must belong to the immutable generation-zero
prefix, while every proposed node must lie in the extension. -/
def boundary (center : Center) : Bool :=
  center.x.index < center.baseSize && center.one.index < center.baseSize &&
    center.gap.index < center.baseSize && center.prod.index < center.baseSize &&
    center.baseSize ≤ center.half.index && center.baseSize ≤ center.shift.index &&
    center.baseSize ≤ center.square.index && center.baseSize ≤ center.quarter.index &&
    center.baseSize ≤ center.form.index

/-- Recompute the proposal generation from its checked base/extension
boundary. This prototype has one instantiation layer. -/
def inferredGeneration (center : Center) : Nat :=
  if center.boundary then 1 else 0

/-- Check the complete source and generated shape of `centerV1`. -/
def check (program : Program) (center : Center) : Bool :=
  program.node? center.x == some (.var 0) &&
    program.node? center.one == some (.lit (1 : Dyadic)) &&
    program.node? center.gap == some (.sub center.one center.x) &&
    program.node? center.prod == some (.mul center.x center.gap) &&
    program.node? center.half == some (.lit (Dyadic.ofIntWithPrec 1 1)) &&
    program.node? center.shift == some (.sub center.x center.half) &&
    program.node? center.square == some (.sq center.shift) &&
    program.node? center.quarter == some (.lit (Dyadic.ofIntWithPrec 1 2)) &&
    program.node? center.form == some (.sub center.quarter center.square) &&
    center.boundary && center.generation == center.inferredGeneration

end Center

/-- Versioned recipes understood by the fixed equality checker. -/
inductive EqRecipe where
  | centerV1 (center : Center)
  deriving DecidableEq

/-- An untrusted equality edge between two expression nodes. -/
structure EqEdge where
  left : NodeId .real
  right : NodeId .real
  recipe : EqRecipe
  deriving DecidableEq

namespace EqEdge

/-- The unique equality edge described by one `centerV1` witness. -/
def ofCenter (center : Center) : EqEdge :=
  ⟨center.prod, center.form, .centerV1 center⟩

/-- Check an equality recipe and its claimed endpoints against the same
trusted base boundary and generation cap as the selected certificate recipe. -/
def check (program : Program) (expectedBaseSize maxGeneration : Nat)
    (edge : EqEdge) : Bool :=
  match edge.recipe with
  | .centerV1 center =>
      center.baseSize == expectedBaseSize && center.generation ≤ maxGeneration &&
        center.check program && edge.left == center.prod && edge.right == center.form

/-- Check that the equality table contains the exact edge belonging to the
certificate's selected centered witness. -/
def containsCenter (edges : List EqEdge) (center : Center) : Bool :=
  edges.any fun edge => edge == ofCenter center

end EqEdge

/-! ## Finite-closed interval rows -/

/-- Construct an exact finite interval with both endpoints closed. -/
def closed (lower upper : Dyadic) : Raw :=
  .bounds (.finite lower false) (.finite upper false)

/-- Recover preflighted endpoints of a consistent finite-closed interval.
Every certificate range crosses `Raw.normalizeWithin` before its endpoint
ordering is inspected. Reversed, empty, open, unbounded, and over-budget
ranges are all rejected. -/
def closed? (limit : EndpointLimit) (raw : Raw) : Option (Dyadic × Dyadic) :=
  match raw.normalizeWithin limit with
  | .ready (.bounds (.finite lower false) (.finite upper false)) _ =>
      some (lower, upper)
  | _ => none

/-! The helpers below are the resource boundary for exact endpoint work.
They inspect only canonical constructor sizes before invoking dyadic
arithmetic or order. -/

/-- Check that several independently cheap size contributions fit in one
endpoint-height budget, without first adding untrusted natural values. -/
def fitHeight (remaining : Nat) : List Nat → Bool
  | [] => true
  | cost :: costs =>
      if cost ≤ remaining then fitHeight (remaining - cost) costs else false

/-- Preflight one endpoint without performing arithmetic. -/
def endpointOk (limit : EndpointLimit) (value : Dyadic) : Bool :=
  (EndpointCost.ofDyadic value).allowed limit

namespace Program

/-- Preflight every literal endpoint before any recipe checker compares
program instructions containing dyadics. -/
def literalsOk (limit : EndpointLimit) : Program → Bool
  | [] => true
  | .lit value :: tail => endpointOk limit value && literalsOk limit tail
  | _ :: tail => literalsOk limit tail

end Program

/-- Preflight one exact comparison, including its alignment shift. -/
def compareOk (limit : EndpointLimit) (left right : Dyadic) : Bool :=
  (CompareCost.ofDyadic left right).allowed limit

/-- Compare only after endpoint and alignment preflight. -/
def le? (limit : EndpointLimit) (left right : Dyadic) : Option Bool :=
  if compareOk limit left right then some (left ≤ right) else none

/-- Allocation preflight for exact dyadic subtraction. If retained endpoint
height is bounded by `H` and alignment by `S`, the aligned temporary work is
bounded at `O(H + S)` (plus a constant carry); the computed endpoint is then
separately required to return to retained height `H`. This preserves useful
cancellation without allowing an unbounded alignment allocation. -/
def subOk (limit : EndpointLimit) (left right : Dyadic) : Bool :=
  (CompareCost.ofDyadic left right).allowed limit

/-- Subtract only after a conservative alignment/allocation preflight, then
verify that the canonical output itself stays within the trusted limit. -/
def subDyadic? (limit : EndpointLimit) (left right : Dyadic) : Option Dyadic :=
  if subOk limit left right then
    let result := left - right
    if endpointOk limit result then some result else none
  else
    none

/-- Allocation and result-height preflight for exact multiplication. For two
nonzero canonical dyadics, the product mantissa needs at most the sum of the
input bit lengths and its exponent is the signed sum. Computing that signed
sum before multiplication preserves useful exponent cancellation. -/
def mulOk (limit : EndpointLimit) (left right : Dyadic) : Bool :=
  let leftCost := EndpointCost.ofDyadic left
  let rightCost := EndpointCost.ofDyadic right
  leftCost.allowed limit && rightCost.allowed limit &&
    match left, right with
    | .zero, _ | _, .zero => true
    | .ofOdd _ leftExponent _, .ofOdd _ rightExponent _ =>
        fitHeight limit.maxEndpointHeight
          [leftCost.numeratorBits, rightCost.numeratorBits,
            (leftExponent + rightExponent).natAbs]

/-- Multiply only after input/allocation preflight, then preflight the
canonical candidate before any min/max comparison can observe it. -/
def mulDyadic? (limit : EndpointLimit) (left right : Dyadic) : Option Dyadic :=
  if mulOk limit left right then
    let result := left * right
    if endpointOk limit result then some result else none
  else
    none

/-- One node and its claimed interval range. -/
structure Row where
  node : NodeId .real
  range : Raw
  deriving DecidableEq

/-- Build a row only when its exact closed range passes consistency and
resource preflight. -/
def checkedClosed? (limit : EndpointLimit) (node : NodeId .real)
    (lower upper : Dyadic) : Option Row := do
  let _ ← closed? limit (closed lower upper)
  pure ⟨node, closed lower upper⟩

namespace Row

/-- Validate an untrusted row without exposing unchecked endpoints. -/
def valid (limit : EndpointLimit) (row : Row) : Bool :=
  (closed? limit row.range).isSome

/-- Exact singleton range for a literal. -/
def lit (node : NodeId .real) (value : Dyadic) : Row :=
  ⟨node, closed value value⟩

/-- Resource-checked exact singleton range for a literal. -/
def lit? (limit : EndpointLimit) (node : NodeId .real) (value : Dyadic) : Option Row :=
  checkedClosed? limit node value value

/-- Finite-closed subtraction hull. Both operand alignment pairs are
preflighted before either subtraction is evaluated; both retained outputs are
then checked against endpoint height `H`. -/
def sub? (limit : EndpointLimit) (node : NodeId .real) (left right : Row) : Option Row := do
  let (leftLower, leftUpper) ← closed? limit left.range
  let (rightLower, rightUpper) ← closed? limit right.range
  if subOk limit leftLower rightUpper && subOk limit leftUpper rightLower then
    let lower := leftLower - rightUpper
    let upper := leftUpper - rightLower
    if endpointOk limit lower && endpointOk limit upper then
      checkedClosed? limit node lower upper
    else
      none
  else
    none

/-- Minimum of two dyadics, written without a `Min` instance so the
Mathlib-free core needs only decidable order. -/
def min2? (limit : EndpointLimit) (a b : Dyadic) : Option Dyadic := do
  let ordered ← le? limit a b
  pure (if ordered then a else b)

/-- Maximum of two dyadics, written without a `Max` instance. -/
def max2? (limit : EndpointLimit) (a b : Dyadic) : Option Dyadic := do
  let ordered ← le? limit a b
  pure (if ordered then b else a)

/-- Minimum of four values without an intermediate collection. -/
def min4? (limit : EndpointLimit) (a b c d : Dyadic) : Option Dyadic := do
  let ab ← min2? limit a b
  let cd ← min2? limit c d
  min2? limit ab cd

/-- Maximum of four values without an intermediate collection. -/
def max4? (limit : EndpointLimit) (a b c d : Dyadic) : Option Dyadic := do
  let ab ← max2? limit a b
  let cd ← max2? limit c d
  max2? limit ab cd

/-- Finite-closed four-corner multiplication hull. -/
def mul? (limit : EndpointLimit) (node : NodeId .real)
    (left right : Row) : Option Row := do
  let (leftLower, leftUpper) ← closed? limit left.range
  let (rightLower, rightUpper) ← closed? limit right.range
  let ll ← mulDyadic? limit leftLower rightLower
  let lu ← mulDyadic? limit leftLower rightUpper
  let ul ← mulDyadic? limit leftUpper rightLower
  let uu ← mulDyadic? limit leftUpper rightUpper
  let lower ← min4? limit ll lu ul uu
  let upper ← max4? limit ll lu ul uu
  checkedClosed? limit node lower upper

/-- Exact finite-closed square hull. Multiplication candidates are checked
before sign tests or extrema comparisons use them. -/
def sq? (limit : EndpointLimit) (node : NodeId .real) (input : Row) : Option Row := do
  let (lower, upper) ← closed? limit input.range
  let lowerSq ← mulDyadic? limit lower lower
  let upperSq ← mulDyadic? limit upper upper
  let upperNonpositive ← le? limit upper 0
  if upperNonpositive then
    checkedClosed? limit node upperSq lowerSq
  else
    let lowerNonnegative ← le? limit 0 lower
    if lowerNonnegative then
      checkedClosed? limit node lowerSq upperSq
    else
      let upperBound ← max2? limit lowerSq upperSq
      checkedClosed? limit node 0 upperBound

end Row

/-! ## Checked derivation -/

/-- Derivation instructions refer only to earlier fact rows. -/
inductive Derivation where
  | source (source : Nat)
  | lit
  | sub (left right : Nat)
  | mul (left right : Nat)
  | sq (input : Nat)
  | transport (edge input : Nat)
  deriving DecidableEq

/-- A claimed row paired with its derivation. -/
structure Fact where
  row : Row
  derivation : Derivation
  deriving DecidableEq

namespace Fact

/-- Cost, in list constructors visited, of finding an original-order fact
index in a newest-first accumulator. Invalid forward references have no cost
because they are rejected before lookup. -/
def reverseDistance? (priorCount index : Nat) : Option Nat :=
  if index < priorCount then some (priorCount - index) else none

/-- Cost, in list constructors visited, of a conventional forward lookup. -/
def forwardDistance? (count index : Nat) : Option Nat :=
  if index < count then some (index + 1) else none

/-- Lookup preserving the certificate's original fact numbering while facts
are accumulated in reverse order. -/
def prior? (priorCount : Nat) (priorRev : List Row) (index : Nat) : Option Row :=
  if index < priorCount then priorRev[priorCount - (index + 1)]? else none

/-- Total list lookup work requested by one derivation, including the program,
source, edge, and prior-fact tables. -/
def lookupCost? (programCount sourceCount edgeCount priorCount : Nat)
    (fact : Fact) : Option Nat :=
  match fact.derivation with
  | .source source => forwardDistance? sourceCount source
  | .lit => forwardDistance? programCount fact.row.node.index
  | .sub left right | .mul left right => do
      let programCost ← forwardDistance? programCount fact.row.node.index
      let leftCost ← reverseDistance? priorCount left
      let rightCost ← reverseDistance? priorCount right
      pure (programCost + leftCost + rightCost)
  | .sq input => do
      let programCost ← forwardDistance? programCount fact.row.node.index
      let inputCost ← reverseDistance? priorCount input
      pure (programCost + inputCost)
  | .transport edge input => do
      let edgeCost ← forwardDistance? edgeCount edge
      let inputCost ← reverseDistance? priorCount input
      pure (edgeCost + inputCost)

/-- Check one fact against the program, source table, equality table, and the
already accepted newest-first rows. -/
def check (limit : EndpointLimit) (program : Program) (sources : List Row)
    (edges : List EqEdge) (priorCount : Nat) (priorRev : List Row) (fact : Fact) : Bool :=
  fact.row.valid limit &&
    match fact.derivation with
    | .source source =>
        sources[source]? == some fact.row
    | .lit =>
        match program.node? fact.row.node with
        | some (.lit value) => Row.lit? limit fact.row.node value == some fact.row
        | _ => false
    | .sub left right =>
        match program.node? fact.row.node, prior? priorCount priorRev left,
            prior? priorCount priorRev right with
        | some (.sub leftNode rightNode), some leftRow, some rightRow =>
            leftRow.node == leftNode && rightRow.node == rightNode &&
              Row.sub? limit fact.row.node leftRow rightRow == some fact.row
        | _, _, _ => false
    | .mul left right =>
        match program.node? fact.row.node, prior? priorCount priorRev left,
            prior? priorCount priorRev right with
        | some (.mul leftNode rightNode), some leftRow, some rightRow =>
            leftRow.node == leftNode && rightRow.node == rightNode &&
              Row.mul? limit fact.row.node leftRow rightRow == some fact.row
        | _, _, _ => false
    | .sq input =>
        match program.node? fact.row.node, prior? priorCount priorRev input with
        | some (.sq inputNode), some inputRow =>
            inputRow.node == inputNode &&
              Row.sq? limit fact.row.node inputRow == some fact.row
        | _, _ => false
    | .transport edge input =>
        match edges[edge]?, prior? priorCount priorRev input with
        | some equality, some inputRow =>
            inputRow.range == fact.row.range &&
              ((inputRow.node == equality.left && fact.row.node == equality.right) ||
                (inputRow.node == equality.right && fact.row.node == equality.left))
        | _, _ => false

end Fact

/-- Check a fact list with constant-time cons accumulation. Certificate fact
indices retain their original order through `Fact.prior?`. Reverse-list
lookup is not asymptotically ideal; this D2 probe explicitly charges the list
constructors visited by each indexed program, source, edge, prior-fact, and
final-result lookup against `maxLookupSteps`. Sequential validation scans are
bounded separately by the structural caps. Production storage and unified
work accounting remain empirical choices. -/
def checkFacts (limit : EndpointLimit) (program : Program) (sources : List Row)
    (edges : List EqEdge)
    (programCount sourceCount edgeCount : Nat) :
    Nat → Nat → List Fact → List Row → Bool
  | _, _, [], _ => true
  | priorCount, remainingSteps, fact :: tail, priorRev =>
      match Fact.lookupCost? programCount sourceCount edgeCount priorCount fact with
      | none => false
      | some cost =>
          if cost ≤ remainingSteps then
            fact.check limit program sources edges priorCount priorRev &&
              checkFacts limit program sources edges programCount sourceCount edgeCount
                (priorCount + 1)
                (remainingSteps - cost) tail (fact.row :: priorRev)
          else
            false

/-- Complete untrusted certificate for the centered-product vertical. -/
structure Certificate where
  program : Program
  center : Center
  edges : List EqEdge
  facts : List Fact
  result : Nat
  deriving DecidableEq

namespace Certificate

/-- Cheap bounded structural preflight. It runs before topology, endpoint,
recipe, or fact-table traversal and stops after the trusted collection caps. -/
def structureOk (certificate : Certificate) (limit : StructureLimit)
    (expectedBaseSize : Nat) (expectedSources : List Row) : Bool :=
  certificate.center.generation ≤ limit.maxGeneration &&
    expectedBaseSize ≤ limit.maxNodes &&
    certificate.result < limit.maxFacts &&
    lengthWithin limit.maxNodes certificate.program &&
    lengthWithin limit.maxSources expectedSources &&
    lengthWithin limit.maxEdges certificate.edges &&
    lengthWithin limit.maxFacts certificate.facts

/-- Check topology, the selected one-generation instantiation, its exact
equality edge, every propagation row, and the caller-bound result under
trusted structural and endpoint limits. Sources, base size, and target are
separate trusted inputs; the untrusted certificate cannot substitute them. -/
def check (certificate : Certificate) (endpointLimit : EndpointLimit)
    (structureLimit : StructureLimit) (expectedBaseSize : Nat)
    (expectedSources : List Row) (expectedTarget : Row) : Bool :=
  certificate.structureOk structureLimit expectedBaseSize expectedSources &&
    certificate.program.literalsOk endpointLimit &&
    certificate.program.check &&
    certificate.center.baseSize == expectedBaseSize &&
    certificate.center.check certificate.program &&
    (expectedSources.all fun source =>
      source.valid endpointLimit && (certificate.program.node? source.node).isSome) &&
    expectedTarget.valid endpointLimit &&
    (certificate.program.node? expectedTarget.node).isSome &&
    EqEdge.containsCenter certificate.edges certificate.center &&
    certificate.edges.all
      (EqEdge.check certificate.program expectedBaseSize structureLimit.maxGeneration) &&
    match Fact.forwardDistance? certificate.facts.length certificate.result with
    | none => false
    | some resultCost =>
        if resultCost ≤ structureLimit.maxLookupSteps then
          checkFacts endpointLimit certificate.program expectedSources certificate.edges
              certificate.program.length expectedSources.length certificate.edges.length 0
              (structureLimit.maxLookupSteps - resultCost) certificate.facts [] &&
            certificate.facts[certificate.result]?.map (fun fact => fact.row) ==
              some expectedTarget
        else
          false

end Certificate

/-! ## Fixed nine-node fixture -/

def node (index : Nat) : NodeId .real := ⟨index⟩

/-- The four-node source program for `x * (1 - x)`. -/
def baseProgram : Program :=
  [.var 0, .lit 1, .sub (node 1) (node 0), .mul (node 0) (node 2)]

/-- The source program plus the five nodes introduced by `centerV1`. -/
def extendedProgram : Program :=
  baseProgram ++
    [.lit (Dyadic.ofIntWithPrec 1 1), .sub (node 0) (node 4), .sq (node 5),
      .lit (Dyadic.ofIntWithPrec 1 2), .sub (node 7) (node 6)]

/-- The unique substitution used by the fixed centered instantiation. -/
def centerWitness : Center :=
  { x := node 0
    one := node 1
    gap := node 2
    prod := node 3
    half := node 4
    shift := node 5
    square := node 6
    quarter := node 7
    form := node 8
    baseSize := baseProgram.length
    generation := 1 }

/-- Checked edge `x * (1 - x) = 1/4 - (x - 1/2)^2`. -/
def centerEdge : EqEdge :=
  EqEdge.ofCenter centerWitness

def unitRange : Raw := closed 0 1
def half : Dyadic := Dyadic.ofIntWithPrec 1 1
def quarter : Dyadic := Dyadic.ofIntWithPrec 1 2
def centeredRange : Raw := closed (-half) half
def quarterRange : Raw := closed 0 quarter

/-- The explicit ten-row trace.  Row 8 bounds the generated centered form;
row 9 transports that same range back across `centerEdge` to the original
product node. -/
def fixtureFacts : List Fact :=
  [ ⟨⟨node 0, unitRange⟩, .source 0⟩
  , ⟨Row.lit (node 1) 1, .lit⟩
  , ⟨⟨node 2, unitRange⟩, .sub 1 0⟩
  , ⟨⟨node 3, unitRange⟩, .mul 0 2⟩
  , ⟨Row.lit (node 4) half, .lit⟩
  , ⟨⟨node 5, centeredRange⟩, .sub 0 4⟩
  , ⟨⟨node 6, quarterRange⟩, .sq 5⟩
  , ⟨Row.lit (node 7) quarter, .lit⟩
  , ⟨⟨node 8, quarterRange⟩, .sub 7 6⟩
  , ⟨⟨node 3, quarterRange⟩, .transport 0 8⟩ ]

/-- The complete fixed certificate used by replay and semantic experiments. -/
def fixtureCert : Certificate :=
  { program := extendedProgram
    center := centerWitness
    edges := [centerEdge]
    facts := fixtureFacts
    result := 9 }

/-- Caller-bound source facts for the fixed fixture. -/
def fixtureSources : List Row := [⟨node 0, unitRange⟩]

/-- Caller-bound result expected from the fixed fixture. -/
def fixtureTarget : Row := ⟨node 3, quarterRange⟩

/-- Trusted endpoint budget for the fixed centered-product replay. -/
def fixtureLimit : EndpointLimit :=
  { maxEndpointHeight := 16
    maxAlignmentShift := 8 }

/-- Trusted structural and lookup-work budget for the fixed fixture. -/
def fixtureStructureLimit : StructureLimit :=
  { maxNodes := 9
    maxSources := 1
    maxEdges := 1
    maxFacts := 10
    maxGeneration := 1
    maxLookupSteps := 74 }

/-- Kernel-reducible checker proposition measured by the D2 replay probes. -/
def checkFixture : Bool :=
  fixtureCert.check fixtureLimit fixtureStructureLimit baseProgram.length
    fixtureSources fixtureTarget

/-- The committed fixture passes the same ordinary-kernel checker exposed to
downstream replay probes. -/
theorem checkFixture_eq_true : checkFixture = true := by
  decide +kernel

/-! ## Resource and shape canaries -/

/-- Representative non-finite, non-closed, inconsistent, and over-budget
claims are all rejected at the range boundary. -/
def rejectsBadRows : Bool :=
  [ Raw.empty
  , closed 1 0
  , .bounds (.finite 0 true) (.finite 1 false)
  , .bounds .unbounded (.finite 1 false)
  , .bounds (.finite 0 false) .unbounded
  , closed (Dyadic.ofIntWithPrec 1 64) (Dyadic.ofIntWithPrec 1 64)
  ].all fun range => (closed? fixtureLimit range).isNone

theorem rejectsBadRows_eq_true : rejectsBadRows = true := by
  decide +kernel

/-- Operation preflight preserves cancellation: it bounds temporary work from
the trusted input/shift limits without charging the endpoint budget twice. -/
def checksCancellationBudget : Bool :=
  let tiny := Dyadic.ofIntWithPrec 1 15
  subDyadic? fixtureLimit tiny tiny == some 0 &&
    mulDyadic? fixtureLimit (Dyadic.ofIntWithPrec 1 8) (256 : Dyadic) == some 1

theorem checksCancellationBudget_eq_true : checksCancellationBudget = true := by
  decide +kernel

/-- Arithmetic work is rejected before an excessive alignment shift or a
product whose predicted canonical height exceeds the trusted budget. -/
def rejectsOperationOverrun : Bool :=
  let alignmentLimit : EndpointLimit :=
    { maxEndpointHeight := 1000000100, maxAlignmentShift := 8 }
  let far : Dyadic := .ofOdd 1 1000000000 (by decide)
  (subDyadic? alignmentLimit far 1).isNone &&
    (mulDyadic? fixtureLimit (32768 : Dyadic) (32768 : Dyadic)).isNone

theorem rejectsOperationOverrun_eq_true : rejectsOperationOverrun = true := by
  decide +kernel

/-- The square evaluator is exact away from zero as well as on the centered
fixture's zero-spanning range. -/
def checksSquareCases : Bool :=
  Row.sq? fixtureLimit (node 0) ⟨node 0, closed 1 2⟩ ==
      some ⟨node 0, closed 1 4⟩ &&
    Row.sq? fixtureLimit (node 0) ⟨node 0, closed (-2) (-1)⟩ ==
      some ⟨node 0, closed 1 4⟩ &&
    Row.sq? fixtureLimit (node 0) ⟨node 0, centeredRange⟩ ==
      some ⟨node 0, quarterRange⟩

theorem checksSquareCases_eq_true : checksSquareCases = true := by
  decide +kernel

end Hex.Interval.Experiment.Center
