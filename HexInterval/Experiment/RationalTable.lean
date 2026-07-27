/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Scale

@[expose] public section

/-!
# Endpoint-erased traces and canonical rational tables

This module starts the Mathlib-free rational endpoint vertical without adding
rational arithmetic to the planner or fixing a wire format.  It has two
separate responsibilities:

* erase every numeric endpoint from a centered certificate while retaining its
  operation and literal slots, cut shapes, derivation references, equality
  recipe, caller-owned boundary, and structural budget;
* validate a complete table of raw integer/natural rational encodings before
  a later arithmetic replay may inspect them.

The table is untrusted.  Its caller owns all limits, every entry is checked
even when no retained fact references it, and a rejected entry is never
silently normalized.  Compiled Core `Rat` planning and arithmetic-edge replay
are later phases and deliberately do not occur in this module.
-/

namespace Hex.Interval.Experiment.RationalTable

open Center Scale

/-! ## Endpoint-erased centered skeleton -/

namespace Shape

/-- Endpoint-free operation at one SSA position.  A literal retains only its
first-occurrence sharing slot, not its numeric value. -/
inductive Op where
  | var (source : Nat)
  | lit (slot : Nat)
  | sub (left right : NodeId .real)
  | mul (left right : NodeId .real)
  | sq (input : NodeId .real)
  deriving DecidableEq, Repr

/-- Shape of a lower cut after erasing its finite endpoint. -/
inductive Lower where
  | unbounded
  | finite (strict : Bool)
  deriving DecidableEq, Repr

/-- Shape of an upper cut after erasing its finite endpoint. -/
inductive Upper where
  | finite (strict : Bool)
  | unbounded
  deriving DecidableEq, Repr

/-- Empty/bounded and open/closed structure of a range, without endpoints. -/
inductive Range where
  | empty
  | bounds (lower : Lower) (upper : Upper)
  deriving DecidableEq, Repr

/-- Endpoint-free row shape. -/
structure Row where
  node : NodeId .real
  range : Range
  deriving DecidableEq, Repr

/-- Endpoint-free fact shape.  The derivation already contains only structural
references, so it is retained exactly. -/
structure Fact where
  row : Row
  derivation : Center.Derivation
  deriving DecidableEq

/-- Complete structural boundary for one centered checker invocation.  Sources,
target, base size, and limits are caller-owned even though the untrusted
certificate supplies the other fields. -/
structure Skeleton where
  program : List Op
  center : Center.Center
  edges : List Center.EqEdge
  facts : List Fact
  result : Nat
  baseSize : Nat
  sources : List Row
  target : Row
  limit : Center.StructureLimit
  deriving DecidableEq

end Shape

/-- First zero-based occurrence of a value in a list.  Keeping this helper
transparent lets both endpoint backends use the same literal-sharing rule. -/
def firstIndex? {α : Type} [DecidableEq α] (value : α) :
    Nat → List α → Option Nat
  | _, [] => none
  | index, head :: tail =>
      if value = head then some index else firstIndex? value (index + 1) tail

/-- Erase a complete dyadic program while retaining the equality pattern of
its literals.  The first distinct literal receives slot zero, the next unseen
literal slot one, and later equal literals reuse the earlier slot. -/
def eraseProgramFrom (seen : List Dyadic) : Center.Program → List Shape.Op
  | [] => []
  | .var source :: tail => .var source :: eraseProgramFrom seen tail
  | .lit value :: tail =>
      match firstIndex? value 0 seen with
      | some slot => .lit slot :: eraseProgramFrom seen tail
      | none => .lit seen.length :: eraseProgramFrom (seen ++ [value]) tail
  | .sub left right :: tail => .sub left right :: eraseProgramFrom seen tail
  | .mul left right :: tail => .mul left right :: eraseProgramFrom seen tail
  | .sq input :: tail => .sq input :: eraseProgramFrom seen tail

/-- Endpoint-erased program projection. -/
def eraseProgram (program : Center.Program) : List Shape.Op :=
  eraseProgramFrom [] program

/-- Erase a lower cut's numeric endpoint. -/
def eraseLower : Hex.Interval.Lower → Shape.Lower
  | .unbounded => .unbounded
  | .finite _ strict => .finite strict

/-- Erase an upper cut's numeric endpoint. -/
def eraseUpper : Hex.Interval.Upper → Shape.Upper
  | .finite _ strict => .finite strict
  | .unbounded => .unbounded

/-- Erase numeric endpoints while retaining empty, bounded, and closure shape. -/
def eraseRange : Hex.Interval.Raw → Shape.Range
  | .empty => .empty
  | .bounds lower upper => .bounds (eraseLower lower) (eraseUpper upper)

/-- Erase one interval row. -/
def eraseRow (row : Center.Row) : Shape.Row :=
  ⟨row.node, eraseRange row.range⟩

/-- Erase one fact without changing its derivation references. -/
def eraseFact (fact : Center.Fact) : Shape.Fact :=
  ⟨eraseRow fact.row, fact.derivation⟩

/-- Project a centered certificate together with its caller-owned invocation
boundary to an endpoint-free skeleton. -/
def eraseCertificate (certificate : Center.Certificate) (baseSize : Nat)
    (sources : List Center.Row) (target : Center.Row)
    (limit : Center.StructureLimit) : Shape.Skeleton :=
  { program := eraseProgram certificate.program
    center := certificate.center
    edges := certificate.edges
    facts := certificate.facts.map eraseFact
    result := certificate.result
    baseSize
    sources := sources.map eraseRow
    target := eraseRow target
    limit }

/-- Project one generated scaling workload using the same fixed caller-owned
source and target as the centered fixture. -/
def eraseWorkload (workload : Scale.Workload) : Shape.Skeleton :=
  eraseCertificate workload.certificate Center.baseProgram.length
    Center.fixtureSources Center.fixtureTarget
    (workload.limitAt workload.lookupSteps)

/-- Endpoint-free skeleton of the fixed centered certificate. -/
def fixtureSkeleton : Shape.Skeleton :=
  eraseCertificate Center.fixtureCert Center.baseProgram.length
    Center.fixtureSources Center.fixtureTarget Center.fixtureStructureLimit

/-- Explicit expected operation sequence for the nine-node centered program. -/
def fixtureOps : List Shape.Op :=
  [ .var 0
  , .lit 0
  , .sub (Center.node 1) (Center.node 0)
  , .mul (Center.node 0) (Center.node 2)
  , .lit 1
  , .sub (Center.node 0) (Center.node 4)
  , .sq (Center.node 5)
  , .lit 2
  , .sub (Center.node 7) (Center.node 6) ]

/-- Closed finite range shape shared by every fixed fixture row. -/
def closedShape : Shape.Range :=
  .bounds (.finite false) (.finite false)

/-- Explicit expected endpoint-free fact sequence for the fixed trace. -/
def fixtureShapes : List Shape.Fact :=
  [ ⟨⟨Center.node 0, closedShape⟩, .source 0⟩
  , ⟨⟨Center.node 1, closedShape⟩, .lit⟩
  , ⟨⟨Center.node 2, closedShape⟩, .sub 1 0⟩
  , ⟨⟨Center.node 3, closedShape⟩, .mul 0 2⟩
  , ⟨⟨Center.node 4, closedShape⟩, .lit⟩
  , ⟨⟨Center.node 5, closedShape⟩, .sub 0 4⟩
  , ⟨⟨Center.node 6, closedShape⟩, .sq 5⟩
  , ⟨⟨Center.node 7, closedShape⟩, .lit⟩
  , ⟨⟨Center.node 8, closedShape⟩, .sub 7 6⟩
  , ⟨⟨Center.node 3, closedShape⟩, .transport 0 8⟩ ]

/-- Independently written expected skeleton for the centered fixture. -/
def expectedSkeleton : Shape.Skeleton :=
  { program := fixtureOps
    center := Center.centerWitness
    edges := [Center.centerEdge]
    facts := fixtureShapes
    result := 9
    baseSize := 4
    sources := [⟨Center.node 0, closedShape⟩]
    target := ⟨Center.node 3, closedShape⟩
    limit := Center.fixtureStructureLimit }

/-- Change every numeric program literal and row endpoint while retaining the
same structural slots and cut shapes.  This is intentionally not a valid
arithmetic certificate; it tests only the erasure boundary. -/
def endpointChanged : Center.Certificate :=
  { Center.fixtureCert with
    program :=
      [ .var 0, .lit 7, .sub (Center.node 1) (Center.node 0),
        .mul (Center.node 0) (Center.node 2), .lit (-3),
        .sub (Center.node 0) (Center.node 4), .sq (Center.node 5), .lit 11,
        .sub (Center.node 7) (Center.node 6) ]
    facts := Center.fixtureFacts.map fun fact =>
      { fact with row := { fact.row with range := Center.closed (-5) 13 } } }

/-- Sources corresponding only in shape to `endpointChanged`. -/
def endpointChangedSources : List Center.Row :=
  [⟨Center.node 0, Center.closed (-5) 13⟩]

/-- Target corresponding only in shape to `endpointChanged`. -/
def endpointChangedTarget : Center.Row :=
  ⟨Center.node 3, Center.closed (-5) 13⟩

/-- Reusing one literal in every literal position changes the sharing pattern
even though it leaves the operation constructors in the same positions. -/
def literalSharingChanged : Center.Certificate :=
  { Center.fixtureCert with
    program :=
      [ .var 0, .lit 1, .sub (Center.node 1) (Center.node 0),
        .mul (Center.node 0) (Center.node 2), .lit 1,
        .sub (Center.node 0) (Center.node 4), .sq (Center.node 5), .lit 1,
        .sub (Center.node 7) (Center.node 6) ] }

/-- The projection agrees with an independent literal/fact skeleton, every
base scaling family has that exact skeleton, and changing only endpoints does
not change it. -/
def checksErasure : Bool :=
  fixtureSkeleton == expectedSkeleton &&
    (Scale.deadNodes? 9).map eraseWorkload == some expectedSkeleton &&
    (Scale.adjacent? 1).map eraseWorkload == some expectedSkeleton &&
    (Scale.far? 1).map eraseWorkload == some expectedSkeleton &&
    eraseWorkload (Scale.sourcePad 0) == expectedSkeleton &&
    eraseCertificate endpointChanged Center.baseProgram.length
      endpointChangedSources endpointChangedTarget Center.fixtureStructureLimit ==
        expectedSkeleton &&
    eraseCertificate literalSharingChanged Center.baseProgram.length
      Center.fixtureSources Center.fixtureTarget Center.fixtureStructureLimit !=
        expectedSkeleton &&
    eraseCertificate { Center.fixtureCert with result := 8 }
      Center.baseProgram.length Center.fixtureSources Center.fixtureTarget
      Center.fixtureStructureLimit != expectedSkeleton

/-- Ordinary-kernel canary for the endpoint erasure boundary. -/
theorem checksErasure_eq_true : checksErasure = true := by
  decide +kernel

/-! ## Canonical raw rational table -/

/-- Untrusted raw rational endpoint.  A natural nonzero denominator is
positive; table validation additionally requires reduced form. -/
structure RawRat where
  num : Int
  den : Nat
  deriving DecidableEq, Repr

namespace RawRat

/-- Mathematical value of a raw endpoint.  This total interpretation is used
only after validation; malformed zero denominators are rejected beforehand. -/
def value (q : RawRat) : Rat :=
  mkRat q.num q.den

/-- Allocation-independent retained size of one raw endpoint. -/
structure Cost where
  numeratorBits : Nat
  denominatorBits : Nat
  deriving DecidableEq, Repr

/-- Caller-owned limits for the first raw-table boundary.  GCD input size and
aggregate GCD work are independent of retained endpoint size.  Arithmetic
temporary work and wire bytes belong to later phases and are not guessed here. -/
structure Limit where
  maxEntries : Nat
  maxNumeratorBits : Nat
  maxDenominatorBits : Nat
  maxGcdInputBits : Nat
  maxGcdWork : Nat
  deriving DecidableEq, Repr

/-- Semantic canonicality required of an admitted raw endpoint. -/
def Canonical (q : RawRat) : Prop :=
  q.den ≠ 0 ∧ q.num.natAbs.Coprime q.den

/-- Inspect numerator and denominator bit lengths without multiplying them. -/
def cost (q : RawRat) : Cost :=
  { numeratorBits := EndpointCost.natBits q.num.natAbs
    denominatorBits := EndpointCost.natBits q.den }

/-- Largest bit width presented to the canonicality GCD. -/
def Cost.gcdInputBits (size : Cost) : Nat :=
  max size.numeratorBits size.denominatorBits

/-- Conservative nonzero work charged for one canonicality GCD.  Giving zero
a one-unit cost ensures that every `Nat.gcd` invocation consumes budget. -/
def Cost.gcdWork (size : Cost) : Nat :=
  max 1 size.numeratorBits * max 1 size.denominatorBits

/-- Logical malformed-entry reasons. -/
inductive Invalid where
  | zeroDenominator
  | notReduced
  deriving DecidableEq, Repr

/-- Resource failures known before canonicality or arithmetic work. -/
inductive Resource where
  | entries
  | numeratorBits
  | denominatorBits
  | gcdInputBits
  | gcdWork
  deriving DecidableEq, Repr

/-- Result of validating one entry. -/
inductive EntryResult where
  | ready
  | malformed (reason : Invalid)
  | resourceLimit (reason : Resource)
  deriving DecidableEq, Repr

/-- Validate retained size and GCD resources before positivity and reduced
form.  `remainingGcdWork` is owned and threaded by the whole-table checker. -/
def check (limit : Limit) (remainingGcdWork : Nat) (q : RawRat) : EntryResult :=
  let size := q.cost
  if size.numeratorBits > limit.maxNumeratorBits then
    .resourceLimit .numeratorBits
  else if size.denominatorBits > limit.maxDenominatorBits then
    .resourceLimit .denominatorBits
  else if size.gcdInputBits > limit.maxGcdInputBits then
    .resourceLimit .gcdInputBits
  else if size.gcdWork > remainingGcdWork then
    .resourceLimit .gcdWork
  else if q.den = 0 then
    .malformed .zeroDenominator
  else if q.num.natAbs.gcd q.den = 1 then
    .ready
  else
    .malformed .notReduced

/-- A ready entry has a positive, coprime denominator. -/
theorem canonical_of_check {limit : Limit} {remainingGcdWork : Nat} {q : RawRat}
    (h : q.check limit remainingGcdWork = .ready) : q.Canonical := by
  unfold check at h
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hden
  split at h <;> try contradiction
  rename_i hcop
  exact ⟨hden, hcop⟩

/-- A ready raw endpoint interprets to the same canonical numerator and
denominator that were checked. -/
theorem value_fields {limit : Limit} {remainingGcdWork : Nat} {q : RawRat}
    (h : q.check limit remainingGcdWork = .ready) :
    q.value.num = q.num ∧ q.value.den = q.den := by
  have hc := canonical_of_check h
  have hvalue : q.value = Rat.mk' q.num q.den hc.1 hc.2 := by
    exact (Rat.mk_eq_mkRat q.num q.den hc.1 hc.2).symm
  rw [hvalue]
  exact ⟨rfl, rfl⟩

end RawRat

namespace Table

/-- Complete table-validation result with the first failing entry index.  A
collection cap has no entry index because validation stops before traversal. -/
inductive Result where
  | ready
  | malformed (index : Nat) (reason : RawRat.Invalid)
  | resourceLimit (index : Option Nat) (reason : RawRat.Resource)
  deriving DecidableEq, Repr

/-- Validate every entry in order after bounded collection preflight, consuming
the caller-owned aggregate GCD budget only after each successful entry. -/
def checkFrom (limit : RawRat.Limit) : Nat → Nat → List RawRat → Result
  | _, _, [] => .ready
  | index, remainingGcdWork, entry :: tail =>
      match entry.check limit remainingGcdWork with
      | .ready =>
          checkFrom limit (index + 1) (remainingGcdWork - entry.cost.gcdWork) tail
      | .malformed reason => .malformed index reason
      | .resourceLimit reason => .resourceLimit (some index) reason

/-- Validate an untrusted table under caller-owned entry and endpoint limits.
The bounded length check precedes the whole-table scan. -/
def check (limit : RawRat.Limit) (entries : List RawRat) : Result :=
  if lengthWithin limit.maxEntries entries then
    checkFrom limit 0 limit.maxGcdWork entries
  else
    .resourceLimit none .entries

/-- A ready suffix scan contains only canonical raw endpoints. -/
theorem canonical_of_checkFrom {limit : RawRat.Limit} {entries : List RawRat}
    {index remainingGcdWork : Nat}
    (h : checkFrom limit index remainingGcdWork entries = .ready) :
    ∀ q ∈ entries, q.Canonical := by
  induction entries generalizing index remainingGcdWork with
  | nil => simp
  | cons head tail ih =>
      simp only [checkFrom] at h
      cases hhead : head.check limit remainingGcdWork with
      | ready =>
          simp only [hhead] at h
          intro q hq
          simp only [List.mem_cons] at hq
          cases hq with
          | inl hsame =>
              subst q
              exact RawRat.canonical_of_check hhead
          | inr htail =>
              exact ih h q htail
      | malformed reason => simp [hhead] at h
      | resourceLimit reason => simp [hhead] at h

/-- A ready table contains only canonical raw endpoints. -/
theorem canonical_of_check {limit : RawRat.Limit} {entries : List RawRat}
    (h : check limit entries = .ready) : ∀ q ∈ entries, q.Canonical := by
  unfold check at h
  split at h
  next _ => exact canonical_of_checkFrom h
  next _ => contradiction

end Table

/-! ## Fixed rational-table canaries -/

/-- Caller-owned limits for small canonical-table canaries. -/
def fixtureTableLimit : RawRat.Limit :=
  { maxEntries := 5
    maxNumeratorBits := 8
    maxDenominatorBits := 8
    maxGcdInputBits := 8
    maxGcdWork := 64 }

/-- An accepted table including canonical zero, negative, and non-dyadic
values. -/
def fixtureTable : List RawRat :=
  [⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 3⟩, ⟨2, 9⟩]

/-- Whole-table acceptance and fail-closed malformed/resource behavior.  The
last cases put the failure in an otherwise unused final entry. -/
def checksTable : Bool :=
  Table.check fixtureTableLimit fixtureTable == .ready &&
    Table.check fixtureTableLimit [⟨0, 0⟩] ==
      .malformed 0 .zeroDenominator &&
    Table.check fixtureTableLimit [⟨0, 7⟩] ==
      .malformed 0 .notReduced &&
    Table.check fixtureTableLimit [⟨2, 6⟩] ==
      .malformed 0 .notReduced &&
    Table.check fixtureTableLimit (fixtureTable ++ [⟨0, 7⟩]) ==
      .malformed 4 .notReduced &&
    Table.check { fixtureTableLimit with maxEntries := 3 } fixtureTable ==
      .resourceLimit none .entries &&
    Table.check { fixtureTableLimit with maxNumeratorBits := 1 } [⟨4, 1⟩] ==
      .resourceLimit (some 0) .numeratorBits &&
    Table.check { fixtureTableLimit with maxNumeratorBits := 8 }
      [⟨2, 6⟩, ⟨256, 1⟩] == .malformed 0 .notReduced &&
    Table.check { fixtureTableLimit with maxDenominatorBits := 8 }
      (fixtureTable ++ [⟨1, 256⟩]) ==
        .resourceLimit (some 4) .denominatorBits &&
    Table.check { fixtureTableLimit with maxGcdInputBits := 7 } [⟨1, 255⟩] ==
      .resourceLimit (some 0) .gcdInputBits &&
    Table.check { fixtureTableLimit with maxGcdWork := 5 }
      [⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩] == .ready &&
    Table.check { fixtureTableLimit with maxGcdWork := 4 }
      [⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩] ==
        .resourceLimit (some 2) .gcdWork

/-- Ordinary-kernel canary for canonical whole-table validation. -/
theorem checksTable_eq_true : checksTable = true := by
  decide +kernel

end Hex.Interval.Experiment.RationalTable
