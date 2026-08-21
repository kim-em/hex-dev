/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Source-pinned PNT+ negative exponential table

This bounded Mathlib-free package authenticates the 79 direct
`exp (-x)` upper-bound declarations in PNT+'s `IEANTN/LogTables.lean`.
Every source argument is represented in sixths, so one checked
`exp (-1/6)` enclosure supplies a uniform range-reduction certificate.
Real exponential semantics live in the Mathlib companion.
-/

namespace Hex.Interval.Experiment.PntExpNegative

open Propagator PayloadArena

structure Source where
  sourceIndex : Nat
  sixths : Nat
  deriving DecidableEq, Repr

structure Upper where
  sourceIndex : Nat
  numerator : Nat
  scale : Nat
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | exact (value : Source)
  | upper (value : Upper)
  | empty
  deriving DecidableEq, Repr

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

structure SourceRecord where
  sixths : Nat
  numerator : Nat
  scale : Nat
  deriving DecidableEq, Repr

/-- Exact source rows 244--322 at pinned PNT+ commit
`21998bb6196b56789f72a52656a781a75e134eb0`. -/
def sourceRecord? : Nat → Option SourceRecord
  | 0 => some ⟨60, 4541, 8⟩
  | 1 => some ⟨63, 2755, 8⟩
  | 2 => some ⟨66, 1672, 8⟩
  | 3 => some ⟨69, 1015, 8⟩
  | 4 => some ⟨72, 6146, 9⟩
  | 5 => some ⟨75, 3728, 9⟩
  | 6 => some ⟨78, 2262, 9⟩
  | 7 => some ⟨80, 1621, 9⟩
  | 8 => some ⟨81, 1372, 9⟩
  | 9 => some ⟨84, 8317, 10⟩
  | 10 => some ⟨87, 5045, 10⟩
  | 11 => some ⟨88, 4271, 10⟩
  | 12 => some ⟨90, 3061, 10⟩
  | 13 => some ⟨92, 2193, 10⟩
  | 14 => some ⟨93, 1857, 10⟩
  | 15 => some ⟨96, 1127, 10⟩
  | 16 => some ⟨99, 6827, 11⟩
  | 17 => some ⟨100, 5779, 11⟩
  | 18 => some ⟨102, 4141, 11⟩
  | 19 => some ⟨104, 2968, 11⟩
  | 20 => some ⟨105, 2512, 11⟩
  | 21 => some ⟨108, 1524, 11⟩
  | 22 => some ⟨111, 9239, 12⟩
  | 23 => some ⟨112, 7821, 12⟩
  | 24 => some ⟨114, 5604, 12⟩
  | 25 => some ⟨116, 4016, 12⟩
  | 26 => some ⟨117, 3400, 12⟩
  | 27 => some ⟨120, 2063, 12⟩
  | 28 => some ⟨123, 1252, 12⟩
  | 29 => some ⟨124, 1060, 12⟩
  | 30 => some ⟨126, 7584, 13⟩
  | 31 => some ⟨128, 5435, 13⟩
  | 32 => some ⟨129, 4601, 13⟩
  | 33 => some ⟨132, 2791, 13⟩
  | 34 => some ⟨135, 1693, 13⟩
  | 35 => some ⟨136, 1434, 13⟩
  | 36 => some ⟨138, 1028, 13⟩
  | 37 => some ⟨140, 7354, 14⟩
  | 38 => some ⟨141, 6226, 14⟩
  | 39 => some ⟨144, 3777, 14⟩
  | 40 => some ⟨147, 2291, 14⟩
  | 41 => some ⟨148, 1940, 14⟩
  | 42 => some ⟨150, 1390, 14⟩
  | 43 => some ⟨152, 9953, 15⟩
  | 44 => some ⟨153, 8425, 15⟩
  | 45 => some ⟨156, 5111, 15⟩
  | 46 => some ⟨159, 3100, 15⟩
  | 47 => some ⟨160, 2625, 15⟩
  | 48 => some ⟨162, 1881, 15⟩
  | 49 => some ⟨164, 1348, 15⟩
  | 50 => some ⟨165, 1141, 15⟩
  | 51 => some ⟨168, 6916, 16⟩
  | 52 => some ⟨171, 4195, 16⟩
  | 53 => some ⟨172, 3551, 16⟩
  | 54 => some ⟨174, 2545, 16⟩
  | 55 => some ⟨176, 1824, 16⟩
  | 56 => some ⟨177, 1544, 16⟩
  | 57 => some ⟨180, 9359, 17⟩
  | 58 => some ⟨184, 4806, 17⟩
  | 59 => some ⟨188, 2468, 17⟩
  | 60 => some ⟨192, 1268, 17⟩
  | 61 => some ⟨196, 6503, 18⟩
  | 62 => some ⟨200, 3340, 18⟩
  | 63 => some ⟨204, 1715, 18⟩
  | 64 => some ⟨208, 8801, 19⟩
  | 65 => some ⟨212, 4519, 19⟩
  | 66 => some ⟨216, 2321, 19⟩
  | 67 => some ⟨220, 1192, 19⟩
  | 68 => some ⟨224, 6116, 20⟩
  | 69 => some ⟨228, 3141, 20⟩
  | 70 => some ⟨232, 1613, 20⟩
  | 71 => some ⟨236, 8276, 21⟩
  | 72 => some ⟨240, 4250, 21⟩
  | 73 => some ⟨300, 1, 20⟩
  | 74 => some ⟨400, 1, 26⟩
  | 75 => some ⟨600, 1, 40⟩
  | 76 => some ⟨800, 1, 53⟩
  | 77 => some ⟨900, 1, 60⟩
  | 78 => some ⟨1200, 1, 80⟩
  | _ => none

structure Certificate where
  sourceIndex : Nat
  sixths : Nat
  baseNumerator : Nat
  baseScale : Nat
  terms : Nat
  numerator : Nat
  scale : Nat
  deriving DecidableEq, Repr

def baseNumerator : Nat := 846481724891
def baseScale : Nat := 12
def terms : Nat := 14

def certificateFor? (sourceIndex : Nat) : Option Certificate :=
  match sourceRecord? sourceIndex with
  | some source =>
      some
        { sourceIndex
          sixths := source.sixths
          baseNumerator
          baseScale
          terms
          numerator := source.numerator
          scale := source.scale }
  | none => none

def defaultCertificate : Certificate := ⟨0, 0, 0, 0, 0, 0, 0⟩

def certificates : List Certificate :=
  (List.range 79).map fun sourceIndex =>
    (certificateFor? sourceIndex).getD defaultCertificate

def Certificate.source (value : Certificate) : Source :=
  { sourceIndex := value.sourceIndex, sixths := value.sixths }

def Certificate.upper (value : Certificate) : Upper :=
  { sourceIndex := value.sourceIndex, numerator := value.numerator,
    scale := value.scale }

/-- Exact integer comparison corresponding to the outward power bound. -/
def Certificate.powerCheck (value : Certificate) : Bool :=
  decide
    (value.baseNumerator ^ value.sixths * 10 ^ value.scale <
      value.numerator * (10 ^ value.baseScale) ^ value.sixths)

def Certificate.valid (value : Certificate) : Bool :=
  certificateFor? value.sourceIndex == some value &&
    decide (0 < value.sixths) && value.powerCheck

def encode (value : Certificate) : List Nat :=
  [value.sourceIndex, value.sixths, value.baseNumerator, value.baseScale,
    value.terms, value.numerator, value.scale]

def decode? : List Nat → Option Certificate
  | [sourceIndex, sixths, baseNumerator, baseScale, terms, numerator, scale] =>
      let value :=
        { sourceIndex, sixths, baseNumerator, baseScale, terms, numerator, scale }
      if value.valid then some value else none
  | _ => none

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-exp-negative.source" }
def expKey : OpKey := { name := "pnt-exp-negative.exp" }
def ruleKey : RuleKey := { name := "pnt-exp-negative.sixth-power" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def expOperation : Operation := { key := expKey, inputs := [real], output := real }
def operations : Array Operation := #[sourceOperation, expOperation]
def node (index : Nat) : NodeId := { index }
def payload : PayloadId := { index := 0 }
def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def expInstruction : Node := { domain := real, op := { index := 1 }, args := [node 0] }
def program : Program := { operations, nodes := #[sourceInstruction, expInstruction] }

def registration : Registration :=
  { key := ruleKey, head := expKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => (decode? body).isSome }

def plan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      match input.fact with
      | .exact source =>
          match certificateFor? source.sourceIndex with
          | some value =>
              if value.sixths == source.sixths then
                { outcome :=
                    .success
                      [{ node := target, fact := .upper value.upper, payload }] []
                      { arithmeticWork := value.terms + value.sixths,
                        estimatedProofNodes := value.terms + 5 }
                  drafts :=
                    [{ label := payload, role := .fact, schema := 1,
                       body := encode value }] }
              else
                { outcome := .noChange {}, drafts := [] }
          | none => { outcome := .noChange {}, drafts := [] }
      | _ => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def expPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[expOperation],
    handlers := #[Handler.statelessPlanned registration plan #[factFormat]] }
def packages : Array (Package Bound) := #[sourcePackage, expPackage]

def checkerInput (value : Certificate) : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program, initialFacts := #[.exact value.source, .all],
    target := { node := node 1, fact := .upper value.upper } }

def representative : Certificate :=
  (certificateFor? 37).getD defaultCertificate

def representativeInput : SemanticReplay.CheckerInput Bound :=
  checkerInput representative

def engineLimits : State.Limits :=
  { maxOperations := 2, maxNodes := 2, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 1, maxScopeNodes := 1, maxApplications := 2,
    maxQueueEntries := 8, maxActions := 4, maxMatcherVisits := 2,
    matcherBatchSize := 2, maxAcceptedFacts := 2, maxRetainedSuggestions := 0,
    maxEffort := 0, maxObservationValue := 2048, maxDiagnosticValue := 4096,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 0, maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8, maxTraversal := 32, maxLiveOffers := 8 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 16, maxDrafts := 2, maxDraftCells := 16,
    maxAtom := 846481724891, maxSchema := 1, maxUses := 2 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.PntExpNegative
