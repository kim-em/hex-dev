/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Executable

/-!
Conformance for the sealed executable package/application assembly. The
fixture combines a built-in-style addition package with an independently
declared sine-shaped operation; the Mathlib-free layer treats both only by
stable keys and typed signatures.
-/

namespace Hex.Interval.ExecutableConformance

open Executable

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "hex.interval.source" }
def addKey : OpKey := { name := "hex.interval.add" }
def sineKey : OpKey := { name := "fixture.sine" }

def addRuleKey : RuleKey := { name := "hex.interval.add.forward" }
def sineRuleKey : RuleKey := { name := "fixture.sine.forward" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def addOperation : Operation := { key := addKey, inputs := [real, real], output := real }
def sineOperation : Operation := { key := sineKey, inputs := [real], output := real }

def addRegistration : Registration :=
  { key := addRuleKey, head := addKey, kind := .forward
    watches := [.argument 0, .argument 1], writes := [.result] }

def sineRegistration : Registration :=
  { key := sineRuleKey, head := sineKey, kind := .forward
    watches := [.argument 0], writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => body == [1] }

def arithmeticMeasure (metadata : Nat) : Measure Nat Nat :=
  { metadata := { bytes := metadata, work := metadata }
    application := fun _ => { bytes := 1, work := 1 }
    cache := fun value => { bytes := value, work := value }
    result := fun _ => { bytes := 1, work := 1 } }

def sineMeasure : Measure (List Nat) Nat :=
  { metadata := { bytes := 20, work := 20 }
    application := fun _ => { bytes := 1, work := 1 }
    cache := fun values => { bytes := values.length, work := values.length }
    result := fun _ => { bytes := 1, work := 1 } }

def addHandler : Handler Nat Nat Nat :=
  { registration := addRegistration
    invoke := fun cache _ =>
      ({ result := 10 + cache, quotes := #[{ role := .fact, schema := 1, body := [1] }] },
        cache + 1)
    formats := #[factFormat] }

def sineHandler : Handler Nat Nat (List Nat) :=
  { registration := sineRegistration
    invoke := fun cache _ =>
      ({ result := 100 + cache.length,
          quotes := #[{ role := .fact, schema := 1, body := [1] }] },
        1 :: cache)
    formats := #[factFormat] }

def arithmeticPackage : Package Nat Nat :=
  { Cache := Nat, cache := 0
    operations := #[sourceOperation, addOperation]
    handlers := #[addHandler]
    measure := arithmeticMeasure 10 }

def sinePackage : Package Nat Nat :=
  { Cache := List Nat, cache := []
    operations := #[sineOperation]
    handlers := #[sineHandler]
    measure := sineMeasure }

def program : Program :=
  { operations := #[sourceOperation, addOperation, sineOperation]
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [{ index := 0 }, { index := 1 }] },
        { domain := real, op := { index := 2 }, args := [{ index := 2 }] }] }

def extendedProgram : Program :=
  { program with nodes := program.nodes ++
      #[{ domain := real, op := { index := 1 }, args := [{ index := 1 }, { index := 2 }] },
        { domain := real, op := { index := 2 }, args := [{ index := 4 }] }] }

def shortProgram : Program :=
  { program with nodes := program.nodes.extract 0 3 }

def oversizedInvalidProgram : Program :=
  { program with nodes := program.nodes ++
      #[{ domain := real, op := { index := 99 }, args := [] },
        { domain := real, op := { index := 99 }, args := [] },
        { domain := real, op := { index := 99 }, args := [] }] }

def scopedRegistration : Registration :=
  { sineRegistration with watches := [], writes := [], binding := .scoped }

def scopedBinding : ScopeBinding :=
  { rule := sineRuleKey, anchor := { index := 3 }
    watches := [{ index := 2 }], writes := [{ index := 3 }] }

def defaultScopedHandler : Handler Nat Nat (List Nat) :=
  { sineHandler with registration := scopedRegistration }

def scopedHandler : Handler Nat Nat (List Nat) :=
  { defaultScopedHandler with acceptsScope := fun actual binding =>
      actual.operations == program.operations && actual.nodes == program.nodes &&
        binding == scopedBinding }

def defaultScopedPackage : Package Nat Nat :=
  { sinePackage with handlers := #[defaultScopedHandler] }

def scopedPackage : Package Nat Nat :=
  { sinePackage with handlers := #[scopedHandler] }

def fullAddRegistration : Registration :=
  { addRegistration with watches := [.result, .argument 0, .argument 1] }

def fullAddHandler : Handler Nat Nat Nat :=
  { addHandler with registration := fullAddRegistration }

def fullAddPackage : Package Nat Nat :=
  { arithmeticPackage with handlers := #[fullAddHandler] }

def oversizedAddRegistration : Registration :=
  { addRegistration with
    watches := [.result, .argument 0, .argument 1, .result] }

def oversizedAddHandler : Handler Nat Nat Nat :=
  { addHandler with registration := oversizedAddRegistration }

def oversizedAddPackage : Package Nat Nat :=
  { arithmeticPackage with handlers := #[oversizedAddHandler] }

def effortRegistration : Registration :=
  { addRegistration with initialEffort := 1 }

def effortHandler : Handler Nat Nat Nat :=
  { addHandler with registration := effortRegistration }

def effortPackage : Package Nat Nat :=
  { arithmeticPackage with handlers := #[effortHandler] }

def undeclaredHeadPackage : Package Nat Nat :=
  { sinePackage with operations := #[], requiredOperations := #[] }

def mismatchedSineOperation : Operation :=
  { sineOperation with inputs := [real, real] }

def rejectedProgramPackage : Package Nat Nat :=
  { sinePackage with operations := #[], requiredOperations := #[mismatchedSineOperation] }

def stateLimits : State.Limits :=
  { maxOperations := 3
    maxNodes := 6
    maxRules := 2
    maxRegistryEntries := 9
    maxReplayFormats := 2
    maxArity := 2
    maxScopeNodes := 1
    maxApplications := 4
    maxQueueEntries := 8
    maxActions := 8
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 8
    maxDiagnosticValue := 8
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 0
    maxProposalItems := 0
    maxInstances := 1
    maxGeneration := 1
    maxNodeDepth := 4
    maxEqualities := 1
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 8 } }

def limits : Limits :=
  { state := stateLimits
    maxPackages := 2
    maxMetadataBytes := 32
    maxMetadataWork := 32
    maxCacheBytes := 3
    maxCacheWork := 3
    maxResultBytes := 1
    maxResultWork := 1
    maxQuotes := 1
    maxQuoteCells := 1
    maxAtom := 1
    maxSchema := 1 }

def assembly? (limits : Limits := limits) : Option (Assembly Nat Nat) :=
  (buildWithin limits #[arithmeticPackage, sinePackage] program).toOption

def scopedAssembly? (limits : Limits := limits)
    (package : Package Nat Nat := scopedPackage) : Option (Assembly Nat Nat) :=
  (buildWithin limits #[package] program #[scopedBinding]).toOption

def buildError (limits : Limits) (packages : Array (Package Nat Nat))
    (actualProgram : Program := program) (bindings : Array ScopeBinding := #[]) : Option Error :=
  match buildWithin limits packages actualProgram bindings with
  | .ok _ => none
  | .error error => some error

def extendError (limits : Limits) (actualProgram : Program) (generation : Nat) : Option Error :=
  match assembly? with
  | none => none
  | some assembly =>
      match assembly.extendWithin limits actualProgram generation with
      | .ok _ => none
      | .error error => some error

def programView : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := #[0, 0, 0, 0]
    depths := #[0, 0, 1, 2] }

def addAction : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 }
    rule := { index := 0 }, key := addRuleKey, node := { index := 2 }
    kind := .forward, effort := 0
    inputs := [{ node := { index := 0 }, version := 0 },
      { node := { index := 1 }, version := 0 }]
    writes := [{ index := 2 }] }

def addRequest : RuleRequest Nat :=
  { action := addAction, program := programView
    inputs := [{ node := { index := 0 }, fact := 2, version := 0 },
      { node := { index := 1 }, fact := 3, version := 0 }]
    writes := [{ index := 2 }] }

def sineAction : Action :=
  { serial := 1, programVersion := 0, application := { index := 1 }
    rule := { index := 1 }, key := sineRuleKey, node := { index := 3 }
    kind := .forward, effort := 0
    inputs := [{ node := { index := 2 }, version := 0 }]
    writes := [{ index := 3 }] }

def sineRequest : RuleRequest Nat :=
  { action := sineAction, program := programView
    inputs := [{ node := { index := 2 }, fact := 5, version := 0 }]
    writes := [{ index := 3 }] }

def quoteHandler (quote : Quote) : Handler Nat Nat Nat :=
  { addHandler with invoke := fun cache _ =>
      ({ result := 10 + cache, quotes := #[quote] }, cache + 1) }

def quotePackage (quote : Quote) : Package Nat Nat :=
  { arithmeticPackage with handlers := #[quoteHandler quote] }

def invokePackageError (limits : Limits) (package : Package Nat Nat)
    (request : RuleRequest Nat := addRequest) : Option Error :=
  match buildWithin limits #[package] program with
  | .error error => some error
  | .ok assembly =>
      match assembly.invokeWithin limits request with
      | .ok _ => none
      | .error error => some error

def invokeError (request : RuleRequest Nat) : Option Error :=
  match assembly? with
  | none => none
  | some assembly =>
      match Assembly.invokeWithin limits assembly request with
      | .ok _ => none
      | .error error => some error

#guard program.check
#guard programView.check
#guard assembly?.isSome
#guard match assembly? with | some assembly => assembly.applications.size == 2 | none => false
#guard match assembly? with
  | some assembly => assembly.applications[0]?.map (·.node) == some { index := 2 }
  | none => false
#guard match assembly? with
  | some assembly => assembly.applications[1]?.map (·.node) == some { index := 3 }
  | none => false

-- A binary local registration may mention its result plus both arguments:
-- the exact port boundary is `maxArity + 1`, not `maxArity`.
#guard buildError limits #[fullAddPackage] == none
#guard buildError limits #[oversizedAddPackage] == some (.resource (.state .arity))

-- Initial effort is admitted at the exact boundary and refused one below.
#guard buildError limits #[effortPackage] == some (.resource (.state .effort))
#guard buildError { limits with state := { stateLimits with maxEffort := 1 } }
    #[effortPackage] == none

-- Explicit scoped assembly succeeds only through the package-owned semantic
-- hook. Its default hook fails closed, and count/port caps run before it.
#guard scopedAssembly?.isSome
#guard match scopedAssembly? with
  | some assembly =>
      assembly.applications[0]?.map (fun application =>
        (application.node, application.watches, application.writes)) ==
          some ({ index := 3 }, [{ index := 2 }], [{ index := 3 }])
  | none => false
#guard buildError limits #[defaultScopedPackage] program #[scopedBinding] ==
  some .invalidBindings
#guard buildError { limits with state := { stateLimits with maxScopeNodes := 0 } }
    #[scopedPackage] program #[scopedBinding] == some (.resource (.state .scopes))
#guard buildError { limits with state := { stateLimits with maxApplications := 0 } }
    #[scopedPackage] program #[scopedBinding] == some (.resource (.state .applications))

-- Registry/program correspondence and append-only ownership fail closed.
#guard match buildError limits #[undeclaredHeadPackage] with
  | some (.undeclaredHead rule head) => rule == sineRuleKey && head == sineKey
  | _ => false
#guard buildError limits #[rejectedProgramPackage] == some .programRejected
#guard extendError limits shortProgram 1 == some .nonExtension

-- Structural caps precede full program validation in both public builders.
#guard buildError limits #[arithmeticPackage, sinePackage] oversizedInvalidProgram ==
  some (.resource (.state .nodes))
#guard extendError limits oversizedInvalidProgram 1 == some (.resource (.state .nodes))

-- Exact application routing updates only the selected private cache. The
-- second addition observes cache `1` even though sine ran between the calls.
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin limits addRequest with
      | .error _ => false
      | .ok (add, assembly) =>
          add.result == 10 && add.rule == addRuleKey && add.route == { package := 0, handler := 0 } &&
            match assembly.invokeWithin limits sineRequest with
            | .error _ => false
            | .ok (sine, assembly) =>
                sine.result == 100 && sine.route == { package := 1, handler := 0 } &&
                  match assembly.invokeWithin limits addRequest with
                  | .error _ => false
                  | .ok (again, _) => again.result == 11

-- Transplanted application identity, compact route, stable rule, anchor,
-- creation generation, and structural fields all reject independently.
#guard invokeError { addRequest with action := { addAction with application := { index := 1 } } }
  == some .wrongRoute
#guard invokeError { addRequest with action := { addAction with application := { index := 99 } } }
  == some .invalidApplication
#guard invokeError { addRequest with action := { addAction with rule := { index := 1 } } }
  == some .wrongRoute
#guard invokeError { addRequest with action := { addAction with key := sineRuleKey } }
  == some .invalidRequest
#guard invokeError { addRequest with action := { addAction with node := { index := 3 } } }
  == some .invalidApplication
#guard invokeError { addRequest with action := { addAction with generation := 1 } }
  == some .invalidApplication
#guard invokeError { addRequest with action := { addAction with inputs := [] } }
  == some .invalidApplication
#guard invokeError { addRequest with action := { addAction with writes := [] } }
  == some .invalidApplication
#guard invokeError
    { addRequest with action := { addAction with
        structuralInputs := [{ key := .node { index := 0 }, generation := 0 }]
        matcherEpoch := some 0 } } == some .invalidApplication

def duplicateOperationPackage : Package Nat Nat :=
  { sinePackage with operations := #[addOperation], requiredOperations := #[sineOperation] }

def duplicateRuleHandler : Handler Nat Nat (List Nat) :=
  { sineHandler with registration := { sineRegistration with key := addRuleKey } }

def duplicateRulePackage : Package Nat Nat :=
  { sinePackage with handlers := #[duplicateRuleHandler] }

def duplicateFormatHandler : Handler Nat Nat (List Nat) :=
  { sineHandler with formats := #[factFormat, factFormat] }

def duplicateFormatPackage : Package Nat Nat :=
  { sinePackage with handlers := #[duplicateFormatHandler] }

def duplicateFormatLimits : Limits :=
  { limits with state :=
      { stateLimits with maxReplayFormats := 3, maxRegistryEntries := 10 } }

#guard
  match buildWithin
      { limits with state := { stateLimits with maxRegistryEntries := 10 } }
      #[arithmeticPackage, duplicateOperationPackage] program with
  | .error (.duplicateOperation key) => key == addKey
  | _ => false
#guard
  match buildWithin limits #[arithmeticPackage, duplicateRulePackage] program with
  | .error (.duplicateRule key) => key == addRuleKey
  | _ => false
#guard
  match buildWithin duplicateFormatLimits
      #[arithmeticPackage, duplicateFormatPackage] program with
  | .error (.duplicateFormat key) =>
      key == { rule := sineRuleKey, role := .fact, schema := 1 }
  | _ => false

-- Quotations must use an exact declared role/schema address and pass that
-- declaration's package-owned body decoder.
#guard invokePackageError limits
    (quotePackage { role := .equality, schema := 1, body := [1] }) ==
  some (.undeclaredFormat { rule := addRuleKey, role := .equality, schema := 1 })
#guard invokePackageError { limits with maxSchema := 2 }
    (quotePackage { role := .fact, schema := 2, body := [1] }) ==
  some (.undeclaredFormat { rule := addRuleKey, role := .fact, schema := 2 })
#guard invokePackageError limits
    (quotePackage { role := .fact, schema := 1, body := [0] }) ==
  some (.invalidBody { rule := addRuleKey, role := .fact, schema := 1 })

-- Append-only program growth preserves every old application byte-for-byte
-- and assigns the exact fresh generation to the local suffix.
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.extendWithin
          { limits with maxMetadataBytes := 34, maxMetadataWork := 34 }
          extendedProgram 1 with
      | .error _ => false
      | .ok extended =>
          applicationsPrefix assembly.applications extended.applications &&
            extended.applications.size == 4 &&
              extended.applications[2]?.map (·.generation) == some 1 &&
                extended.applications[3]?.map (·.generation) == some 1

#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.extendWithin limits extendedProgram 0 with
      | .error .staleGeneration => true
      | _ => false

-- Exact one-over guards for every retained assembly dimension and reply stage.
#guard assembly? { limits with maxPackages := 1 } |>.isNone
#guard assembly? { limits with state := { stateLimits with maxOperations := 2 } } |>.isNone
#guard assembly? { limits with state := { stateLimits with maxRules := 1 } } |>.isNone
#guard assembly? { limits with state := { stateLimits with maxReplayFormats := 1 } } |>.isNone
#guard assembly? { limits with state := { stateLimits with maxRegistryEntries := 8 } } |>.isNone
#guard assembly? { limits with state := { stateLimits with maxApplications := 1 } } |>.isNone
#guard assembly? { limits with maxMetadataBytes := 31 } |>.isNone
#guard assembly? { limits with maxMetadataWork := 31 } |>.isNone

#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin { limits with maxResultBytes := 0 } addRequest with
      | .error (.resource .resultBytes) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin { limits with maxQuotes := 0 } addRequest with
      | .error (.resource .quotes) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin { limits with maxQuoteCells := 0 } addRequest with
      | .error (.resource .quoteCells) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin { limits with maxAtom := 0 } addRequest with
      | .error (.resource .atom) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin { limits with maxSchema := 0 } addRequest with
      | .error (.resource .schema) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin
          { limits with maxCacheBytes := 0, maxCacheWork := 3 } addRequest with
      | .error (.resource .cacheBytes) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin
          { limits with maxCacheBytes := 3, maxCacheWork := 0 } addRequest with
      | .error (.resource .cacheWork) => true
      | _ => false
#guard
  match assembly? with
  | none => false
  | some assembly =>
      match assembly.invokeWithin { limits with maxResultWork := 0 } addRequest with
      | .error (.resource .resultWork) => true
      | _ => false

end Hex.Interval.ExecutableConformance
