/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexRealRoots.IsolateSturm
public import HexRealRoots.Refine
public import HexRoots.IsolateAll
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec
import all HexRealRoots.IsolateSturm
import all HexRealRoots.Refine
import all HexRoots.Basic
import all HexRoots.IsolateAll
import all HexPolyZ.IntegerPolynomial
import all HexRoots
import all HexRealRoots
import all HexPolyZ
import all HexPoly.Euclid.Content
import all HexPolyZ.Mignotte
import all HexRoots.MahlerPrec
import all HexRoots.Cauchy
import all HexRoots.Refine
import all HexRoots.Kantorovich
import all HexRoots.Pellet
import all HexRoots.SoftPellet
import all HexRoots.Taylor
import all HexRoots.Bisection
import all HexRoots.Newton

@[expose] public section

/-!
# Specialized polynomial dispatch

This experiment recognizes a univariate integer polynomial from operation keys
and structural arguments, then calls the real Sturm or complex NK/Pellet root
isolator.  Recognition is independent of the two acceptance polynomials: a
`Language` supplies the variable, constant, addition, subtraction, and
multiplication keys, and the recursive recognizer constructs a `ZPoly`.

The finite output facts and payload recipes remain bounded canaries.  The
Mathlib companion is solely responsible for turning an authenticated backend
result into semantic evidence.
-/

namespace Hex.Interval.Experiment.PolynomialDispatch

open Propagator PayloadArena
open Hex

inductive Bound where
  | all
  | cubeTwoReal
  | pisotComplex
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .cubeTwoReal, .cubeTwoReal => .cubeTwoReal
  | .pisotComplex, .pisotComplex => .pisotComplex
  | _, _ => .empty

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def valueDomain : DomainId := { index := 0 }

def variableKey : OpKey := { name := "polynomial.variable" }
def otherVariableKey : OpKey := { name := "polynomial.variable.1" }
def oneKey : OpKey := { name := "polynomial.integer.1" }
def twoKey : OpKey := { name := "polynomial.integer.2" }
def addKey : OpKey := { name := "polynomial.add" }
def subKey : OpKey := { name := "polynomial.sub" }
def mulKey : OpKey := { name := "polynomial.mul" }
def expKey : OpKey := { name := "nonpolynomial.exp" }
def realRootsKey : OpKey := { name := "polynomial.real-roots" }
def complexRootsKey : OpKey := { name := "polynomial.complex-roots" }

def nullary (key : OpKey) : Operation :=
  { key, inputs := [], output := valueDomain }

def unary (key : OpKey) : Operation :=
  { key, inputs := [valueDomain], output := valueDomain }

def binary (key : OpKey) : Operation :=
  { key, inputs := [valueDomain, valueDomain], output := valueDomain }

def operations : Array Operation :=
  #[nullary variableKey, nullary otherVariableKey, nullary oneKey,
    nullary twoKey, binary addKey, binary subKey, binary mulKey,
    unary expKey, binary realRootsKey, binary complexRootsKey]

/-- Operation-key vocabulary for polynomial reconstruction.  Constants are a
table, so adding another integer literal does not change the recognizer. -/
structure Language where
  indeterminate : OpKey
  constants : List (OpKey × Int)
  add : OpKey
  sub : OpKey
  mul : OpKey

def language : Language :=
  { indeterminate := variableKey
    constants := [(oneKey, 1), (twoKey, 2)]
    add := addKey
    sub := subKey
    mul := mulKey }

def Language.constant? (self : Language) (key : OpKey) : Option Int :=
  (self.constants.find? fun entry => entry.1 == key).map (fun entry => entry.2)

/-- Reconstruct a univariate `ZPoly` by structural recursion over registered
operation keys.  Unknown keys, extra variables, malformed arities, and an
exhausted resource bound decline with `none`. -/
def recognize? (vocabulary : Language) (view : ProgramView)
    (indeterminate : NodeId) : Nat → NodeId → Option ZPoly
  | 0, _ => none
  | fuel + 1, target => do
      let instruction ← view.node? target
      let key ← view.operationKey? target
      if key == vocabulary.indeterminate then
        if target == indeterminate && instruction.args == [] then
          some (DensePoly.monomial 1 1)
        else none
      else if let some coefficient := vocabulary.constant? key then
        if instruction.args == [] then some (DensePoly.C coefficient) else none
      else if key == vocabulary.add then
        match instruction.args with
        | [left, right] =>
            return (← recognize? vocabulary view indeterminate fuel left) +
              (← recognize? vocabulary view indeterminate fuel right)
        | _ => none
      else if key == vocabulary.sub then
        match instruction.args with
        | [left, right] =>
            return (← recognize? vocabulary view indeterminate fuel left) -
              (← recognize? vocabulary view indeterminate fuel right)
        | _ => none
      else if key == vocabulary.mul then
        match instruction.args with
        | [left, right] =>
            return (← recognize? vocabulary view indeterminate fuel left) *
              (← recognize? vocabulary view indeterminate fuel right)
        | _ => none
      else none

def polynomialCode (p : ZPoly) : List Int :=
  (List.range p.size).map p.coeff

def cubeTwoCode : List Int := [-2, 0, 0, 1]
def pisotCode : List Int := [-1, -1, 0, 1]

def cubeTwo : ZPoly := DensePoly.ofCoeffs cubeTwoCode.toArray
def pisot : ZPoly := DensePoly.ofCoeffs pisotCode.toArray

structure RealRegion where
  lower : Dyadic
  upper : Dyadic

/-- The real backend is the actual Sturm isolator followed by cached exact
bisection refinement of every emitted interval. -/
def realBackend? (p : ZPoly) (target : Int) : Option (Array RealRegion) := do
  let output ← isolateSturm? p
  let chain := ZPoly.sturmChain p
  return output.isolations.map fun isolation =>
    let refined := isolation.refineToWithChain chain rfl target
    { lower := refined.interval.lower, upper := refined.interval.upper }

/-- Plain square projection of the proof-carrying complex backend. -/
def complexBackend? (p : ZPoly) (target : Int) : Option (Array DyadicSquare) :=
  if simple : HasOnlySimpleRoots p then
    (Hex.isolate p simple target .nk).map fun isolations =>
      isolations.map (fun isolation => isolation.square)
  else none

def cubeTwoLower : Dyadic := Dyadic.ofIntWithPrec 5 2
def cubeTwoUpper : Dyadic := Dyadic.ofIntWithPrec 21 4

def realResultMatches : Option (Array RealRegion) → Bool
  | some regions =>
      regions.size == 1 &&
        regions[0]?.any fun region =>
          region.lower == cubeTwoLower && region.upper == cubeTwoUpper
  | none => false

def pisotSquares : Array DyadicSquare :=
  #[{ re := .ofIntWithPrec (-91033924845) 37
      im := .ofIntWithPrec (-77279107697) 37
      prec := 33 },
    { re := .ofIntWithPrec (-91033924845) 37
      im := .ofIntWithPrec 4829944231 33
      prec := 33 },
    { re := .ofIntWithPrec 182067849689 37
      im := 0
      prec := 33 }]

def squareEq (left right : DyadicSquare) : Bool :=
  left.re == right.re && left.im == right.im && left.prec == right.prec

def complexResultMatches : Option (Array DyadicSquare) → Bool
  | some regions =>
      regions.size == pisotSquares.size &&
        (List.range pisotSquares.size).all fun index =>
          match regions[index]?, pisotSquares[index]? with
          | some left, some right => squareEq left right
          | _, _ => false
  | none => false

def encodeInt : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def realBody : List Nat :=
  [0, cubeTwoCode.length] ++ cubeTwoCode.map encodeInt ++
    [4, 5, 4, 21, 16]

def complexBody : List Nat :=
  [1, pisotCode.length] ++ pisotCode.map encodeInt ++
    [32, 3,
      encodeInt (-91033924845), 37, encodeInt (-77279107697), 37, 33,
      encodeInt (-91033924845), 37, encodeInt 4829944231, 33, 33,
      encodeInt 182067849689, 37, encodeInt 0, 0, 33]

structure DispatchCertificate where
  backend : Nat
  coefficients : List Int
  precision : Nat
  deriving DecidableEq, Repr

def realCertificate : DispatchCertificate :=
  { backend := 0, coefficients := cubeTwoCode, precision := 4 }

def complexCertificate : DispatchCertificate :=
  { backend := 1, coefficients := pisotCode, precision := 32 }

def decodeReal? : List Nat → Option DispatchCertificate
  | [0, 4, 3, 0, 0, 2, 4, 5, 4, 21, 16] => some realCertificate
  | _ => none

def decodeComplex? : List Nat → Option DispatchCertificate
  | [1, 4, 1, 1, 0, 2, 32, 3,
      182067849689, 37, 154558215393, 37, 33,
      182067849689, 37, 9659888462, 33, 33,
      364135699378, 37, 0, 0, 33] => some complexCertificate
  | _ => none

def realFormat : ReplayFormat :=
  { role := .fact, schema := 1
    validateBody := fun body => decodeReal? body == some realCertificate }

def complexFormat : ReplayFormat :=
  { role := .fact, schema := 2
    validateBody := fun body => decodeComplex? body == some complexCertificate }

def realRuleKey : RuleKey := { name := "polynomial.dispatch.real" }
def complexRuleKey : RuleKey := { name := "polynomial.dispatch.complex" }

def realRule : Registration :=
  { key := realRuleKey, head := realRootsKey, kind := .forward,
    watches := [], writes := [.result] }

def complexRule : Registration :=
  { key := complexRuleKey, head := complexRootsKey, kind := .forward,
    watches := [], writes := [.result] }

def payload (index : Nat) : PayloadId := { index }
def node (index : Nat) : NodeId := { index }

def polynomialInput? (request : RuleRequest Bound) : Option ZPoly := do
  let instruction ← request.program.node? request.action.node
  let [indeterminate, polynomial] := instruction.args | none
  recognize? language request.program indeterminate
    (request.program.nodes.size + 1) polynomial

def realPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [], [target] =>
      match polynomialInput? request with
      | some p =>
          if polynomialCode p == cubeTwoCode && realResultMatches (realBackend? p 4) then
            { outcome :=
                .success [{ node := target, fact := .cubeTwoReal, payload := payload 0 }]
                  [] { arithmeticWork := 4, estimatedProofNodes := 12 }
              drafts :=
                [{ label := payload 0, role := .fact, schema := 1, body := realBody }] }
          else { outcome := .noChange {}, drafts := [] }
      | none => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def complexPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [], [target] =>
      match polynomialInput? request with
      | some p =>
          if polynomialCode p == pisotCode &&
              complexResultMatches (complexBackend? p 32) then
            { outcome :=
                .success [{ node := target, fact := .pisotComplex, payload := payload 0 }]
                  [] { arithmeticWork := 32, estimatedProofNodes := 24 }
              drafts :=
                [{ label := payload 0, role := .fact, schema := 2, body := complexBody }] }
          else { outcome := .noChange {}, drafts := [] }
      | none => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 2, drafts := [] }

def realPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations
    handlers := #[Handler.statelessPlanned realRule realPlan #[realFormat]] }

def complexPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations
    handlers := #[Handler.statelessPlanned complexRule complexPlan #[complexFormat]] }

def realPackages : Array (Package Bound) := #[realPackage]
def complexPackages : Array (Package Bound) := #[complexPackage]
def packages : Array (Package Bound) := #[realPackage, complexPackage]

def instruction (operation : Nat) (arguments : List NodeId := []) : Node :=
  { domain := valueDomain, op := { index := operation }, args := arguments }

/-- `x³ - 2`, followed by the real-root query. -/
def realProgram : Program :=
  { operations
    nodes :=
      #[instruction 0, instruction 3, instruction 6 [node 0, node 0],
        instruction 6 [node 2, node 0], instruction 5 [node 3, node 1],
        instruction 8 [node 0, node 4]] }

/-- `x³ - x - 1`, followed by the complex-root query. -/
def complexProgram : Program :=
  { operations
    nodes :=
      #[instruction 0, instruction 2, instruction 6 [node 0, node 0],
        instruction 6 [node 2, node 0], instruction 5 [node 3, node 0],
        instruction 5 [node 4, node 1], instruction 9 [node 0, node 5]] }

def engineLimits : Propagator.Limits :=
  { maxOperations := 10
    maxNodes := 8
    maxRules := 2
    maxRegistryEntries := 16
    maxReplayFormats := 4
    maxArity := 2
    maxScopeNodes := 1
    maxApplications := 2
    maxQueueEntries := 8
    maxActions := 4
    maxMatcherVisits := 2
    matcherBatchSize := 2
    maxAcceptedFacts := 2
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 64
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 5
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 32, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 2
    maxBodyCells := 32
    maxDrafts := 1
    maxDraftCells := 32
    maxAtom := 400000000000
    maxSchema := 2
    maxUses := 2 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def realStart : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain realProgram realPackages
    (Array.replicate realProgram.nodes.size .all) limits

def complexStart : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain complexProgram complexPackages
    (Array.replicate complexProgram.nodes.size .all) limits

end Hex.Interval.Experiment.PolynomialDispatch
