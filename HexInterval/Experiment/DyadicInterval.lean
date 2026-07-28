/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Propagator

@[expose] public section

/-!
# Checked dyadic interval facts

This module is the first concrete fact domain for the function-agnostic
propagation experiment.  It retains open, closed, and independently unbounded
cuts exactly.  Every comparison and endpoint-producing arithmetic operation is
preceded by a deterministic size preflight.

`Fact` carries a dependent consistency witness, so malformed cuts cannot enter
a propagation engine through this API.  `start` additionally rejects an
initially empty fact; an empty interval is reserved for a contradiction
discovered by narrowing.

The arithmetic surface is deliberately honest about its current boundary.
Finite multiplication is exact and attainment-sensitive, while multiplication
with an unbounded factor is reported as `inapplicable`.  Reciprocal handles the
positive and negative components (including an open zero endpoint) and reports
mixed-sign input as `inapplicable` until interval-set support is available.
-/

namespace Hex.Interval.Experiment.DyadicInterval

open Propagator

/-! ## Checked representation and resource results -/

/-- A canonical raw interval.  Constructing one from malformed raw cuts would
require a proof of a false consistency check; ordinary callers instead use the
smart constructors below or cross the checked `importRaw` boundary. -/
structure Fact where
  raw : Raw
  isConsistent : raw.CutConsistent

namespace Fact

instance : DecidableEq Fact := fun left right =>
  if h : left.raw = right.raw then
    isTrue (by cases left; cases right; simp_all)
  else
    isFalse fun equality => h (congrArg Fact.raw equality)

/-- Exact raw view used by conformance and, later, certificate freezing. -/
def view (fact : Fact) : Raw := fact.raw

/-- The unique canonical empty fact.  It is an operation result, never an
accepted initial engine fact. -/
def empty : Fact := ⟨.empty, Raw.cutConsistent_empty⟩

/-- The interval with neither a lower nor an upper bound. -/
def whole : Fact := ⟨.bounds .unbounded .unbounded, rfl⟩

def isEmpty (fact : Fact) : Bool :=
  match fact.raw with
  | .empty => true
  | .bounds _ _ => false

def isWhole (fact : Fact) : Bool := fact.raw == .bounds .unbounded .unbounded

end Fact

/-- The work whose configured limit was exceeded.  Values are computed without
first performing the potentially allocating comparison or arithmetic step. -/
inductive WorkCost where
  | endpoint (cost : EndpointCost)
  | comparison (cost : CompareCost)
  | arithmetic (left right : EndpointCost)
  | inverse (input : EndpointCost) (precisionMagnitude alignmentShift : Nat)
  deriving DecidableEq, Repr

/-- Result of a canonical smart constructor or interval operation. -/
inductive Result where
  | ready (fact : Fact)
  | inapplicable
  | resourceLimit (cost : WorkCost)
  deriving DecidableEq

/-- Result of importing an untrusted raw fact.  Inconsistent raw cuts are
malformed, rather than silently being reinterpreted as a proved empty set. -/
inductive ImportResult where
  | ready (fact : Fact)
  | malformed
  | resourceLimit (cost : WorkCost)
  deriving DecidableEq

def workMagnitude : WorkCost -> Nat
  | .endpoint cost => cost.numeratorBits + cost.exponentMagnitude
  | .comparison cost =>
      cost.lower.numeratorBits + cost.lower.exponentMagnitude +
        cost.upper.numeratorBits + cost.upper.exponentMagnitude + cost.alignmentShift
  | .arithmetic left right =>
      left.numeratorBits + left.exponentMagnitude +
        right.numeratorBits + right.exponentMagnitude
  | .inverse input precisionMagnitude alignmentShift =>
      input.numeratorBits + input.exponentMagnitude + precisionMagnitude + alignmentShift

/-! ## Preflight helpers -/

def endpointChecked (limit : EndpointLimit) (value : Dyadic) : Except WorkCost Unit :=
  let cost := EndpointCost.ofDyadic value
  if cost.allowed limit then pure () else throw (.endpoint cost)

def compareChecked (limit : EndpointLimit) (left right : Dyadic) :
    Except WorkCost Ordering := do
  let cost := CompareCost.ofDyadic left right
  if !cost.allowed limit then throw (.comparison cost)
  if left < right then pure .lt
  else if left = right then pure .eq
  else pure .gt

/-- Check several bounded size contributions without constructing their sum. -/
def fitHeight (remaining : Nat) : List Nat -> Bool
  | [] => true
  | cost :: costs =>
      if cost ≤ remaining then fitHeight (remaining - cost) costs else false

def preflightSubtraction (limit : EndpointLimit) (left right : Dyadic) :
    Except WorkCost Unit := do
  let comparison := CompareCost.ofDyadic left right
  if !comparison.allowed limit then throw (.comparison comparison)

def subtractionChecked (limit : EndpointLimit) (left right : Dyadic) :
    Except WorkCost Dyadic := do
  preflightSubtraction limit left right
  let result := left - right
  endpointChecked limit result
  pure result

def multiplicationAllowed (limit : EndpointLimit) (left right : Dyadic) : Bool :=
  let leftCost := EndpointCost.ofDyadic left
  let rightCost := EndpointCost.ofDyadic right
  leftCost.allowed limit && rightCost.allowed limit &&
    match left, right with
    | .zero, _ | _, .zero => true
    | .ofOdd _ leftExponent _, .ofOdd _ rightExponent _ =>
        fitHeight limit.maxEndpointHeight
          [leftCost.numeratorBits, rightCost.numeratorBits,
            (leftExponent + rightExponent).natAbs]

def multiplicationChecked (limit : EndpointLimit) (left right : Dyadic) :
    Except WorkCost Dyadic := do
  let leftCost := EndpointCost.ofDyadic left
  let rightCost := EndpointCost.ofDyadic right
  if !multiplicationAllowed limit left right then
    throw (.arithmetic leftCost rightCost)
  let result := left * right
  endpointChecked limit result
  pure result

def negationChecked (limit : EndpointLimit) (value : Dyadic) : Except WorkCost Dyadic := do
  endpointChecked limit value
  let result := -value
  endpointChecked limit result
  pure result

/-- Preflight the shift and retained endpoint work performed by `invAtPrec`.
The check is deliberately conservative: a requested precision and the
canonical input exponent must each fit the endpoint budget, and the sum of
their magnitudes must fit the alignment budget before Core's two separate
rational-conversion shifts run.  In particular, opposite-signed exponents do
not cancel in the preflight merely because their signed sum is small. -/
def inverseChecked (limit : EndpointLimit) (precision : Precision) (value : Dyadic) :
    Except WorkCost Dyadic := do
  let inputCost := EndpointCost.ofDyadic value
  let precisionMagnitude := precision.natAbs
  if !inputCost.allowed limit ||
      EndpointCost.natBits precisionMagnitude > limit.maxEndpointHeight ||
      precisionMagnitude > limit.maxEndpointHeight then
    throw (.inverse inputCost precisionMagnitude 0)
  let alignmentShift :=
    match value with
    | .zero => 0
    | .ofOdd _ exponent _ => exponent.natAbs + precisionMagnitude
  if alignmentShift > limit.maxAlignmentShift then
    throw (.inverse inputCost precisionMagnitude alignmentShift)
  let result := value.invAtPrec precision
  endpointChecked limit result
  pure result

/-! ## Smart constructors -/

/-- Normalize a trusted operation result after resource preflight. -/
def normalize (limit : EndpointLimit) (raw : Raw) : Result :=
  let cost := raw.normalizeCost
  if !cost.allowed limit then
    .resourceLimit (.comparison cost)
  else
    let normalized := raw.normalizeUnchecked
    .ready ⟨normalized, Raw.consistent_normalizeUnchecked raw⟩

/-- Import untrusted raw cuts without normalizing malformed input to empty. -/
def importRaw (limit : EndpointLimit) (raw : Raw) : ImportResult :=
  let cost := raw.normalizeCost
  if !cost.allowed limit then
    .resourceLimit (.comparison cost)
  else if h : raw.CutConsistent then
    .ready ⟨raw, h⟩
  else
    .malformed

def empty : Fact := Fact.empty

def whole : Fact := Fact.whole

/-- Smart constructor for arbitrary lower and upper cut shapes.  Inconsistent
cuts canonicalize to `empty`; malformed *imported* cuts use `importRaw`. -/
def bounds (limit : EndpointLimit) (lower : Lower) (upper : Upper) : Result :=
  normalize limit (.bounds lower upper)

def closed (limit : EndpointLimit) (lower upper : Dyadic) : Result :=
  bounds limit (.finite lower false) (.finite upper false)

def openInterval (limit : EndpointLimit) (lower upper : Dyadic) : Result :=
  bounds limit (.finite lower true) (.finite upper true)

def closedOpen (limit : EndpointLimit) (lower upper : Dyadic) : Result :=
  bounds limit (.finite lower false) (.finite upper true)

def openClosed (limit : EndpointLimit) (lower upper : Dyadic) : Result :=
  bounds limit (.finite lower true) (.finite upper false)

def atLeast (limit : EndpointLimit) (lower : Dyadic) : Result :=
  bounds limit (.finite lower false) .unbounded

def greaterThan (limit : EndpointLimit) (lower : Dyadic) : Result :=
  bounds limit (.finite lower true) .unbounded

def atMost (limit : EndpointLimit) (upper : Dyadic) : Result :=
  bounds limit .unbounded (.finite upper false)

def lessThan (limit : EndpointLimit) (upper : Dyadic) : Result :=
  bounds limit .unbounded (.finite upper true)

/-! ## Exact intersection -/

def intersectLower (limit : EndpointLimit) (left right : Lower) :
    Except WorkCost Lower := do
  match left, right with
  | .unbounded, cut | cut, .unbounded => pure cut
  | .finite leftValue leftStrict, .finite rightValue rightStrict =>
      match ← compareChecked limit leftValue rightValue with
      | .lt => pure right
      | .gt => pure left
      | .eq => pure (.finite leftValue (leftStrict || rightStrict))

def intersectUpper (limit : EndpointLimit) (left right : Upper) :
    Except WorkCost Upper := do
  match left, right with
  | .unbounded, cut | cut, .unbounded => pure cut
  | .finite leftValue leftStrict, .finite rightValue rightStrict =>
      match ← compareChecked limit leftValue rightValue with
      | .lt => pure left
      | .gt => pure right
      | .eq => pure (.finite leftValue (leftStrict || rightStrict))

/-- Exact set intersection.  Equal-valued cuts are open when either input cut
is open. -/
def intersect (limit : EndpointLimit) (left right : Fact) : Result :=
  match left.raw, right.raw with
  | .empty, _ | _, .empty => .ready .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match intersectLower limit leftLower rightLower with
      | .error cost => .resourceLimit cost
      | .ok lower =>
          match intersectUpper limit leftUpper rightUpper with
          | .error cost => .resourceLimit cost
          | .ok upper => normalize limit (.bounds lower upper)

/-! ## Unary negation and subtraction -/

def negateLower (limit : EndpointLimit) : Upper -> Except WorkCost Lower
  | .unbounded => pure .unbounded
  | .finite value strict => do
      pure (.finite (← negationChecked limit value) strict)

def negateUpper (limit : EndpointLimit) : Lower -> Except WorkCost Upper
  | .unbounded => pure .unbounded
  | .finite value strict => do
      pure (.finite (← negationChecked limit value) strict)

def neg (limit : EndpointLimit) (input : Fact) : Result :=
  match input.raw with
  | .empty => .ready .empty
  | .bounds lower upper =>
      match negateLower limit upper with
      | .error cost => .resourceLimit cost
      | .ok resultLower =>
          match negateUpper limit lower with
          | .error cost => .resourceLimit cost
          | .ok resultUpper => normalize limit (.bounds resultLower resultUpper)

def subtractLower (limit : EndpointLimit) (left : Lower) (right : Upper) :
    Except WorkCost Lower := do
  match left, right with
  | .finite leftValue leftStrict, .finite rightValue rightStrict =>
      pure (.finite (← subtractionChecked limit leftValue rightValue)
        (leftStrict || rightStrict))
  | _, _ => pure .unbounded

def subtractUpper (limit : EndpointLimit) (left : Upper) (right : Lower) :
    Except WorkCost Upper := do
  match left, right with
  | .finite leftValue leftStrict, .finite rightValue rightStrict =>
      pure (.finite (← subtractionChecked limit leftValue rightValue)
        (leftStrict || rightStrict))
  | _, _ => pure .unbounded

def preflightLowerSubtraction (limit : EndpointLimit) (left : Lower) (right : Upper) :
    Except WorkCost Unit := do
  match left, right with
  | .finite leftValue _, .finite rightValue _ =>
      preflightSubtraction limit leftValue rightValue
  | _, _ => pure ()

def preflightUpperSubtraction (limit : EndpointLimit) (left : Upper) (right : Lower) :
    Except WorkCost Unit := do
  match left, right with
  | .finite leftValue _, .finite rightValue _ =>
      preflightSubtraction limit leftValue rightValue
  | _, _ => pure ()

/-- Exact interval subtraction, including independently unbounded sides.  Both
finite endpoint-alignment pairs are preflighted before either subtraction is
evaluated. -/
def sub (limit : EndpointLimit) (left right : Fact) : Result :=
  match left.raw, right.raw with
  | .empty, _ | _, .empty => .ready .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match (do
        preflightLowerSubtraction limit leftLower rightUpper
        preflightUpperSubtraction limit leftUpper rightLower) with
      | .error cost => .resourceLimit cost
      | .ok () =>
          match subtractLower limit leftLower rightUpper with
          | .error cost => .resourceLimit cost
          | .ok lower =>
              match subtractUpper limit leftUpper rightLower with
              | .error cost => .resourceLimit cost
              | .ok upper => normalize limit (.bounds lower upper)

/-! ## Extrema with endpoint-attainment witnesses -/

structure Candidate where
  value : Dyadic
  attained : Bool

def chooseMin (limit : EndpointLimit) (left right : Candidate) :
    Except WorkCost Candidate := do
  match ← compareChecked limit left.value right.value with
  | .lt => pure left
  | .gt => pure right
  | .eq => pure { value := left.value, attained := left.attained || right.attained }

def chooseMax (limit : EndpointLimit) (left right : Candidate) :
    Except WorkCost Candidate := do
  match ← compareChecked limit left.value right.value with
  | .lt => pure right
  | .gt => pure left
  | .eq => pure { value := left.value, attained := left.attained || right.attained }

def minCandidates (limit : EndpointLimit) (first : Candidate) :
    List Candidate -> Except WorkCost Candidate
  | [] => pure first
  | next :: rest => do
      minCandidates limit (← chooseMin limit first next) rest

def maxCandidates (limit : EndpointLimit) (first : Candidate) :
    List Candidate -> Except WorkCost Candidate
  | [] => pure first
  | next :: rest => do
      maxCandidates limit (← chooseMax limit first next) rest

def containsZeroFinite (limit : EndpointLimit)
    (lower : Dyadic) (lowerStrict : Bool) (upper : Dyadic) (upperStrict : Bool) :
    Except WorkCost Bool := do
  let lowerOrder ← compareChecked limit lower 0
  let upperOrder ← compareChecked limit upper 0
  let lowerAllows := lowerOrder == .lt || (lowerOrder == .eq && !lowerStrict)
  let upperAllows := upperOrder == .gt || (upperOrder == .eq && !upperStrict)
  pure (lowerAllows && upperAllows)

def endpointCandidate (limit : EndpointLimit)
    (left : Dyadic × Bool) (right : Dyadic × Bool) : Except WorkCost Candidate := do
  pure
    { value := ← multiplicationChecked limit left.1 right.1
      attained := !left.2 && !right.2 }

/-! ## Finite multiplication and square -/

/-- Exact multiplication for two finite intervals.  Unbounded multiplication
is intentionally left to a later sign-partitioned implementation and returns
`inapplicable`.  Tied extrema combine attainment witnesses, including the
special fact that multiplication by any contained zero attains zero. -/
def mul (limit : EndpointLimit) (left right : Fact) : Result :=
  match left.raw, right.raw with
  | .empty, _ | _, .empty => .ready .empty
  | .bounds (.finite ll lls) (.finite lu lus),
      .bounds (.finite rl rls) (.finite ru rus) =>
      match (do
        let llc ← endpointCandidate limit (ll, lls) (rl, rls)
        let luc ← endpointCandidate limit (ll, lls) (ru, rus)
        let ulc ← endpointCandidate limit (lu, lus) (rl, rls)
        let uuc ← endpointCandidate limit (lu, lus) (ru, rus)
        let minimum ← minCandidates limit llc [luc, ulc, uuc]
        let maximum ← maxCandidates limit llc [luc, ulc, uuc]
        let leftZero ← containsZeroFinite limit ll lls lu lus
        let rightZero ← containsZeroFinite limit rl rls ru rus
        let zeroAttained := leftZero || rightZero
        let minimum :=
          if minimum.value = 0 && zeroAttained then { minimum with attained := true }
          else minimum
        let maximum :=
          if maximum.value = 0 && zeroAttained then { maximum with attained := true }
          else maximum
        pure (minimum, maximum)) with
      | .error cost => .resourceLimit cost
      | .ok (minimum, maximum) =>
          normalize limit (.bounds (.finite minimum.value (!minimum.attained))
            (.finite maximum.value (!maximum.attained)))
  | _, _ => .inapplicable

def squareFinite (limit : EndpointLimit)
    (lower : Dyadic) (lowerStrict : Bool) (upper : Dyadic) (upperStrict : Bool) :
    Except WorkCost (Lower × Upper) := do
  let lowerOrder ← compareChecked limit lower 0
  let upperOrder ← compareChecked limit upper 0
  let lowerSquare ← multiplicationChecked limit lower lower
  let upperSquare ← multiplicationChecked limit upper upper
  if upperOrder == .lt || upperOrder == .eq then
    pure (.finite upperSquare upperStrict, .finite lowerSquare lowerStrict)
  else if lowerOrder == .gt || lowerOrder == .eq then
    pure (.finite lowerSquare lowerStrict, .finite upperSquare upperStrict)
  else
    let upperCandidate ← chooseMax limit
      { value := lowerSquare, attained := !lowerStrict }
      { value := upperSquare, attained := !upperStrict }
    pure (.finite 0 false, .finite upperCandidate.value (!upperCandidate.attained))

/-- Tight square image.  A straddled zero is attained even when both finite
endpoints are open; tied squared maxima are closed when either source endpoint
is closed. -/
def square (limit : EndpointLimit) (input : Fact) : Result :=
  match input.raw with
  | .empty => .ready .empty
  | .bounds .unbounded .unbounded =>
      normalize limit (.bounds (.finite 0 false) .unbounded)
  | .bounds .unbounded (.finite upper upperStrict) =>
      match compareChecked limit upper 0 with
      | .error cost => .resourceLimit cost
      | .ok order =>
          if order == .lt || order == .eq then
            match multiplicationChecked limit upper upper with
            | .error cost => .resourceLimit cost
            | .ok lower => normalize limit
                (.bounds (.finite lower upperStrict) .unbounded)
          else
            normalize limit (.bounds (.finite 0 false) .unbounded)
  | .bounds (.finite lower lowerStrict) .unbounded =>
      match compareChecked limit lower 0 with
      | .error cost => .resourceLimit cost
      | .ok order =>
          if order == .gt || order == .eq then
            match multiplicationChecked limit lower lower with
            | .error cost => .resourceLimit cost
            | .ok lowerSquare => normalize limit
                (.bounds (.finite lowerSquare lowerStrict) .unbounded)
          else
            normalize limit (.bounds (.finite 0 false) .unbounded)
  | .bounds (.finite lower lowerStrict) (.finite upper upperStrict) =>
      match squareFinite limit lower lowerStrict upper upperStrict with
      | .error cost => .resourceLimit cost
      | .ok (resultLower, resultUpper) => normalize limit (.bounds resultLower resultUpper)

/-! ## Singleton scaling and exact backward scaling -/

def scaleLowerPositive (limit : EndpointLimit) (scalar : Dyadic) :
    Lower -> Except WorkCost Lower
  | .unbounded => pure .unbounded
  | .finite value strict => do
      pure (.finite (← multiplicationChecked limit scalar value) strict)

def scaleUpperPositive (limit : EndpointLimit) (scalar : Dyadic) :
    Upper -> Except WorkCost Upper
  | .unbounded => pure .unbounded
  | .finite value strict => do
      pure (.finite (← multiplicationChecked limit scalar value) strict)

/-- Exact image under multiplication by a singleton dyadic. -/
def scale (limit : EndpointLimit) (scalar : Dyadic) (input : Fact) : Result :=
  match input.raw with
  | .empty => .ready .empty
  | .bounds lower upper =>
      match compareChecked limit scalar 0 with
      | .error cost => .resourceLimit cost
      | .ok .eq => normalize limit (.bounds (.finite 0 false) (.finite 0 false))
      | .ok .gt =>
          match scaleLowerPositive limit scalar lower with
          | .error cost => .resourceLimit cost
          | .ok resultLower =>
              match scaleUpperPositive limit scalar upper with
              | .error cost => .resourceLimit cost
              | .ok resultUpper => normalize limit (.bounds resultLower resultUpper)
      | .ok .lt =>
          match scaleLowerPositive limit scalar
              (match upper with
               | .unbounded => .unbounded
               | .finite value strict => .finite value strict) with
          | .error cost => .resourceLimit cost
          | .ok provisionalLower =>
              match scaleUpperPositive limit scalar
                  (match lower with
                   | .unbounded => .unbounded
                   | .finite value strict => .finite value strict) with
              | .error cost => .resourceLimit cost
              | .ok provisionalUpper =>
                  let resultLower :=
                    match provisionalLower with
                    | .unbounded => .unbounded
                    | .finite value strict => .finite value strict
                  let resultUpper :=
                    match provisionalUpper with
                    | .unbounded => .unbounded
                    | .finite value strict => .finite value strict
                  normalize limit (.bounds resultLower resultUpper)

/-- Exact reciprocal exists precisely for a nonzero dyadic whose canonical odd
mantissa is `1` or `-1`. -/
def exactReciprocal? (limit : EndpointLimit) : Dyadic -> Except WorkCost (Option Dyadic)
  | .zero => pure none
  | value@(.ofOdd numerator exponent _) => do
      endpointChecked limit value
      if numerator = 1 || numerator = -1 then
        let result := Dyadic.ofIntWithPrec numerator (-exponent)
        endpointChecked limit result
        pure (some result)
      else
        pure none

/-- Backward image under singleton multiplication when division is exactly
dyadic.  Nondyadic reciprocal and zero scalar are explicitly inapplicable. -/
def unscaleExact (limit : EndpointLimit) (scalar : Dyadic) (image : Fact) : Result :=
  match exactReciprocal? limit scalar with
  | .error cost => .resourceLimit cost
  | .ok none => .inapplicable
  | .ok (some reciprocal) => scale limit reciprocal image

/-! ## Precision-indexed reciprocal -/

/-- Lower cut of a sign-separated reciprocal component.  A zero endpoint is
the one-sided unbounded limit and is never passed to pointwise inversion;
`reciprocal` separately rejects a closed zero in the original interval. -/
def inverseLower (limit : EndpointLimit) (precision : Precision)
    (upper : Upper) : Except WorkCost Lower := do
  match upper with
  | .unbounded => pure (.finite 0 true)
  | .finite value strict =>
      -- Zero is a boundary limit, never an input to `invAtPrec`.  The outer
      -- component check decides whether a closed zero makes the whole
      -- reciprocal inapplicable.
      if value = 0 then
        pure .unbounded
      else
        let rounded ← inverseChecked limit precision value
        let exact ← exactReciprocal? limit value
        pure (.finite rounded (strict || exact != some rounded))

/-- Upper cut of a sign-separated reciprocal component, with the same
zero-limit contract as `inverseLower`. -/
def inverseUpper (limit : EndpointLimit) (precision : Precision)
    (lower : Lower) : Except WorkCost Upper := do
  match lower with
  | .unbounded => pure (.finite 0 true)
  | .finite value strict =>
      -- As above, zero denotes the unbounded component limit and must not be
      -- passed to the pointwise inverse implementation.
      if value = 0 then
        pure .unbounded
      else
        let roundedDown ← inverseChecked limit precision (-value)
        let rounded := -roundedDown
        endpointChecked limit rounded
        let exact ← exactReciprocal? limit value
        pure (.finite rounded (strict || exact != some rounded))

def strictlyPositiveLower (limit : EndpointLimit) : Lower -> Except WorkCost Bool
  | .unbounded => pure false
  | .finite value strict => do
      match ← compareChecked limit value 0 with
      | .gt => pure true
      | .eq => pure strict
      | .lt => pure false

def strictlyNegativeUpper (limit : EndpointLimit) : Upper -> Except WorkCost Bool
  | .unbounded => pure false
  | .finite value strict => do
      match ← compareChecked limit value 0 with
      | .lt => pure true
      | .eq => pure strict
      | .gt => pure false

/-- Reciprocal enclosure for intervals wholly on the positive or negative side
of zero.  An open zero endpoint maps to an unbounded side.  Mixed-sign input,
closed zero, and the singleton zero are `inapplicable` in this first component
backend rather than being assigned a misleading connected image. -/
def reciprocal (limit : EndpointLimit) (precision : Precision) (input : Fact) : Result :=
  match input.raw with
  | .empty => .ready .empty
  | .bounds lower upper =>
      match strictlyPositiveLower limit lower with
      | .error cost => .resourceLimit cost
      | .ok true =>
          match inverseLower limit precision upper with
          | .error cost => .resourceLimit cost
          | .ok resultLower =>
              match inverseUpper limit precision lower with
              | .error cost => .resourceLimit cost
              | .ok resultUpper => normalize limit (.bounds resultLower resultUpper)
      | .ok false =>
          match strictlyNegativeUpper limit upper with
          | .error cost => .resourceLimit cost
          | .ok false => .inapplicable
          | .ok true =>
              match inverseLower limit precision upper with
              | .error cost => .resourceLimit cost
              | .ok resultLower =>
                  match inverseUpper limit precision lower with
                  | .error cost => .resourceLimit cost
                  | .ok resultUpper => normalize limit (.bounds resultLower resultUpper)

/-! ## Split and propagator fact domain -/

/-- Split `input` into `input ∩ (-∞, point]` and
`input ∩ (point, +∞)`.  The equal cut belongs only to the left child. -/
def split (limit : EndpointLimit) (input : Fact) (point : Dyadic) :
    Except WorkCost (Fact × Fact) :=
  if input.isEmpty then
    pure (.empty, .empty)
  else do
    endpointChecked limit point
    let leftCut ←
      match normalize limit (.bounds .unbounded (.finite point false)) with
      | .ready fact => pure fact
      | .resourceLimit cost => throw cost
      | .inapplicable => throw (.endpoint (EndpointCost.ofDyadic point))
    let rightCut ←
      match normalize limit (.bounds (.finite point true) .unbounded) with
      | .ready fact => pure fact
      | .resourceLimit cost => throw cost
      | .inapplicable => throw (.endpoint (EndpointCost.ofDyadic point))
    let left ←
      match intersect limit input leftCut with
      | .ready fact => pure fact
      | .resourceLimit cost => throw cost
      | .inapplicable => throw (.endpoint (EndpointCost.ofDyadic point))
    let right ←
      match intersect limit input rightCut with
      | .ready fact => pure fact
      | .resourceLimit cost => throw cost
      | .inapplicable => throw (.endpoint (EndpointCost.ofDyadic point))
    pure (left, right)

/-- Concrete domain adapter.  Its only possible malformed result would require
constructing a `Fact` with a false consistency proof. -/
def factDomain (limit : EndpointLimit) : FactDomain Fact where
  top _ := .whole
  narrow _ current candidate :=
    match intersect limit current candidate with
    | .inapplicable => .malformed 1
    | .resourceLimit cost => .resourceLimit (workMagnitude cost)
    | .ready result =>
        if result = current then .noChange
        else if result.isEmpty then .contradiction result
        else .improved result

/-- Error at the checked initial-fact boundary. -/
inductive StartError where
  | malformedFact (index : Nat)
  | emptyFact (index : Nat)
  | factResource (index : Nat) (cost : WorkCost)
  | engine (error : Propagator.StartError)
  deriving DecidableEq, Repr

def importInitialFacts (limit : EndpointLimit) :
    Nat -> List Raw -> Except StartError (List Fact)
  | _, [] => pure []
  | index, raw :: raws => do
      let fact ←
        match importRaw limit raw with
        | .malformed => throw (.malformedFact index)
        | .resourceLimit cost => throw (.factResource index cost)
        | .ready fact => pure fact
      if fact.isEmpty then throw (.emptyFact index)
      pure (fact :: (← importInitialFacts limit (index + 1) raws))

/-- Checked wrapper around `Engine.start`.  Raw initial facts must already be
canonical and nonempty; malformed cuts, empty cuts, and resource failures are
reported before the generic scheduler can observe them. -/
def start (endpointLimit : EndpointLimit) (program : Program)
    (rules : Array Registration) (rawFacts : Array Raw) (limits : Limits) :
    Except StartError (Engine Fact) := do
  -- Bound the raw-fact scan with the same early structural checks used by the
  -- generic engine.  In particular, a wrong-sized untrusted array is never
  -- converted to an unbounded intermediate list.
  if limits.maxOperations < program.operations.size then
    throw (.engine (.resourceLimit .operations))
  if limits.maxNodes < program.nodes.size then
    throw (.engine (.resourceLimit .nodes))
  if rawFacts.size != program.nodes.size then
    throw (.engine .wrongFactCount)
  let facts ← importInitialFacts endpointLimit 0 rawFacts.toList
  match Engine.start (factDomain endpointLimit) program rules facts.toArray limits with
  | .ok engine => pure engine
  | .error error => throw (.engine error)

end Hex.Interval.Experiment.DyadicInterval
