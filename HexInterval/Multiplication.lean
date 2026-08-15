/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Interval

public section

/-!
# Resource-checked interval multiplication

The executable core enumerates the four products of extended endpoint cuts,
omitting the undefined formal products `0 * ±∞`, and adds an attained zero
candidate exactly when either nonempty factor contains zero. Every finite
endpoint is admitted before sign inspection, all finite corner products pass
`Arithmetic.preflightMul` before the first mantissa multiplication, and all
finite candidate endpoints are admitted before their alignment comparisons
and extremum selection.
-/

namespace Hex.Interval

namespace Raw.Mul

/-- An endpoint viewed in the extended real line. -/
inductive Edge where
  | negInf
  | finite (value : Dyadic) (strict : Bool)
  | posInf
  deriving DecidableEq

/-- A product-extremum candidate. Infinite candidates are never attained;
finite candidates remember whether their endpoint product is attained. -/
inductive Candidate where
  | negInf
  | finite (value : Dyadic) (attained : Bool)
  | posInf
  deriving DecidableEq

/-- Lower cut as an extended endpoint. -/
@[expose] def lowerEdge : Lower → Edge
  | .unbounded => .negInf
  | .finite value strict => .finite value strict

/-- Upper cut as an extended endpoint. -/
@[expose] def upperEdge : Upper → Edge
  | .finite value strict => .finite value strict
  | .unbounded => .posInf

/-- Sign inspection after the caller has admitted comparison with zero. -/
@[expose] def signUnchecked (value : Dyadic) : Ordering :=
  if value < 0 then .lt else if value = 0 then .eq else .gt

/-- One extended corner product. Formal `0 * ±∞` contributes no corner;
zero attainment is handled independently from interval membership. -/
@[expose] def productUnchecked : Edge → Edge → Option Candidate
  | .finite left leftStrict, .finite right rightStrict =>
      some (.finite (left * right) (!leftStrict && !rightStrict))
  | .negInf, .negInf | .posInf, .posInf => some .posInf
  | .negInf, .posInf | .posInf, .negInf => some .negInf
  | .negInf, .finite value _ | .finite value _, .negInf =>
      match signUnchecked value with
      | .lt => some .posInf
      | .eq => none
      | .gt => some .negInf
  | .posInf, .finite value _ | .finite value _, .posInf =>
      match signUnchecked value with
      | .lt => some .negInf
      | .eq => none
      | .gt => some .posInf

/-- The four extended endpoint-pair recipes. -/
@[expose] def corners (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) : List (Edge × Edge) :=
  let ll := lowerEdge leftLower
  let lu := upperEdge leftUpper
  let rl := lowerEdge rightLower
  let ru := upperEdge rightUpper
  [(ll, rl), (ll, ru), (lu, rl), (lu, ru)]

/-- A lower cut permits zero after its finite comparison with zero is
admitted. -/
@[expose] def lowerAllowsZeroUnchecked : Lower → Bool
  | .unbounded => true
  | .finite value strict =>
      match signUnchecked value with
      | .lt => true
      | .eq => !strict
      | .gt => false

/-- An upper cut permits zero after its finite comparison with zero is
admitted. -/
@[expose] def upperAllowsZeroUnchecked : Upper → Bool
  | .unbounded => true
  | .finite value strict =>
      match signUnchecked value with
      | .lt => false
      | .eq => !strict
      | .gt => true

/-- Whether nonempty bounds contain zero. -/
@[expose] def containsZeroUnchecked (lower : Lower) (upper : Upper) : Bool :=
  lowerAllowsZeroUnchecked lower && upperAllowsZeroUnchecked upper

/-- Admit one finite source endpoint before sign inspection. Comparing a
dyadic with zero requires no exponent alignment, so a refusal here is an
endpoint diagnostic rather than a degenerate comparison diagnostic. -/
def preflightEdge (limit : EndpointLimit) : Edge → Except Arithmetic.Cost Unit
  | .negInf | .posInf => pure ()
  | .finite value _ =>
      let cost := EndpointCost.ofDyadic value
      if cost.allowed limit then pure () else throw (.endpoint cost)

/-- Admit every endpoint sign inspection before any product is formed. -/
def preflightEdges (limit : EndpointLimit) : List Edge → Except Arithmetic.Cost Unit
  | [] => pure ()
  | edge :: rest => do
      preflightEdge limit edge
      preflightEdges limit rest

/-- Admit one finite corner product without multiplying its mantissas. -/
def preflightProduct (limit : EndpointLimit) : Edge × Edge → Except Arithmetic.Cost Unit
  | (.finite left _, .finite right _) => do
      let _ ← Arithmetic.preflightMul limit left right
      pure ()
  | _ => pure ()

/-- Admit all finite corner products before the first one is evaluated. -/
def preflightProducts (limit : EndpointLimit) :
    List (Edge × Edge) → Except Arithmetic.Cost Unit
  | [] => pure ()
  | pair :: rest => do
      preflightProduct limit pair
      preflightProducts limit rest

/-- Evaluate already-admitted corner recipes. -/
@[expose] def evaluate : List (Edge × Edge) → List Candidate
  | [] => []
  | pair :: rest =>
      match productUnchecked pair.1 pair.2 with
      | none => evaluate rest
      | some candidate => candidate :: evaluate rest

/-- Admit one finite candidate endpoint after product growth has been
preflighted and before any candidate comparison. -/
def preflightCandidate (limit : EndpointLimit) : Candidate → Except Arithmetic.Cost Unit
  | .negInf | .posInf => pure ()
  | .finite value _ =>
      let cost := EndpointCost.ofDyadic value
      if cost.allowed limit then pure () else throw (.endpoint cost)

/-- Admit every retained candidate endpoint before comparison. -/
def preflightCandidates (limit : EndpointLimit) :
    List Candidate → Except Arithmetic.Cost Unit
  | [] => pure ()
  | candidate :: rest => do
      preflightCandidate limit candidate
      preflightCandidates limit rest

/-- Admit one exact comparison between finite, already-bounded candidates. -/
def preflightCompare (limit : EndpointLimit) : Candidate → Candidate →
    Except Arithmetic.Cost Unit
  | .finite left _, .finite right _ =>
      let cost := CompareCost.ofDyadic left right
      if cost.alignmentShift ≤ limit.maxAlignmentShift then
        pure ()
      else
        throw (.comparison cost)
  | _, _ => pure ()

/-- Admit all pairwise finite comparisons before extremum selection. -/
def preflightComparisons (limit : EndpointLimit) :
    List Candidate → Except Arithmetic.Cost Unit
  | [] => pure ()
  | candidate :: rest => do
      for other in rest do
        preflightCompare limit candidate other
      preflightComparisons limit rest

/-- Select the smaller already-admitted candidate, combining attainment at a
tied finite value. -/
@[expose] def minUnchecked : Candidate → Candidate → Candidate
  | .negInf, _ | _, .negInf => .negInf
  | .posInf, candidate | candidate, .posInf => candidate
  | left@(.finite leftValue leftAttained), right@(.finite rightValue rightAttained) =>
      if leftValue < rightValue then left
      else if leftValue = rightValue then
        .finite leftValue (leftAttained || rightAttained)
      else right

/-- Select the larger already-admitted candidate, combining attainment at a
tied finite value. -/
@[expose] def maxUnchecked : Candidate → Candidate → Candidate
  | .posInf, _ | _, .posInf => .posInf
  | .negInf, candidate | candidate, .negInf => candidate
  | left@(.finite leftValue leftAttained), right@(.finite rightValue rightAttained) =>
      if leftValue < rightValue then right
      else if leftValue = rightValue then
        .finite leftValue (leftAttained || rightAttained)
      else left

/-- Minimum of a nonempty candidate list. -/
@[expose] def minimum : Candidate → List Candidate → Candidate
  | candidate, [] => candidate
  | candidate, next :: rest => minimum (minUnchecked candidate next) rest

/-- Maximum of a nonempty candidate list. -/
@[expose] def maximum : Candidate → List Candidate → Candidate
  | candidate, [] => candidate
  | candidate, next :: rest => maximum (maxUnchecked candidate next) rest

/-- Convert the selected minimum to a lower cut. -/
@[expose] def lowerCut : Candidate → Lower
  | .negInf => .unbounded
  | .finite value attained => .finite value (!attained)
  | .posInf => .unbounded

/-- Convert the selected maximum to an upper cut. -/
@[expose] def upperCut : Candidate → Upper
  | .negInf => .unbounded
  | .finite value attained => .finite value (!attained)
  | .posInf => .unbounded

/-- Add the attained-zero candidate, when justified, to an already evaluated
corner list. -/
@[expose] def withZeroUnchecked (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper)
    (cornerCandidates : List Candidate) : List Candidate :=
  if containsZeroUnchecked leftLower leftUpper ||
      containsZeroUnchecked rightLower rightUpper then
    .finite 0 true :: cornerCandidates
  else
    cornerCandidates

/-- Candidate list for two nonempty raw bounds. -/
@[expose] def candidatesUnchecked (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) : List Candidate :=
  withZeroUnchecked leftLower leftUpper rightLower rightUpper
    (evaluate (corners leftLower leftUpper rightLower rightUpper))

/-- Convert a candidate list to its enclosing raw cuts. The empty fallback is
unreachable for canonical nonempty interval inputs, but keeps this decoder
helper total on arbitrary raw data. -/
@[expose] def result : List Candidate → Raw
  | [] => .empty
  | first :: rest =>
      .bounds (lowerCut (minimum first rest)) (upperCut (maximum first rest))

end Raw.Mul

namespace Raw

/-- Exact raw multiplication candidate without resource checks. Call
`mulChecked` at untrusted boundaries. -/
@[expose] def mulUnchecked : Raw → Raw → Raw
  | .empty, _ | _, .empty => .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      Mul.result
        (Mul.candidatesUnchecked leftLower leftUpper rightLower rightUpper)

/-- Compute exact multiplication cuts with preflighted source endpoints,
product growth, retained candidates, and candidate ordering. Empty is
absorbing. This raw boundary accepts arbitrary cut data; the supported
`mulWithin` entry point supplies canonical public inputs and checks the final
result. -/
def mulChecked (limit : EndpointLimit) : Raw → Raw → Except Arithmetic.Cost Raw
  | .empty, _ | _, .empty => pure .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper => do
      let recipes := Mul.corners leftLower leftUpper rightLower rightUpper
      Mul.preflightEdges limit
        [Mul.lowerEdge leftLower, Mul.upperEdge leftUpper,
          Mul.lowerEdge rightLower, Mul.upperEdge rightUpper]
      Mul.preflightProducts limit recipes
      let cornerCandidates := Mul.evaluate recipes
      let candidates := Mul.withZeroUnchecked leftLower leftUpper
        rightLower rightUpper cornerCandidates
      Mul.preflightCandidates limit candidates
      Mul.preflightComparisons limit candidates
      pure (Mul.result candidates)

/-- Every successful checked raw computation returns the corresponding exact
unchecked candidate. -/
theorem eq_mulUnchecked_of_mulChecked {limit : EndpointLimit} {left right raw : Raw}
    (checked : mulChecked limit left right = .ok raw) :
    raw = mulUnchecked left right := by
  cases left with
  | empty =>
      change Except.ok .empty = Except.ok raw at checked
      cases checked
      rfl
  | bounds leftLower leftUpper =>
      cases right with
      | empty =>
          change Except.ok .empty = Except.ok raw at checked
          cases checked
          rfl
      | bounds rightLower rightUpper =>
          let edges :=
            [Mul.lowerEdge leftLower, Mul.upperEdge leftUpper,
              Mul.lowerEdge rightLower, Mul.upperEdge rightUpper]
          let recipes := Mul.corners leftLower leftUpper rightLower rightUpper
          let cornerCandidates := Mul.evaluate recipes
          let candidates := Mul.withZeroUnchecked leftLower leftUpper
            rightLower rightUpper cornerCandidates
          cases edgeCheck : Mul.preflightEdges limit edges with
          | error cost =>
              change (do
                Mul.preflightEdges limit edges
                Mul.preflightProducts limit recipes
                Mul.preflightCandidates limit candidates
                Mul.preflightComparisons limit candidates
                pure (Mul.result candidates)) = .ok raw at checked
              rw [edgeCheck] at checked
              contradiction
          | ok value =>
              cases value
              cases productCheck : Mul.preflightProducts limit recipes with
              | error cost =>
                  change (do
                    Mul.preflightEdges limit edges
                    Mul.preflightProducts limit recipes
                    Mul.preflightCandidates limit candidates
                    Mul.preflightComparisons limit candidates
                    pure (Mul.result candidates)) = .ok raw at checked
                  rw [edgeCheck, productCheck] at checked
                  contradiction
              | ok value =>
                  cases value
                  cases candidateCheck : Mul.preflightCandidates limit candidates with
                  | error cost =>
                      change (do
                        Mul.preflightEdges limit edges
                        Mul.preflightProducts limit recipes
                        Mul.preflightCandidates limit candidates
                        Mul.preflightComparisons limit candidates
                        pure (Mul.result candidates)) = .ok raw at checked
                      rw [edgeCheck, productCheck, candidateCheck] at checked
                      contradiction
                  | ok value =>
                      cases value
                      cases comparisonCheck : Mul.preflightComparisons limit candidates with
                      | error cost =>
                          change (do
                            Mul.preflightEdges limit edges
                            Mul.preflightProducts limit recipes
                            Mul.preflightCandidates limit candidates
                            Mul.preflightComparisons limit candidates
                            pure (Mul.result candidates)) = .ok raw at checked
                          rw [edgeCheck, productCheck, candidateCheck,
                            comparisonCheck] at checked
                          contradiction
                      | ok value =>
                          cases value
                          change (do
                            Mul.preflightEdges limit edges
                            Mul.preflightProducts limit recipes
                            Mul.preflightCandidates limit candidates
                            Mul.preflightComparisons limit candidates
                            pure (Mul.result candidates)) = .ok raw at checked
                          rw [edgeCheck, productCheck, candidateCheck,
                            comparisonCheck] at checked
                          cases checked
                          rfl

end Raw

/-- Resource-safe exact interval multiplication. Refusal is distinct from the
empty product. -/
def mulWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : Arithmetic.Result :=
  match Raw.mulChecked limit left.view right.view with
  | .error cost => .resourceLimit cost
  | .ok raw => Arithmetic.Result.ofBuild (ofRawWithin limit raw)

/-- A successful multiplication exposes the normalized exact raw candidate. -/
theorem view_mulWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : mulWithin limit left right = .ready result) :
    result.view = (Raw.mulUnchecked left.view right.view).normalizeUnchecked := by
  unfold mulWithin at checked
  split at checked
  · contradiction
  · next raw rawChecked =>
      have rawEq := Raw.eq_mulUnchecked_of_mulChecked rawChecked
      rw [rawEq] at checked
      generalize buildEq : ofRawWithin limit
          (Raw.mulUnchecked left.view right.view) = build at checked
      cases build with
      | ready interval =>
          simp only [Arithmetic.Result.ofBuild] at checked
          cases checked
          exact view_ofRawWithin_ready buildEq
      | resourceLimit cost =>
          simp only [Arithmetic.Result.ofBuild] at checked
          contradiction

end Hex.Interval
