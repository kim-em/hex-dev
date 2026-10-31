/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Division
import HexGroebner.DivisionConformance

namespace Hex.Groebner.Certificate.DivisionTest

private def checked : Bool := Id.run do
  let .success result usage := divideWith context {} divisors input | return false
  if !valid context divisors input result.value then return false
  let .candidate produced production := Division.computeWith context {} divisors input | return false
  if produced.quotients != result.value.quotients || produced.remainder != result.value.remainder ||
      usage.work ≤ production.work then return false
  let mut replayExhausted := false
  for work in [0, production.work, usage.work - 1, usage.work] do
    match divideWith context { work } divisors input with
    | .success actual _ =>
      if actual.value.quotients != result.value.quotients ||
          actual.value.remainder != result.value.remainder then return false
    | .exhausted .work state =>
      replayExhausted := replayExhausted || state.stage.isRight
      match resumeDivideWith {} state with
      | .success actual final =>
        if actual.value.quotients != result.value.quotients ||
            actual.value.remainder != result.value.remainder || final.work < work then return false
      | _ => return false
    | _ => return false
  return replayExhausted

#guard checked
#guard match divideWith context {} #[[([0], 1)]] [] with
  | .invalid 0 _ => true
  | _ => false
#guard match Verification.verifyWith context {} divisors input ⟨#[[], [], []], input⟩ with
  | .rejected _ => true
  | _ => false
#guard match Verification.verifyWith context { work := 0 } divisors input ⟨#[[], [], []], input⟩ with
  | .exhausted .work _ => true
  | _ => false

end Hex.Groebner.Certificate.DivisionTest

/-- error: invalid {...} notation, constructor for `Hex.Groebner.Certificate.Division.State` is marked as private -/
#guard_msgs in
example (state : Hex.Groebner.Certificate.Division.State) :
    Hex.Groebner.Certificate.Division.State :=
  { state with context := { state.context with order := .lex } }
