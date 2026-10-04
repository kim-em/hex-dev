/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Construction
public import Lean.Data.Json

public section

/-! The full current construction profile, including the registered ECM
retry. This is the same default schedule as Hex.PrimalityTactic.construct.
Inputs use the ordinary construction seed (the subject). -/

open Hex.Nat

@[noinline] private def run (n : Nat) : IO Lean.Json := do
  let first := Construction.runTraced n (Hex.Rand.ofSeed n) constructionBudget
  let (result, coreAttempts, retry) :
      Except Construction.Failure (Internal.PrimeCertSuccess n) × Nat × Bool := match first with
    | .ok result => (.ok result, result.attempts, false)
    | .error f =>
      if Construction.retryable n constructionBudget f then
        (Construction.retry n constructionBudget f ecmConstructionFactor, f.attempts, true)
      else (.error f, f.attempts, false)
  let common := [("core_attempts", Lean.toJson coreAttempts), ("ecm_retry", Lean.toJson retry),
    ("budget", Lean.toJson (reprStr constructionBudget))]
  return Lean.Json.mkObj <| common ++ match result with
    | .ok result => [("verdict", Lean.toJson "success"), ("attempts", Lean.toJson result.attempts),
        ("checked", Lean.toJson (result.cert.raw.subject == n && checkPrime result.cert.raw))]
    | .error f => [("verdict", Lean.toJson (reprStr f.stop)), ("attempts", Lean.toJson f.attempts),
        ("unresolved", Lean.toJson (f.obligation.getD n))]

def main (args : List String) : IO UInt32 := do
  let [subject] := args | throw <| IO.userError "usage: hexecpp_compare SUBJECT"
  let some n := subject.toNat? | throw <| IO.userError "invalid subject"
  let start ← IO.monoNanosNow
  let result ← run n
  let elapsed := (← IO.monoNanosNow) - start
  IO.println <| (Lean.Json.mkObj [("subject", Lean.toJson n),
    ("construction_ns", Lean.toJson elapsed), ("construction", result)]).compress
  return 0
