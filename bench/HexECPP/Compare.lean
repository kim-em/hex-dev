/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Construction
import Lean.Data.Json

/-! The current registered construction profile: one pass with the interleaved
factor provider. Inputs use the ordinary construction seed (the subject).
Earlier retained reports used the core-first/fixed-curve retry policy. -/

open Hex.Nat

@[noinline] private def run (n : Nat) : IO Lean.Json := do
  let result := Construction.runTraced n (Hex.Rand.ofSeed n)
    constructionBudget interleavedConstructionFactor
  let common := [("policy", Lean.toJson "interleaved"),
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
