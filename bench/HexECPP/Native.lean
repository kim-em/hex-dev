/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Search
import Lean.Data.Json

/-! Serial native ECPP campaign output, retaining every verdict and raw data.
No certificate, trace, factorization, curve or point is an input. -/

open Hex.ECPP

private def terminal : Cert → Hex.Nat.PrimeCert
  | .base c => c
  | .step _ _ _ _ _ _ _ c => terminal c

private def steps : Cert → Nat
  | .base _ => 0
  | .step _ _ _ _ _ _ _ c => 1 + steps c

private def stats (s : SearchStats) : Lean.Json := Lean.Json.mkObj [
  ("candidates", toJson s.candidates), ("roots", toJson s.roots),
  ("nonresidues", toJson s.nonresidues), ("points", toJson s.points),
  ("factorWork", toJson s.factorWork), ("scalarWork", toJson s.scalarWork),
  ("backtracks", toJson s.backtracks)]
where toJson := Lean.toJson

@[noinline] private def searchIO (n seed : Nat) : IO SearchResult :=
  pure (produce n seed)

@[noinline] private def convertIO (source : String) (leaf : Hex.Nat.PrimeCert) :
    IO (Except ImportError Cert) := pure (convertText defaultImportBudget source leaf)

@[noinline] private def checkIO (n : Nat) (c : Cert) : IO Bool := pure (checkAt n c)

def main (args : List String) : IO UInt32 := do
  let [n, seed] := args | throw <| IO.userError "usage: hexecpp_native SUBJECT SEED"
  let some n := n.toNat? | throw <| IO.userError "invalid subject"
  let some seed := seed.toNat? | throw <| IO.userError "invalid seed"
  let start ← IO.monoNanosNow
  let result ← searchIO n seed
  let elapsed := (← IO.monoNanosNow) - start
  let common := [("subject", Lean.toJson n), ("seed", Lean.toJson seed),
    ("search_ns", Lean.toJson elapsed), ("stats", stats result.state.stats),
    ("rand", Lean.toJson result.state.rand.state.toNat)]
  let fields ← match result.result with
    | .error e => pure [("verdict", Lean.toJson "exhausted"),
        ("resource", Lean.toJson (reprStr e.resource)), ("unresolved", Lean.toJson e.subject)]
    | .ok c => do
      let source := frozenRows c
      let leaf := terminal c
      let start ← IO.monoNanosNow
      let converted ← convertIO source leaf
      let convertTime := (← IO.monoNanosNow) - start
      let start ← IO.monoNanosNow
      let valid ← checkIO n c
      let checkTime := (← IO.monoNanosNow) - start
      pure [("verdict", Lean.toJson "success"), ("checked", Lean.toJson valid),
        ("steps", Lean.toJson (steps c)), ("data_bits", Lean.toJson (certBits c)),
        ("rows", Lean.toJson source), ("leaf", Lean.toJson (reprStr leaf)),
        ("expanded", Lean.toJson (reprStr c)),
        ("conversion_ns", Lean.toJson convertTime), ("check_ns", Lean.toJson checkTime),
        ("converted", Lean.toJson (converted.toOption.any (checkAt n)))]
  IO.println <| (Lean.Json.mkObj (common ++ fields)).compress
  return 0
