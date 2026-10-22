/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Search
public import Lean.Data.Json

public section

/-! Serial native ECPP campaign output, retaining every verdict and raw data.
No certificate, trace, factorization, curve or point is an input. -/

open Hex.ECPP

private def terminal : Cert → Hex.Nat.PrimeCert
  | .base c => c
  | .step _ _ _ _ _ _ _ c => terminal c

private def steps : Cert → Nat
  | .base _ => 0
  | .step _ _ _ _ _ _ _ c => 1 + steps c

private def primeNodes : Nat → Hex.Nat.PrimeCert → Option Nat
  | 0, _ => none
  | _ + 1, .small _ => some 1
  | fuel + 1, .pock _ fs
  | fuel + 1, .pock3 _ _ _ _ fs
  | fuel + 1, .pock3Sieve _ _ _ _ _ fs => do
      let nodes ← fs.mapM fun (_, _, child) => primeNodes fuel child
      pure (1 + nodes.sum)

private def descent : Cert → List (Nat × Nat)
  | .base _ => []
  | .step n _ _ _ _ _ _ child =>
      (HexArith.bitLength n, HexArith.bitLength child.subject) :: descent child

private def stats (s : SearchStats) : Lean.Json := Lean.Json.mkObj [
  ("candidates", toJson s.candidates), ("roots", toJson s.roots),
  ("nonresidues", toJson s.nonresidues), ("points", toJson s.points),
  ("factorWork", toJson s.factorWork), ("scalarWork", toJson s.scalarWork),
  ("backtracks", toJson s.backtracks),
  ("terminalCalls", toJson s.terminalCalls), ("terminalSuccesses", toJson s.terminalSuccesses),
  ("terminalBitRejects", toJson s.terminalBitRejects),
  ("terminalObligation", Lean.toJson s.terminalObligation),
  ("norms", toJson s.norms), ("orders", toJson s.orders),
  ("largeFactors", toJson s.largeFactors), ("proposals", toJson s.proposals),
  ("outputRejects", toJson s.outputRejects), ("outputBits", Lean.toJson s.outputBits),
  ("polynomialWork", toJson s.polynomialWork), ("polynomialRoots", toJson s.polynomialRoots),
  ("lastRetry", Lean.toJson (s.lastRetry.map (fun e => (e.subject, reprStr e.resource)))),
  ("unresolved", Lean.toJson (s.unresolved.map (fun e => (e.subject, reprStr e.resource))))]
where toJson := Lean.toJson

@[noinline] private def searchIO (n seed : Nat) (budget : SearchBudget) : IO SearchResult :=
  pure (produce n seed budget)

@[noinline] private def convertIO (source : String) (leaf : Hex.Nat.PrimeCert) :
    IO (Except ImportError Cert) := pure (convertText defaultImportBudget source leaf)

@[noinline] private def checkIO (n : Nat) (c : Cert) : IO Bool := pure (checkAt n c)

@[noinline] private def outputIO (c : Cert) : IO (String × Hex.Nat.PrimeCert × String × String) :=
  let leaf := terminal c
  pure (frozenRows c, leaf, reprStr leaf, reprStr c)

def main (args : List String) : IO UInt32 := do
  let (n, seed, budget) ← match args with
    | [n, seed] => pure (n, seed, ({} : SearchBudget))
    | [n, seed, "diagnose512"] => pure (n, seed, { maxBits := 512 })
    | [n, seed, "diagnose512-public"] =>
        pure (n, seed, { maxBits := 512, maxDepth := 20 })
    | [n, seed, "native512"] => pure (n, seed, native512Budget)
    | [n, seed, "native512-public"] => pure (n, seed, public512Budget)
    | [n, seed, depth, candidates] =>
        let some depth := depth.toNat? | throw <| IO.userError "invalid depth"
        let some candidates := candidates.toNat? | throw <| IO.userError "invalid candidates"
        pure (n, seed, { maxDepth := depth, maxCandidates := candidates })
    | _ => throw <| IO.userError (
        "usage: hexecpp_native SUBJECT SEED [DEPTH CANDIDATES | diagnose512 | diagnose512-public | native512 | native512-public]")
  let some n := n.toNat? | throw <| IO.userError "invalid subject"
  let some seed := seed.toNat? | throw <| IO.userError "invalid seed"
  let start ← IO.monoNanosNow
  let result ← searchIO n seed budget
  let elapsed := (← IO.monoNanosNow) - start
  let common := [("subject", Lean.toJson n), ("seed", Lean.toJson seed),
    ("search_ns", Lean.toJson elapsed), ("budget", Lean.toJson (reprStr budget)), ("stats", stats result.state.stats),
    ("rand", Lean.toJson result.state.rand.state.toNat)]
  let fields ← match result.result with
    | .error e => pure [("verdict", Lean.toJson "exhausted"),
        ("resource", Lean.toJson (reprStr e.resource)), ("unresolved", Lean.toJson e.subject)]
    | .ok c => do
      let start ← IO.monoNanosNow
      let (source, leaf, leafText, expanded) ← outputIO c
      let outputTime := (← IO.monoNanosNow) - start
      let start ← IO.monoNanosNow
      let converted ← convertIO source leaf
      let convertTime := (← IO.monoNanosNow) - start
      let start ← IO.monoNanosNow
      let valid ← checkIO n c
      let checkTime := (← IO.monoNanosNow) - start
      pure [("verdict", Lean.toJson "success"), ("checked", Lean.toJson valid),
        ("steps", Lean.toJson (steps c)), ("data_bits", Lean.toJson
          (certBitsAt ((budget.terminal.getD leafBudget).maxDepth + 1) c)),
        ("descent_bits", Lean.toJson (descent c)),
        ("terminal_nodes", Lean.toJson (primeNodes ((budget.terminal.getD leafBudget).maxDepth + 1) leaf)),
        ("rows", Lean.toJson source), ("leaf", Lean.toJson leafText),
        ("expanded", Lean.toJson expanded),
        ("output_render_ns", Lean.toJson outputTime),
        ("row_bytes", Lean.toJson source.utf8ByteSize),
        ("expanded_bytes", Lean.toJson expanded.utf8ByteSize),
        ("conversion_ns", Lean.toJson convertTime), ("check_ns", Lean.toJson checkTime),
        ("converted", Lean.toJson (converted.toOption.any (checkAt n)))]
  IO.println <| (Lean.Json.mkObj (common ++ fields)).compress
  return 0
