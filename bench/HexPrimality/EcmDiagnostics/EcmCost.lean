/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexPrimality.Elab
public import HexIntFactor.Construction
public meta import HexPrimality.Elab
public meta import HexIntFactor.Construction
public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 1024

-- Both dispatch forms select precisely the default production provider.
meta def namedProvider : Hex.Nat.FactorSearch := Hex.Nat.ecmFactorSearch

open Lean Meta Elab in
run_cmd Command.liftTermElabM do
  -- The CI smoke build is deliberately not a measurement record.
  let arg? ← IO.getEnv "ECM_SUBJECT"
  let arg := arg?.getD "7"
  let some n := arg.toNat? | throwError "invalid subject"
  let mode := (← IO.getEnv "ECM_DISPATCH").getD "expression"
  unless mode == "name" || mode == "expression" do throwError "invalid dispatch"
  let dispatchStart ← IO.monoNanosNow
  let factor ← if mode == "name" then
      unsafe evalConst Hex.Nat.FactorSearch ``namedProvider
    else do
      let e ← Term.elabTermEnsuringType (← `(Hex.Nat.ecmFactorSearch))
        (mkConst ``Hex.Nat.FactorSearch)
      unsafe evalExpr Hex.Nat.FactorSearch (mkConst ``Hex.Nat.FactorSearch) e
  let dispatchStop ← IO.monoNanosNow
  let hb ← IO.getNumHeartbeats
  let start ← IO.monoNanosNow
  let cell ← IO.mkRef (Hex.Nat.Construction.run n (Hex.Rand.ofSeed n)
    Hex.Nat.constructionBudget factor)
  let result ← cell.get
  let stop ← IO.monoNanosNow
  let hbStop ← IO.getNumHeartbeats
  let fields := [("subject", toJson n), ("nanos", toJson (stop-start)), ("heartbeats_raw", toJson (hbStop-hb)),
    ("dispatch_nanos", toJson (dispatchStop-dispatchStart))]
  let fields ← match result with
    | .error f => pure (fields ++ [("status", toJson (reprStr f.stop)),
        ("attempts", toJson f.attempts), ("rand", toJson (reprStr f.rand)), ("events", toJson (reprStr f.events))])
    | .ok s => do
      unless Hex.Nat.checkPrime s.cert.raw && s.cert.raw.subject == n do
        throwError "certificate check failed"
      pure (fields ++ [("status", toJson "ok"), ("attempts", toJson s.attempts),
        ("rand", toJson (reprStr s.rand)), ("events", toJson (reprStr s.events)), ("certificate", toJson (reprStr s.cert.raw))])
  let tag := if arg?.isSome then "ECM_COST" else "ECM_SMOKE"
  logInfo m!"{tag} {(Json.mkObj fields).compress}"
