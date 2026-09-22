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
  let arg := (← IO.getEnv "ECM_SUBJECT").getD "7"
  let some n := arg.toNat? | throwError "invalid subject"
  let mode := (← IO.getEnv "ECM_DISPATCH").getD "expression"
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
  let fields := [("nanos", toJson (stop-start)), ("heartbeats_raw", toJson (hbStop-hb)),
    ("dispatch_nanos", toJson (dispatchStop-dispatchStart))]
  let fields ← match result with
    | .error f => pure (fields ++ [("status", toJson (reprStr f.stop)),
        ("attempts", toJson f.attempts), ("rand", toJson (reprStr f.rand)), ("events", toJson (reprStr f.events))])
    | .ok s => do
      unless Hex.Nat.checkPrime s.cert.raw && s.cert.raw.subject == n do
        throwError "certificate check failed"
      pure (fields ++ [("status", toJson "ok"), ("attempts", toJson s.attempts),
        ("rand", toJson (reprStr s.rand)), ("events", toJson (reprStr s.events)), ("certificate", toJson (reprStr s.cert.raw))])
  logInfo m!"ECM_COST {(Json.mkObj fields).compress}"
