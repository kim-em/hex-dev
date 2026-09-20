/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.Construction
import Lean

/-! Shared output and construction boundaries for Pollard p−1 measurements.
Native benches place serialization outside their LeanBench timing boundary.
Fresh-module probes use the same constructor without an in-process clock. -/

namespace Hex.PMinusOneMeasure

open Hex.Nat Lean

def outcome : PMinusOneResult → String
  | .noFactor => "noFactor"
  | .whole => "whole"
  | .factor _ => "factor"

def eventJson (e : PMinusOne.Event) : Json := Json.mkObj [
  ("subject", toJson e.subject), ("base", toJson e.base),
  ("requestedB1", toJson e.requestedB1), ("effectiveB1", toJson e.effectiveB1),
  ("requestedB2", toJson e.requestedB2), ("effectiveB2", toJson e.effectiveB2),
  ("outcome", toJson (outcome e.outcome)), ("reason", toJson e.reason),
  ("factor", toJson (match e.outcome with | .factor d => some d | _ => none)),
  ("candidates", toJson e.candidates), ("giantAdvances", toJson e.giantAdvances),
  ("multiplications", toJson e.multiplications), ("setupGcds", toJson e.setupGcds),
  ("batchGcds", toJson e.batchGcds), ("recoveryGcds", toJson e.recoveryGcds),
  ("batches", toJson (e.batches.map fun b => Json.mkObj [
    ("first", toJson b.firstPrime), ("last", toJson b.lastPrime),
    ("length", toJson b.length), ("gcd", toJson b.gcd),
    ("recovery", toJson b.recovery)]))]

def factorEventJson : FactorEvent → Json
  | .pMinusOne e => eventJson e
  | .route name fields => Json.mkObj (("route", toJson name) ::
      fields.map (fun (k, v) => (k, toJson v)))

structure Result where
  checked : Bool := false
  outcome : String
  value : Nat := 0
  attempts : Nat := 0
  rand : String := ""
  events : List FactorEvent := []

def Result.json (r : Result) : Json := Json.mkObj [
  ("checked", toJson r.checked), ("outcome", toJson r.outcome),
  ("value", toJson r.value), ("attempts", toJson r.attempts),
  ("rand", toJson r.rand), ("events", toJson (r.events.map factorEventJson))]

def fromRun (r : PMinusOne.Run) : Result := {
  outcome := outcome r.result
  value := match r.result with | .factor d => d | _ => 0
  attempts := r.attempts, rand := reprStr r.rand
  events := r.events.map .pMinusOne }

/-- A single native/interpreted boundary used by both policy arms. -/
@[noinline] def construct (n seed : Nat) (enabled : Bool) (maxBits : Nat := 512) : Result :=
  let budget := { constructionBudget with
    maxBits := maxBits
    factor := { constructionBudget.factor with pMinusOneStage2 := enabled } }
  match Construction.run n (Hex.Rand.ofSeed seed) budget with
  | .ok r =>
      { checked := true, outcome := "certificate", value := r.cert.raw.subject
        attempts := r.attempts, rand := reprStr r.rand, events := r.events }
  | .error r =>
      { outcome := match r.stop with | .composite => "composite" | .exhausted => "exhausted"
        attempts := r.attempts
        rand := reprStr r.rand, events := r.events }

end Hex.PMinusOneMeasure
