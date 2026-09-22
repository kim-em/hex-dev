/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexIntFactor.Construction
public import Lean
public meta import HexIntFactor.Construction
public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 1024

open Lean Elab Hex.Nat in
run_cmd do
  let kind := (← IO.getEnv "ECM_CASE").getD "stage2"
  let (n, sigma, b₁, b₂) := match kind with
    | "stage1" => (51, 13, 5, 1024)
    | "stage2" => (1022117, 6, 16, 1024)
    | "failure" => (2^127-1, 6, 64, 8191)
    | _ => (1009, 6, 16, 1024)
  let hb ← IO.getNumHeartbeats
  let start ← IO.monoNanosNow
  let input ← IO.mkRef (Ecm.Internal.start n sigma b₁)
  let (first, saved) ← input.get
  let middle ← IO.monoNanosNow
  let input ← IO.mkRef (saved.map fun s => Ecm.Internal.stage2 s b₁ b₂)
  let second ← input.get
  let stop ← IO.monoNanosNow
  let hbStop ← IO.getNumHeartbeats
  let result := second.map (·.result) |>.getD first
  let attempts := if saved.isSome && b₂ > b₁ then 2 else 1
  unless Ecm.search n sigma b₁ b₂ 2 == (result, attempts) do throwError "search disagrees"
  unless Ecm.Internal.flush 1081 0 #[0,23] == (.factor 23,[1081,23]) do
    throwError "proper-factor gcd recovery failed"
  logInfo m!"ECM_COST {(Json.mkObj [
    ("result", toJson (reprStr result)), ("attempts", toJson attempts),
    ("stage1", toJson (reprStr first)), ("trace", toJson (reprStr second)),
    ("stage1_nanos", toJson (middle-start)), ("stage2_nanos", toJson (stop-middle)),
    ("nanos", toJson (stop-start)), ("heartbeats_raw", toJson (hbStop-hb)),
    ("candidates", toJson (second.map (·.candidates) |>.getD 0)),
    ("advances", toJson (second.map (·.advances) |>.getD 0)),
    ("batches", toJson (second.map (·.batches) |>.getD 0))]).compress}"
