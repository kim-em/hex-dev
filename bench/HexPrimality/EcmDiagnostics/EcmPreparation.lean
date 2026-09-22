/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexIntFactor.EcmStage2
import all HexIntFactor.EcmStage2
public import Lean
public meta import HexIntFactor.EcmStage2
public section

open Lean Elab Hex.Nat.Ecm in
run_cmd do
  let bound ← IO.mkRef (32768, 524288)
  let (b₁, b₂) ← bound.get
  let hb ← IO.getNumHeartbeats
  let begin ← IO.monoNanosNow
  let some t := prepare b₁ b₂ | throwError "bounds rejected"
  let input ← IO.mkRef (Internal.prepareStage1 t)
  let t ← input.get
  let middle ← IO.monoNanosNow
  let input ← IO.mkRef (Internal.prepareStage2 t)
  let t ← input.get
  let stop ← IO.monoNanosNow
  let hbStop ← IO.getNumHeartbeats
  logInfo m!"ECM_PREPARATION {(Json.mkObj [
    ("stage1_nanos", toJson (middle-begin)), ("stage2_nanos", toJson (stop-middle)),
    ("heartbeats_raw", toJson (hbStop-hb)),
    ("powers", toJson (t.powers.getD []).length),
    ("primes", toJson (t.primes.getD []).length)]).compress}"
