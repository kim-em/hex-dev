/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Export

/-!
Frozen-source conformance.
Oracle: acceptance proof checking precedes every rendered result; fresh
ordinary Replay modules and exclusive export are checked by check_intfactor_pari.py.
Mode: internal
Covered operations: FactorExport.source, validate, and both editor-gated commands.
Edge cases: exact complete/partial constructor text, source/proof allocations,
editor execution and no search on replay.
-/

open Lean Elab Command Hex.Nat

/--
info: module

public import HexIntFactor.Replay

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[expose] def certificate : Hex.Nat.Factorization :=
  ⟨12, [⟨2, (Hex.Nat.PrimeCert.small 2)⟩, ⟨1, (Hex.Nat.PrimeCert.small 3)⟩]⟩

@[expose] def certificate_checked : Hex.Nat.CheckedFactorization 12 :=
  ⟨certificate, rfl, by decide +kernel⟩
-/
#guard_msgs in
run_cmd do
  let .ok r := importFactors {} 12 ⟨12, [(2, 2, none), (3, 1, none)]⟩ (Hex.Rand.ofSeed 12)
    | throwError "import failed"
  let text ← liftTermElabM <| FactorExport.source `certificate 12 r.value
  logInfo text

/--
info: module

public import HexIntFactor.Replay

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[expose] def certificate : Hex.Nat.PartialFactorization :=
  ⟨12, [⟨2, (Hex.Nat.PrimeCert.small 2)⟩], 3⟩

@[expose] def certificate_checked : Hex.Nat.CheckedPartialFactorization 12 :=
  ⟨certificate, rfl, by decide +kernel⟩
-/
#guard_msgs in
run_cmd do
  let b : ImportBudget := { completion := { maxAttempts := 0 } }
  let .ok r := importFactors b 12 ⟨12, [(2, 2, some (.small 2)), (3, 1, none)]⟩ (Hex.Rand.ofSeed 12)
    | throwError "import failed"
  let text ← liftTermElabM <| FactorExport.source `certificate 12 r.value
  logInfo text

/-- error: factor export: source byte limit -/
#guard_msgs in
run_cmd do
  let .ok r := importFactors {} 1 ⟨1, []⟩ (Hex.Rand.ofSeed 1) | throwError "import failed"
  discard <| liftTermElabM <| FactorExport.source `certificate 1 r.value { maxSourceBytes := 1 }

/-- error: factor export: proof budgets must be positive -/
#guard_msgs in
run_cmd do
  let .ok r := importFactors {} 1 ⟨1, []⟩ (Hex.Rand.ofSeed 1) | throwError "import failed"
  discard <| liftTermElabM <| FactorExport.source `certificate 1 r.value { maxHeartbeats := 0 }

/-- info: Integer factor production runs only in batch builds. Run `lake build +HexIntFactor.ExportTests`, then remove the generation command. -/
#guard_msgs in
set_option Elab.inServer true in
#int_factor for 1000036000099

/-- info: Integer factor production runs only in batch builds. Run `lake build +HexIntFactor.ExportTests`, then remove the generation command. -/
#guard_msgs in
set_option Elab.inServer true in
#int_factor_export HexIntFactor.EditorMustNotExist cert for 1000036000099
