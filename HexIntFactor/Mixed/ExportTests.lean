/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Mixed.Export
import HexIntFactor.Mixed.Frozen.Small

/-!
Mixed source conformance.
Oracle: kernel acceptance and fresh ordinary replay in check_intfactor_pari.py.
Mode: internal
Covered operations: exact suggestions, bounded constructor admission, editor gating.
Edge cases: residual overlap, rejected subjects, executable data and exclusive exports.
-/

open Hex.Nat.Mixed

/--
info: Try this:
module

public import HexIntFactor.Mixed.Replay

public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 65536

@[expose] def certificate : Hex.Nat.Mixed.Factorization :=
  ⟨34, [⟨2, 1, (Hex.Nat.Mixed.Evidence.legacy (Hex.Nat.PrimeCert.small 2))⟩, ⟨17, 1, (Hex.Nat.Mixed.Evidence.ecpp (Hex.ECPP.Cert.step 17 2 3 3 6 6 [10, 13, 3, 13] (Hex.ECPP.Cert.base (Hex.Nat.PrimeCert.small 11))))⟩]⟩

@[expose] def certificate_checked : Hex.Nat.Mixed.CheckedFactorization 34 :=
  ⟨certificate, rfl, by decide +kernel⟩
-/
#guard_msgs in
#int_factor_mixed for 34 using
  ⟨34, [(2, 1, some (.legacy (.small 2))), (17, 1, some (.ecpp Frozen.ecpp17))]⟩

/--
info: Try this:
module

public import HexIntFactor.Mixed.Replay

public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 65536

@[expose] def certificate : Hex.Nat.Mixed.PartialFactorization :=
  ⟨578, [⟨2, 1, (Hex.Nat.Mixed.Evidence.legacy (Hex.Nat.PrimeCert.small 2))⟩, ⟨17, 1, (Hex.Nat.Mixed.Evidence.ecpp (Hex.ECPP.Cert.step 17 2 3 3 6 6 [10, 13, 3, 13] (Hex.ECPP.Cert.base (Hex.Nat.PrimeCert.small 11))))⟩], 17⟩

@[expose] def certificate_checked : Hex.Nat.Mixed.CheckedPartialFactorization 578 :=
  ⟨certificate, rfl, by decide +kernel⟩
-/
#guard_msgs in
#int_factor_mixed for 578 using
  ⟨578, [(2, 1, some (.legacy (.small 2))), (17, 1, some (.ecpp Frozen.ecpp17))]⟩

/-- error: mixed factor: proposal rejected (Hex.Nat.ImportError.subjectMismatch) -/
#guard_msgs in
#int_factor_mixed for 35 using ⟨34, []⟩

/-- error: mixed factor: ECPP bits must be 256 or 512 -/
#guard_msgs in
#int_factor_mixed (ecpp := 1024) for 1 using ⟨1, []⟩

opaque hidden : FactorProposal := ⟨1, []⟩
/-- error: ecpp: `hidden` is not an exposed data definition -/
#guard_msgs in
#int_factor_mixed for 1 using hidden

/-- error: ecpp: in exposed `HPow.hPow`: ecpp: certificate must be constructor data; got fun α β {γ} [self : HPow α β γ] => self.1 -/
#guard_msgs in
#int_factor_mixed for (2^4097) using ⟨1, []⟩

/-- info: Mixed factor production runs only in batch builds. Run `lake build +HexIntFactor.Mixed.ExportTests`, then remove the generation command. -/
#guard_msgs in
set_option Elab.inServer true in
#int_factor_mixed (method := pari) (ecpp := 512) for 34

/-- info: Mixed factor production runs only in batch builds. Run `lake build +HexIntFactor.Mixed.ExportTests`, then remove the generation command. -/
#guard_msgs in
set_option Elab.inServer true in
#int_factor_mixed_export HexIntFactor.Mixed.EditorMustNotExist cert for 34 using ⟨34, []⟩

/-- error: mixed factor export: source byte limit -/
#guard_msgs in
run_cmd do
  discard <| Lean.Elab.Command.liftTermElabM <| FactorExport.source `certificate 34
    (.complete Frozen.small_checked) { maxSourceBytes := 1 }

/-- error: mixed factor export: proof budgets must be positive -/
#guard_msgs in
run_cmd do
  discard <| Lean.Elab.Command.liftTermElabM <| FactorExport.source `certificate 34
    (.complete Frozen.small_checked) { maxHeartbeats := 0 }

/-- error: ecpp: certificate syntax exceeds 1 nodes -/
#guard_msgs in
run_cmd do
  discard <| Lean.Elab.Command.liftTermElabM <| FactorExport.source `certificate 34
    (.complete Frozen.small_checked) { maxSyntaxNodes := 1 }

private unsafe def proposalImpl : FactorProposal := ⟨1, []⟩

@[implemented_by proposalImpl]
def overriddenProposal : FactorProposal := ⟨1, []⟩

/-- error: ecpp: `overriddenProposal` has a compiled implementation; use constructor data -/
#guard_msgs in
#int_factor_mixed for 1 using overriddenProposal
