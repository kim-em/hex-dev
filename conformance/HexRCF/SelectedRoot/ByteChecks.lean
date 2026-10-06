/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.ByteProofs

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.SelectedRootTests.ByteChecks
open Hex.RCF.SelectedRootTests Hex.RCF.SelectedRootTests.ByteProofs

def evaluateBytes (coefficients : Fin 1 → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF 2) (input : ByteArray) (limits : Codec.Limits := {}) :=
  SelectedFormula.checkBytesWith original coefficients guards formula context
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedNeg reduction reduction_eq facts)
    (Algebraic.Element.cachedSub reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedInv reduction reduction_eq facts)
    (Algebraic.Element.cachedDiv reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    (Algebraic.Element.cachedOne_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedNeg_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedSub_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedMul_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedInv_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedDiv_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts)
    valueCodec Tower.Signature.codec input limits

theorem evaluateBytes_eq (coefficients : Fin 1 → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF 2) (input : ByteArray) (limits : Codec.Limits) :
    evaluateBytes coefficients guards formula input limits =
      SelectedFormula.checkBytes original coefficients guards formula context
        valueCodec Tower.Signature.codec input limits := by
  unfold evaluateBytes
  erw [SelectedFormula.checkBytesWith_eq]

theorem falseAccepted : SelectedFormula.checkBytes original values [] Controls.falseSchema context
    valueCodec Tower.Signature.codec bytes {} = .ok (.ok false) := by
  have checked := Checks.falseAccepted
  erw [Row.evaluate_eq] at checked
  rw [SelectedFormula.bytes_decoded original values [] Controls.falseSchema context
    valueCodec Tower.Signature.codec bytes {} Controls.packet decoded, checked]

theorem counterexample : ∃ x : ℝ, ¬ Controls.falseSchema.toProp (Samples.valuation original values x) := by
  exact SelectedFormula.bytes_false original values [] Controls.falseSchema context
    valueCodec Tower.Signature.codec bytes {} falseAccepted

theorem wrongCoefficient : SelectedFormula.checkBytes original (fun _ => Controls.negative) [] schema context
    valueCodec Tower.Signature.codec bytes {} = .ok (.error .evidence) := by
  have checked := of_decide_eq_true Refusals.coefficientChecked
  change Row.evaluate RowCollect.facts (fun _ => Controls.negative) [] schema Controls.packet =
    .error Replay.Error.evidence at checked
  erw [Row.evaluate_eq] at checked
  rw [SelectedFormula.bytes_decoded original (fun _ => Controls.negative) [] schema context
    valueCodec Tower.Signature.codec bytes {} Controls.packet decoded, checked]

private def replace (j : Codec.Json) (index : Nat) (value : Codec.Json) :=
  Codec.Json.arr ((j.getArr?.toOption.getD #[]).set! index value)

def stale : ByteArray := (replace Literals.rowPacket 0 (Codec.Json.of (2 : Nat))).writeBytes

def crossed : ByteArray :=
  let fields := Literals.rowPacket.getArr?.toOption.getD #[]
  let binding := fields[1]?.getD (Codec.Json.arr #[])
  (replace Literals.rowPacket 1
    (replace binding 0 (Tower.Signature.codec.encode base.signature))).writeBytes

/-- info: Except.ok (Except.ok true) -/
#guard_msgs in
#eval evaluateBytes values [] schema bytes
/-- info: Except.ok (Except.ok false) -/
#guard_msgs in
#eval evaluateBytes values [] Controls.falseSchema bytes
/-- info: Except.error "invalid certificate JSON or UTF-8" -/
#guard_msgs in
#eval evaluateBytes values [] schema ByteArray.empty
/-- info: Except.error "certificate byte limit exceeded" -/
#guard_msgs in
#eval evaluateBytes values [] schema bytes {bytes := 0}
/-- info: Except.error "certificate nesting limit exceeded" -/
#guard_msgs in
#eval evaluateBytes values [] schema bytes {depth := 0}
/-- info: Except.error "integer token limit exceeded" -/
#guard_msgs in
#eval evaluateBytes values [] schema bytes {digits := 0}
/-- info: Except.ok (Except.error (Hex.RCF.RealCoefficients.Replay.Error.divisor)) -/
#guard_msgs in
#eval evaluateBytes values [Controls.zeroGuard] schema bytes {bytes := 0}
/-- info: Except.ok (Except.error (Hex.RCF.RealCoefficients.Replay.Error.evidence)) -/
#guard_msgs in
#eval evaluateBytes (fun _ => Controls.negative) [] schema bytes

/-- info: Except.error "unsupported sign evidence version" -/
#guard_msgs in
#eval evaluateBytes values [] schema stale
/-- info: Except.error "selected root binding mismatch" -/
#guard_msgs in
#eval evaluateBytes values [] schema crossed

run_meta do
  for name in #[``SelectedFormula.bytes_rejected, ``evaluateBytes_eq, ``falseAccepted,
    ``counterexample, ``wrongCoefficient] do
    Hex.RCF.checkAxioms name (Lean.mkConst name)
end Hex.RCF.SelectedRootTests.ByteChecks
