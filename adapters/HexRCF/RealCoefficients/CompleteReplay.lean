/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootTableCodec
public import HexRCF.RealCoefficients.CellFootprint
public section
namespace Hex.RCF.RealCoefficients.CompleteReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Independently restore the full carrier root table and all its cells.
Original guards are checked by the root reader before any graph decoding. -/
@[expose] def read (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (rootGraph cells : Codec.Json) :
    Except Replay.Error (Σ roots : RootReplay.Result p .negInf .posInf,
      CellReplay.Evidence roots values formula) := do
  let roots ← RootReplay.read value guards p .negInf .posInf rootGraph
  let rows ← CellRead.read value guards roots values formula cells
  return ⟨roots,rows⟩

/-- Check the original radical identities and strict quantified fold after
both independent readers. Every failure and false verdict is retained. -/
@[expose] def check (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) : Except Replay.Error Bool := do
  let restored ← read value guards cert.core values formula rootGraph cells
  CellReplay.check values formula guards cert restored.1 restored.2 quantifier

/-- Acceptance retains the actual independently decoded table and cells and
the canonical typed check result. It assumes no origin for the supplied data. -/
theorem check_parts (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) (verdict : Bool)
    (accepted : check value values formula guards cert quantifier rootGraph cells = .ok verdict) :
    ∃ restored, read value guards cert.core values formula rootGraph cells = .ok restored ∧
      CellReplay.check values formula guards cert restored.1 restored.2 quantifier = .ok verdict := by
  unfold check at accepted
  cases decoded : read value guards cert.core values formula rootGraph cells with
  | error cause => simp [decoded, bind, Except.bind] at accepted
  | ok restored =>
    exact ⟨restored,rfl,by simpa only [decoded,bind,Except.bind] using accepted⟩

/-- Accepted arbitrary literal packets preserve every original divisor under
the actual ordinary-real model. -/
theorem check_domains (model : Model parent ℝ) (value : ValueCodec parent.Value)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (quantifier : RealFormula.Quantifier) (rootGraph cells : Codec.Json) (verdict : Bool)
    (accepted : check value values formula guards cert quantifier rootGraph cells = .ok verdict) :
    ∀ d ∈ guards, model.value d ≠ 0 := by
  obtain ⟨restored,_,checked⟩ := check_parts value values formula guards cert quantifier
    rootGraph cells verdict accepted
  exact CellReplay.check_domains model values formula guards cert restored.1 restored.2
    quantifier verdict checked

/-- Acceptance of arbitrary supplied root/cell packets proves the shared
sentence at the original fixed coefficient interpretation. -/
theorem check_sound (model : Model parent ℝ) (value : ValueCodec parent.Value)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (quantifier : RealFormula.Quantifier) (rootGraph cells : Codec.Json)
    (accepted : check value values formula guards cert quantifier rootGraph cells = .ok true) :
    (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
      (fun i => model.value (values i)) := by
  obtain ⟨restored,_,checked⟩ := check_parts value values formula guards cert quantifier
    rootGraph cells true accepted
  exact CellReplay.check_sound model values formula guards cert restored.1 restored.2 quantifier checked

variable [Hashable parent.Value] [Hashable Signature]
variable {p : DensePoly parent.Value} {roots : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {formula : RealFormula.QF (n+1)}

/-- Every stored scalar in the root graph and complete-cell payload, in that
order. Source authentication and intermediate arithmetic records are separate. -/
@[expose] def coefficients (data : CellReplay.Evidence roots values formula) : List parent.Value :=
  Codec.Coefficients.graph (Dag.encode roots.replay) ++ CellFootprint.coefficients data

/-- Finite complete-packet coverage restores both exact dependent components.
No root-producer success or descriptor-reader success is assumed. -/
theorem read_covered (value : ValueCodec parent.Value)
    (data : CellReplay.Evidence roots values formula) (guards : List parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0) (covered : value.Covers (coefficients data)) :
    read value guards p values formula
      (Codec.graph value Signature.codec (Dag.encode roots.replay))
      (CellEncode.packet value data) = .ok ⟨roots,data⟩ := by
  have parts := (ValueCodec.covers_append value _ _).mp covered
  simp only [read, RootTableCodec.read_roots value roots guards guarded parts.1,
    CellFootprint.read_packet value data guards guarded parts.2,
    bind, Except.bind, pure, Except.pure]

/-- Independent complete-packet checking agrees exactly with the checked typed
fold, including its false result and radical-binding failures. -/
theorem check_covered (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : CellReplay.Evidence roots values formula) (quantifier : RealFormula.Quantifier)
    (guarded : ∀ d ∈ guards, d ≠ 0) (covered : value.Covers (coefficients data)) :
    check value values formula guards cert quantifier
      (Codec.graph value Signature.codec (Dag.encode roots.replay)) (CellEncode.packet value data) =
        CellReplay.check values formula guards cert roots data quantifier := by
  simp only [check, read_covered value data guards guarded covered, bind, Except.bind]

end Hex.RCF.RealCoefficients.CompleteReplay
