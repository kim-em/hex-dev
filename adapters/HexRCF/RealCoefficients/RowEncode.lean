/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RowOperations
public import HexSignDet.DagEncode
public import HexSignDet.Codec.Bytes
public section
namespace Hex.RCF.RealCoefficients.RowEncode
open Hex Hex.RealClosure Hex.SignDet
/-- Hash frozen codec bytes for the complete-cell producers and their progress proofs. -/
@[expose, instance_reducible] def hashable {α : Type} (codec : ValueCodec α) : Hashable α :=
  ⟨fun value => hash (codec.encode value).writeBytes⟩

variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [Hashable E] [Hashable Ctx] {sign : E → Int} {binding : Ctx}

/-- Freeze the existing checked joint row without invoking sign production. -/
@[expose] def packet (value : ValueCodec E) (ctx : ValueCodec Ctx)
    {root : Descriptor E Ctx sign binding} {queries : List (DensePoly E)}
    (signs : SelectedSigns root queries) : Codec.Json :=
  (Algebraic.SignEvidence.codec value ctx root.raw).encode
    (Algebraic.SignEvidence.ofSigns signs)

/-- Finite predecessor coverage suffices for the shared row reader to recover
its exact supplied checked data. No global codec law or native context
construction is needed. -/
theorem read_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Algebraic.Context E Ctx sign binding) (queries : List (DensePoly E))
    (signs : SelectedSigns context.root queries)
    (hv : value.Covers (Algebraic.SignEvidence.coefficients context.root.raw
      (Algebraic.SignEvidence.ofSigns signs)))
    (hc : ctx.Covers (Algebraic.SignEvidence.contexts context.root.raw
      (Algebraic.SignEvidence.ofSigns signs))) :
    RowOperations.read value ctx sign binding context.root queries
      (packet value ctx signs) = .ok signs := by
  unfold packet
  have decoded := Algebraic.SignEvidence.codec_ofSigns_covered value ctx context signs hv hc
  have checked := Algebraic.SignEvidence.check_ofSigns context queries signs
  have graph : (Algebraic.SignEvidence.ofSigns signs).graph.selectedSigns? context.root queries
      signs.values = some signs := by
    simpa [Algebraic.SignEvidence.check?, Algebraic.SignEvidence.ofSigns] using checked
  unfold RowOperations.read
  rw [decoded]
  simp only [bind, Except.bind]
  simp only [Algebraic.SignEvidence.ofSigns] at graph ⊢
  simp [graph]

end Hex.RCF.RealCoefficients.RowEncode
