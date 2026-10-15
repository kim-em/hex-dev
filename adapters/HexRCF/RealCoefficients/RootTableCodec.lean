/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootCodec
public import HexRCF.RealCoefficients.RootReplay
public section
namespace Hex.RCF.RealCoefficients.RootTableCodec
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Hashable E] [Hashable Ctx] {sign : E → Int} {binding : Ctx}
variable {p : DensePoly E} {lo hi : Endpoint E}

/-- Restore the exact supplied full table and its complete ordered root list
from finite stored-graph coverage. The original extraction equation suffices;
no successful native root producer is assumed. -/
theorem read_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (data : RootTable.Result sign binding p lo hi) (guards : List E)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (hv : value.Covers (Codec.Coefficients.graph (Dag.encode data.tree)))
    (hc : ctx.Covers (Codec.graphContexts (Dag.encode data.tree))) :
    RootTable.read value ctx sign binding guards p lo hi
      (Codec.graph value ctx (Dag.encode data.tree)) = .ok data := by
  have graph := RootCodec.replay_covered value ctx p lo hi
    ((⟨binding,p,lo,hi,[],[]⟩ : RawDescriptor E Ctx).full []).queries data.tree data.checked hv hc
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d member
    exact decide_eq_true (guarded d member)
  simp only [RootTable.read, all, ↓reduceIte, graph, bind, Except.bind,
    Dag.replay_encode data.checked]
  have extracted := (RootTable.extract_eq sign binding p lo hi data.tree data.checked).trans data.extracted
  split
  · rename_i error failed
    rw [extracted] at failed
    cases failed
  · rename_i roots accepted
    have same : roots = data.roots := Except.ok.inj (accepted.symm.trans extracted)
    cases same
    rfl

section Native
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable [Hashable parent.Value] [Hashable Signature]
variable {p : DensePoly parent.Value} {lo hi : Endpoint parent.Value}

/-- The native-indexed root reader shares the operation-parametric table
round trip, retaining the exact checked replay and every extracted root. -/
theorem read_roots (value : ValueCodec parent.Value)
    (data : RootReplay.Result p lo hi) (guards : List parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (covered : value.Covers (Codec.Coefficients.graph (Dag.encode data.replay))) :
    RootReplay.read value guards p lo hi
      (Codec.graph value Signature.codec (Dag.encode data.replay)) = .ok data := by
  let table : RootTable.Result parent.sign parent.signature p lo hi :=
    ⟨data.replay,data.checked,data.roots,data.extracted⟩
  have restored := read_covered value Signature.codec table guards guarded covered
    (Signature.codec_lawful.covers _)
  unfold RootReplay.read
  rw [restored]
  rfl

end Native
end Hex.RCF.RealCoefficients.RootTableCodec
