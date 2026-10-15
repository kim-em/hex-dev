/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.RootReplay
public import HexSignDet.Codec.FiniteGraph
public import HexSignDet.DagExpand
public import HexSignDet.DagBounds
public section
namespace Hex.RCF.RealCoefficients.RootCodec
open Hex Hex.RealClosure Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Hashable E] [Hashable Ctx] {sign : E → Int} {binding : Ctx}

/-- Restore the supplied descriptor graph with only finite literal coverage.
The owner checker supplies node shape and bindings; arbitrary producer hashing
is retained. No root/sign producer or globally lawful codec is required. -/
theorem graph_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (root : Descriptor E Ctx sign binding)
    (hv : value.Covers (Codec.Coefficients.graph (Dag.encode root.evidence)))
    (hc : ctx.Covers (Codec.graphContexts (Dag.encode root.evidence))) :
    Codec.readGraph value ctx binding root.raw.head root.raw.lower root.raw.upper
      (Codec.graph value ctx (Dag.encode root.evidence)) = .ok (Dag.encode root.evidence) := by
  obtain ⟨_,_,checked,_⟩ := RawDescriptor.check_iff.mp root.accepted
  have replay := Dag.replay_encode checked
  cases valid : (Dag.encode root.evidence).validate? sign binding
      root.raw.head root.raw.lower root.raw.upper with
  | none => simp [Dag.replay?, valid, bind, Option.bind] at replay
  | some memo =>
    apply Codec.read_graph_covered value ctx binding root.raw.head root.raw.lower root.raw.upper
      (Dag.encode root.evidence) hv hc (Dag.encode_root root.evidence)
      (Codec.Shape.of_validate valid) _ (Dag.encode_bounds root.evidence)
    intro entry member
    have nodes := Dag.validate_nodes sign binding root.raw.head root.raw.lower root.raw.upper
      (Dag.encode root.evidence) memo valid
    have included : entry.node ∈ (Dag.encode root.evidence).entries.map Dag.Entry.node :=
      Array.mem_map.mpr ⟨entry,member,rfl⟩
    rw [← nodes] at included
    obtain ⟨node,_,same⟩ := Array.mem_map.mp included
    rw [← same]
    exact Codec.bindings_of_check (Replay.check_node node.accepted)

/-- The independent subject and graph readers restore the exact existing
descriptor, including its selected embedding and complete checked evidence. -/
theorem read_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (root : Descriptor E Ctx sign binding)
    (head : value.Covers (Codec.Coefficients.poly root.raw.head))
    (lower : value.Covers (Codec.Coefficients.endpoint root.raw.lower))
    (upper : value.Covers (Codec.Coefficients.endpoint root.raw.upper))
    (graph : value.Covers (Codec.Coefficients.graph (Dag.encode root.evidence)))
    (context : ctx.decode (ctx.encode root.raw.context) = .ok root.raw.context)
    (contexts : ctx.Covers (Codec.graphContexts (Dag.encode root.evidence))) :
    Algebraic.RootReplay.readDescriptor value ctx sign binding
      (Codec.descriptor value ctx root.raw) (Codec.graph value ctx (Dag.encode root.evidence)) =
        .ok root := by
  have subject := Algebraic.SignRequests.readRoot_binding value ctx root.raw context
    (fun x member => head x (by simpa [Codec.Coefficients.poly] using member))
    (fun x same => lower x (by simp [Codec.Coefficients.endpoint, same]))
    (fun x same => upper x (by simp [Codec.Coefficients.endpoint, same]))
  have restored := graph_covered value ctx root graph contexts
  have data := Descriptor.ofReplay_data sign binding root.raw root.evidence
  rw [ite_eq_left root.accepted] at data
  have decoded : Descriptor.ofReplay? sign binding root.raw root.evidence = some root := by
    cases result : Descriptor.ofReplay? sign binding root.raw root.evidence with
    | none => simp [result] at data
    | some other =>
      simp only [result, Option.map_some, Option.some.injEq, Prod.mk.injEq] at data
      have same : other = root := by
        rw [← Descriptor.ofChecked_eq other, ← Descriptor.ofChecked_eq root]
        congr 1
        · exact data.1
        · exact data.2
      simp only [same]
  simp only [Algebraic.RootReplay.readDescriptor, subject, restored, bind, Except.bind,
    Dag.descriptor_encode, decoded, pure, Except.pure]

end Hex.RCF.RealCoefficients.RootCodec
