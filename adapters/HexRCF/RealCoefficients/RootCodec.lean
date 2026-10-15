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

/-- Restore any checked replay graph with finite literal coverage. Shape and
binding are derived using the owner's checker laws, independently of root count. -/
theorem replay_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (queries : List (DensePoly E)) (tree : SignDet.Replay E Ctx)
    (checked : tree.check sign binding p lo hi queries = true)
    (hv : value.Covers (Codec.Coefficients.graph (Dag.encode tree)))
    (hc : ctx.Covers (Codec.graphContexts (Dag.encode tree))) :
    Codec.readGraph value ctx binding p lo hi (Codec.graph value ctx (Dag.encode tree)) =
      .ok (Dag.encode tree) := by
  have replay := Dag.replay_encode checked
  cases valid : (Dag.encode tree).validate? sign binding
      p lo hi with
  | none => simp [Dag.replay?, valid, bind, Option.bind] at replay
  | some memo =>
    apply Codec.read_graph_covered value ctx binding p lo hi
      (Dag.encode tree) hv hc (Dag.encode_root tree)
      (Codec.Shape.of_validate valid) _ (Dag.encode_bounds tree)
    intro entry member
    have nodes := Dag.validate_nodes sign binding p lo hi
      (Dag.encode tree) memo valid
    have included : entry.node ∈ (Dag.encode tree).entries.map Dag.Entry.node :=
      Array.mem_map.mpr ⟨entry,member,rfl⟩
    rw [← nodes] at included
    obtain ⟨node,_,same⟩ := Array.mem_map.mp included
    rw [← same]
    exact Codec.bindings_of_check (Replay.check_node node.accepted)

/-- Restore a selected descriptor graph without a global codec law or native
producer premise. Arbitrary producer hashing and exact graph data are retained. -/
theorem graph_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (root : Descriptor E Ctx sign binding)
    (hv : value.Covers (Codec.Coefficients.graph (Dag.encode root.evidence)))
    (hc : ctx.Covers (Codec.graphContexts (Dag.encode root.evidence))) :
    Codec.readGraph value ctx binding root.raw.head root.raw.lower root.raw.upper
      (Codec.graph value ctx (Dag.encode root.evidence)) = .ok (Dag.encode root.evidence) := by
  obtain ⟨_,_,checked,_⟩ := RawDescriptor.check_iff.mp root.accepted
  exact replay_covered value ctx root.raw.head root.raw.lower root.raw.upper root.raw.queries
    root.evidence checked hv hc

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
