/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignRequests
public import HexRealClosure.ContextOperations
public import HexSignDet.Codec.FiniteGraph
import HexSignDet.DagExpand
import HexSignDet.DagBounds

public section

namespace Hex.RealClosure.Algebraic.RootReplay
open SignDet

variable {E Ctx : Type} [zero : Zero E] [dec : DecidableEq E] [decCtx : DecidableEq Ctx]
variable [one : One E] [add : Add E] [neg : Neg E] [sub : Sub E]
variable [mul : Mul E] [inv : Inv E] [div : Div E] [natCast : NatCast E]

/-- Every coefficient in the serialized subject and complete retained graph.
The list includes moment witnesses and duplicates. -/
@[expose] def coefficients (raw : RawDescriptor E Ctx) (graph : Dag E Ctx) : List E :=
  Codec.Coefficients.poly raw.head ++
    (Codec.Coefficients.endpoint raw.lower ++
      (Codec.Coefficients.endpoint raw.upper ++ Codec.Coefficients.graph graph))

/-- Every literal context in the subject and retained graph, including moments. -/
@[expose] def contexts (raw : RawDescriptor E Ctx) (graph : Dag E Ctx) : List Ctx :=
  raw.context :: Codec.graphContexts graph

/-- Finite coefficient requirements read directly from the supplied evidence
tree, without running hash consing. Repeated node occurrences remain present. -/
@[expose] def treeCoefficients (raw : RawDescriptor E Ctx) (tree : Replay E Ctx) : List E :=
  Codec.Coefficients.poly raw.head ++
    (Codec.Coefficients.endpoint raw.lower ++
      (Codec.Coefficients.endpoint raw.upper ++ tree.nodes.flatMap Codec.Coefficients.node))

/-- Literal contexts in the supplied subject and tree, without hash lookups.
Accepted evidence binds every node and moment context to the subject context. -/
@[expose] def treeContexts (raw : RawDescriptor E Ctx) (tree : Replay E Ctx) : List Ctx :=
  raw.context :: tree.nodes.flatMap Codec.nodeContexts

/-- Decode the complete root subject and all supplied graph entries before
checking a count-one descriptor. The predecessor codec may require exact
supplied sign facts; this reader does not replace missing coefficients. -/
@[expose] def readDescriptor (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : Codec.Json) :
    Except String (Descriptor E Ctx sign binding) := do
  let raw ← SignRequests.readRoot value ctx subject
  let graph ← Codec.readGraph value ctx binding raw.head raw.lower raw.upper evidence
  match graph.descriptor? sign binding raw with
  | none => throw "root descriptor replay rejected"
  | some descriptor => return descriptor

omit neg inv div in
/-- Finite coverage restores a checked descriptor from its literal subject and
encoded evidence, using the caller's hashing. No global codec law is required. -/
theorem readDescriptor_covered [Hashable E] [Hashable Ctx]
    (value : ValueCodec E) (ctx : ValueCodec Ctx) {sign : E → Int} {binding : Ctx}
    (root : Descriptor E Ctx sign binding)
    (hv : value.Covers (coefficients root.raw (Dag.encode root.evidence)))
    (hc : ctx.Covers (contexts root.raw (Dag.encode root.evidence))) :
    readDescriptor value ctx sign binding (Codec.descriptor value ctx root.raw)
      (Codec.graph value ctx (Dag.encode root.evidence)) = .ok root := by
  simp only [coefficients, ValueCodec.covers_append] at hv
  obtain ⟨head, lower, upper, graph⟩ := hv
  simp only [contexts, ValueCodec.covers_cons] at hc
  have subject := SignRequests.readRoot_binding value ctx root.raw hc.1
    (fun x hx => head x (by simpa [Codec.Coefficients.poly] using hx))
    (fun x hx => lower x (by simp [Codec.Coefficients.endpoint, hx]))
    (fun x hx => upper x (by simp [Codec.Coefficients.endpoint, hx]))
  obtain ⟨_, _, accepted, _⟩ := RawDescriptor.check_eq root.accepted
  obtain ⟨memo, checked⟩ := Dag.validate_encode accepted
  have restored : Codec.readGraph value ctx binding root.raw.head root.raw.lower root.raw.upper
      (Codec.graph value ctx (Dag.encode root.evidence)) = .ok (Dag.encode root.evidence) := by
    exact Codec.read_graph_covered value ctx binding root.raw.head root.raw.lower root.raw.upper
      (Dag.encode root.evidence) graph hc.2 (Dag.encode_root root.evidence)
      (Codec.Shape.of_validate checked) (Codec.bindings_of_validate checked)
      (Dag.encode_bounds root.evidence)
  simp [readDescriptor, subject, restored, Dag.descriptor_encode, Descriptor.ofReplay_self,
    bind, Except.bind, pure, Except.pure]

omit neg inv div in
/-- Tree coverage implies exact restoration under any caller hash instances.
The caller need not evaluate the encoder to establish either finite premise. -/
theorem readDescriptor_tree [Hashable E] [Hashable Ctx]
    (value : ValueCodec E) (ctx : ValueCodec Ctx) {sign : E → Int} {binding : Ctx}
    (root : Descriptor E Ctx sign binding)
    (hv : value.Covers (treeCoefficients root.raw root.evidence))
    (hc : ctx.Covers (treeContexts root.raw root.evidence)) :
    readDescriptor value ctx sign binding (Codec.descriptor value ctx root.raw)
      (Codec.graph value ctx (Dag.encode root.evidence)) = .ok root := by
  simp only [treeCoefficients, ValueCodec.covers_append, ValueCodec.covers_flatMap] at hv
  simp only [treeContexts, ValueCodec.covers_cons, ValueCodec.covers_flatMap] at hc
  apply readDescriptor_covered value ctx root
  · simp only [coefficients, ValueCodec.covers_append]
    refine ⟨hv.1, hv.2.1, hv.2.2.1, ?_⟩
    simpa only [Codec.Coefficients.graph, ValueCodec.covers_flatMap,
      Array.mem_toList_iff] using
      Dag.encode_nodes (fun n => value.Covers (Codec.Coefficients.node n)) root.evidence hv.2.2.2
  · simp only [contexts, ValueCodec.covers_cons]
    refine ⟨hc.1, ?_⟩
    simpa only [Codec.graphContexts, ValueCodec.covers_flatMap, Array.mem_toList_iff] using
      Dag.encode_nodes (fun n => ctx.Covers (Codec.nodeContexts n)) root.evidence hc.2

omit neg inv div in
/-- An accepted descriptor retains the entire decoded subject literally,
including its derivative indices and signs. -/
theorem readDescriptor_subject (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : Codec.Json)
    (descriptor : Descriptor E Ctx sign binding)
    (h : readDescriptor value ctx sign binding subject evidence = .ok descriptor) :
    SignRequests.readRoot value ctx subject = .ok descriptor.raw := by
  unfold readDescriptor at h
  cases hr : SignRequests.readRoot value ctx subject with
  | error message => simp [hr, bind, Except.bind] at h
  | ok raw =>
    simp only [hr, bind, Except.bind] at h
    cases hg : Codec.readGraph value ctx binding raw.head raw.lower raw.upper evidence with
    | error message => simp [hg] at h
    | ok graph =>
      simp only [hg] at h
      cases hd : graph.descriptor? sign binding raw with
      | none => simp [hd] at h
      | some checked =>
        simp only [hd, pure, Except.pure, Except.ok.injEq] at h
        subst descriptor
        rw [Dag.descriptor_raw hd]

/-- Parse the existing subject and graph byte records, then validate their
complete descriptor. Both records use the shared bounded byte parser. The
predecessor codec controls lower-level coefficient evidence. -/
@[expose] def decodeDescriptor (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : ByteArray)
    (limits : Codec.Limits := {}) : Except String (Descriptor E Ctx sign binding) :=
  Codec.decodePair (readDescriptor value ctx sign binding) subject evidence limits

omit neg inv div in
/-- The actual byte printer/parser preserves descriptor acceptance and exact
rejection, including malformed supplied certificates. Only the lexical resource
prechecks are assumed; no mathematical validity or parser-success premise is
required. -/
theorem decodeDescriptor_write (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : Codec.Json)
    (limits : Codec.Limits)
    (subjectBound : Codec.checkBytes limits subject.writeBytes = .ok ())
    (evidenceBound : Codec.checkBytes limits evidence.writeBytes = .ok ()) :
    decodeDescriptor value ctx sign binding subject.writeBytes evidence.writeBytes limits =
      readDescriptor value ctx sign binding subject evidence := by
  exact Codec.decodePair_write _ subject evidence limits subjectBound evidenceBound

omit neg inv div in
/-- The bounded byte reader restores the same checked descriptor under finite
literal coverage. The only additional premises are the lexical resource checks. -/
theorem decodeDescriptor_covered [Hashable E] [Hashable Ctx]
    (value : ValueCodec E) (ctx : ValueCodec Ctx) {sign : E → Int} {binding : Ctx}
    (root : Descriptor E Ctx sign binding)
    (hv : value.Covers (coefficients root.raw (Dag.encode root.evidence)))
    (hc : ctx.Covers (contexts root.raw (Dag.encode root.evidence)))
    (limits : Codec.Limits)
    (subjectBound : Codec.checkBytes limits
      (Codec.descriptor value ctx root.raw).writeBytes = .ok ())
    (evidenceBound : Codec.checkBytes limits
      (Codec.graph value ctx (Dag.encode root.evidence)).writeBytes = .ok ()) :
    decodeDescriptor value ctx sign binding (Codec.descriptor value ctx root.raw).writeBytes
      (Codec.graph value ctx (Dag.encode root.evidence)).writeBytes limits = .ok root := by
  rw [decodeDescriptor_write value ctx sign binding _ _ limits subjectBound evidenceBound]
  exact readDescriptor_covered value ctx root hv hc

omit neg inv div in
/-- Every accepted byte descriptor retains the full decoded subject. -/
theorem decodeDescriptor_subject (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : ByteArray)
    (limits : Codec.Limits) (descriptor : Descriptor E Ctx sign binding)
    (accepted : decodeDescriptor value ctx sign binding subject evidence limits = .ok descriptor) :
    ∃ raw, Codec.parse limits subject = .ok raw ∧
      SignRequests.readRoot value ctx raw = .ok descriptor.raw := by
  unfold decodeDescriptor Codec.decodePair at accepted
  cases hs : Codec.parse limits subject with
  | error message => simp [hs] at accepted
  | ok raw =>
    simp only [hs] at accepted
    cases hg : Codec.parse limits evidence with
    | error message => simp [hg] at accepted
    | ok graph =>
      simp only [hg] at accepted
      exact ⟨raw, rfl, readDescriptor_subject value ctx sign binding raw graph descriptor accepted⟩

/-- Reconstruct with equal supplied predecessor operations, including the
canonical prepared-query cache and reduction policy. Transport retains the checked
root and cache with the original operations. Ordinary-kernel assembly may stop at a
missing scalar fact; compiled execution retains the coefficient fallback. -/
@[expose] def readContext (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (clean : E → Bool)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add) (hn : predecessorNeg = neg)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul) (hi : predecessorInv = inv)
    (hd : predecessorDiv = div) (hc : predecessorNatCast = natCast)
    (subject evidence : Codec.Json) : Except String (@Context E Ctx zero dec one add neg sub mul inv div natCast
      decCtx sign binding) :=
  letI := predecessorOne
  letI := predecessorAdd
  letI := predecessorNeg
  letI := predecessorSub
  letI := predecessorMul
  letI := predecessorInv
  letI := predecessorDiv
  letI := predecessorNatCast
  do
    let root ← readDescriptor value ctx sign binding subject evidence
    let context := Context.adjoin root clean
    return @Context.changeOps E Ctx _ _ _ one add neg sub mul inv div natCast
      predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
      predecessorInv predecessorDiv predecessorNatCast ho ha hn hs hm hi hd hc
      sign binding context

/-- Supplied operations preserve exact native reconstruction, including
rejection. The equality assumes no completeness of the finite fact lists. -/
theorem readContext_eq (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (clean : E → Bool)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add) (hn : predecessorNeg = neg)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul) (hi : predecessorInv = inv)
    (hd : predecessorDiv = div) (hc : predecessorNatCast = natCast)
    (subject evidence : Codec.Json) :
    @readContext E Ctx zero dec decCtx one add neg sub mul inv div natCast
      value ctx sign binding clean predecessorOne predecessorAdd predecessorNeg
      predecessorSub predecessorMul predecessorInv predecessorDiv predecessorNatCast
      ho ha hn hs hm hi hd hc subject evidence =
      (@readDescriptor E Ctx zero dec decCtx one add sub mul natCast
        value ctx sign binding subject evidence).map
        (fun root => @Context.adjoin E Ctx zero dec one add neg sub mul inv div natCast
          decCtx sign binding root clean) := by
  cases ho
  cases ha
  cases hn
  cases hs
  cases hm
  cases hi
  cases hd
  cases hc
  unfold readContext
  cases readDescriptor value ctx sign binding subject evidence with
  | error message => rfl
  | ok root =>
    simp only [bind, Except.bind, pure, Except.pure, Except.map]
    rw [Context.changeOps_self]

end Hex.RealClosure.Algebraic.RootReplay
