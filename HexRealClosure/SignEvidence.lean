/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignRequests
public import HexSignDet.Codec.GraphLaws
public import HexSignDet.DagReplay
public import HexSignDet.DagBounds
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node

public section

namespace Hex.RealClosure.Algebraic
open SignDet

/-- One joint child certificate for an ordered list of literal polynomial keys.
The graph shares repeated nodes; the sign vector retains repeated requests.
This data is untrusted until `SignEvidence.check?` succeeds. -/
structure SignEvidence (E Ctx : Type) [Zero E] [DecidableEq E] where
  queries : List (DensePoly E)
  values : Vector Int queries.length
  graph : Dag E Ctx

namespace SignEvidence
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]

/-- The packet contains one full root binding and one shared graph. Readers
must supply that exact root and the required ordered keys. -/
@[expose] def codec (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) : ValueCodec (SignEvidence E Ctx) where
  encode evidence := .arr #[Codec.Json.of (1 : Nat), SignRequests.binding value ctx raw,
    Codec.list (Codec.poly value) evidence.queries,
    Codec.array Codec.Json.of evidence.values.toArray, Codec.graph value ctx evidence.graph]
  decode j := do
    let fields ← Codec.tuple 5 j
    if (← Codec.Json.decode (α := Nat) fields[0]) != 1 then
      throw "unsupported sign evidence version"
    SignRequests.readBinding value ctx raw fields[1]
    let queries ← Codec.readList (Codec.readPoly value) fields[2]
    let values ← Codec.vector queries.length (Codec.Json.decode (α := Int)) fields[3]
    let graph ← Codec.readGraph value ctx raw.context raw.head raw.lower raw.upper fields[4]
    return ⟨queries, values, graph⟩

/-- Literal roundtrips require only the graph parser's structural bounds and
lawful predecessor codecs. This theorem does not assert graph acceptance. -/
theorem codec_roundtrip (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (raw : RawDescriptor E Ctx)
    (evidence : SignEvidence E Ctx)
    (root : evidence.graph.root < evidence.graph.entries.size)
    (shape : ∀ e ∈ evidence.graph.entries, Codec.Shape e.node)
    (subjects : ∀ e ∈ evidence.graph.entries,
      Codec.bindings raw.context raw.head raw.lower raw.upper e.node = true)
    (bounds : ∀ (i : Nat) (h : i < evidence.graph.entries.size),
      ∀ pair ∈ evidence.graph.entries[i].children, pair.1 < i ∧ pair.2 < i) :
    (codec value ctx raw).decode ((codec value ctx raw).encode evidence) = .ok evidence := by
  have binding := SignRequests.readRoot_binding value ctx raw (hc _)
    (fun x _ => hv x) (fun x _ => hv x) (fun x _ => hv x)
  have graph := Codec.read_graph value ctx hv hc raw.context raw.head raw.lower raw.upper
    evidence.graph root shape subjects bounds
  simp [codec, Codec.tuple, Codec.Json.getArr_arr, SignRequests.readBinding, binding,
    Codec.read_list _ _ (Codec.read_poly value hv),
    Codec.read_vector _ _ Codec.read_int evidence.values, graph,
    bind, Except.bind, pure, Except.pure]

/-- The actual byte printer/parser preserves that complete literal packet
under the caller's lexical limits; no parser-success premise is assumed. -/
theorem codec_bytes (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (raw : RawDescriptor E Ctx)
    (evidence : SignEvidence E Ctx)
    (root : evidence.graph.root < evidence.graph.entries.size)
    (shape : ∀ e ∈ evidence.graph.entries, Codec.Shape e.node)
    (subjects : ∀ e ∈ evidence.graph.entries,
      Codec.bindings raw.context raw.head raw.lower raw.upper e.node = true)
    (bounds : ∀ (i : Nat) (h : i < evidence.graph.entries.size),
      ∀ pair ∈ evidence.graph.entries[i].children, pair.1 < i ∧ pair.2 < i)
    (limits : Codec.Limits)
    (bytes : Codec.checkBytes limits ((codec value ctx raw).encodeBytes evidence) = .ok ()) :
    (codec value ctx raw).decodeBytes ((codec value ctx raw).encodeBytes evidence) limits =
      .ok evidence :=
  ValueCodec.decode_encode_of _ _
    (codec_roundtrip value ctx hv hc raw evidence root shape subjects bounds) limits bytes

variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {coeffSign : E → Int} {parent : Ctx}

/-- Check every supplied graph entry once, then select its joint row. Missing,
reordered or extra keys reject even when the remaining signs are valid.
This level adds no query production. Coefficient arithmetic retains the
caller's operations and may still evaluate lower-level signs. -/
@[expose] def check? (evidence : SignEvidence E Ctx)
    (context : Context E Ctx coeffSign parent) (required : List (DensePoly E)) :
    Option (SelectedSigns context.root required) :=
  if h : evidence.queries = required then
    h ▸ evidence.graph.selectedSigns? context.root evidence.queries evidence.values
  else none

/-- Acceptance retains the exact requested keys, signs and supplied graph. -/
theorem check_evidence (evidence : SignEvidence E Ctx)
    (context : Context E Ctx coeffSign parent) (required : List (DensePoly E))
    (selected : SelectedSigns context.root required)
    (h : evidence.check? context required = some selected) :
    ∃ same : evidence.queries = required,
      evidence.graph.selectedSigns? context.root required (same ▸ evidence.values) =
        some selected := by
  unfold check? at h
  split at h
  · rename_i same
    subst required
    exact ⟨rfl, h⟩
  · contradiction

/-- Encode the existing checked producer's literal tree. No new query kernel
or alternative sign algorithm is used. -/
@[expose] def ofSigns [Hashable E] [Hashable Ctx]
    {root : Descriptor E Ctx coeffSign parent} {queries : List (DensePoly E)}
    (signs : SelectedSigns root queries) : SignEvidence E Ctx :=
  ⟨queries, signs.values, Dag.encode signs.evidence⟩

/-- The independent graph checker accepts every packet made from the actual
checked joint signs, including the empty request list. -/
theorem check_ofSigns [Hashable E] [Hashable Ctx]
    (context : Context E Ctx coeffSign parent) (queries : List (DensePoly E))
    (signs : SelectedSigns context.root queries) :
    (ofSigns signs).check? context queries = some signs := by
  obtain ⟨accepted, row⟩ := signs.check_eq
  rw [signs.evidence.table_rows accepted] at row
  unfold check?
  split
  · change Dag.selectedSigns? context.root queries signs.values
      (Dag.encode signs.evidence) = some signs
    unfold Dag.selectedSigns?
    rw [Dag.replay_encode accepted]
    simp only [bind, Option.bind, row, dite_eq_left, pure]
    cases signs
    rfl
  · rename_i different
    exact (different rfl).elim

omit [Neg E] [Inv E] [Div E] in
private theorem node_bindings {sign : E → Int} {parent : Ctx}
    {head : DensePoly E} {lower upper : Endpoint E} {queries : List (DensePoly E)}
    {node : Node E Ctx} (h : node.check sign parent head lower upper queries = true) :
    Codec.bindings parent head lower upper node = true := by
  obtain ⟨subject, _⟩ := Node.check_bindings h
  simp only [Codec.bindings, subject.1, subject.2.1, subject.2.2.1,
    subject.2.2.2.1, and_self, decide_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro cert mem
  obtain ⟨i, hi, same⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp mem)
  subst cert
  have checked := Sturm.check_bindings sign parent head _ lower upper _ node.moments[i]
    (checkMoment_query (Node.check_moment h ⟨i, hi⟩))
  simp only [checked.1, checked.2.1, checked.2.2.2.1, checked.2.2.2.2.1,
    and_self, decide_true]

/-- The actual encoder retains every node and moment's literal root-domain
binding from checked production. No coefficient interpretation is needed. -/
theorem ofSigns_bindings [Hashable E] [Hashable Ctx]
    (context : Context E Ctx coeffSign parent) {queries : List (DensePoly E)}
    (signs : SelectedSigns context.root queries) :
    ∀ entry ∈ (ofSigns signs).graph.entries,
      Codec.bindings context.root.raw.context context.root.raw.head
        context.root.raw.lower context.root.raw.upper entry.node = true := by
  obtain ⟨accepted, _⟩ := signs.check_eq
  have replay := Dag.replay_encode accepted
  cases hv : (Dag.encode signs.evidence).validate? coeffSign parent context.root.raw.head
      context.root.raw.lower context.root.raw.upper with
  | none => simp [Dag.replay?, hv, bind, Option.bind] at replay
  | some memo =>
    intro entry he
    have nodes := Dag.validate_nodes coeffSign parent context.root.raw.head
      context.root.raw.lower context.root.raw.upper (Dag.encode signs.evidence) memo hv
    have member : entry.node ∈ (Dag.encode signs.evidence).entries.map Dag.Entry.node :=
      Array.mem_map.mpr ⟨entry, he, rfl⟩
    rw [← nodes] at member
    obtain ⟨checked, _, same⟩ := Array.mem_map.mp member
    rw [← same, (RawDescriptor.check_eq context.root.accepted).2.1]
    exact node_bindings (Replay.check_node checked.accepted)

/-- Producer output satisfies the graph parser's root and child-reference
bounds and literal bindings. Node-shape premises remain separate obligations. -/
theorem codec_ofSigns [Hashable E] [Hashable Ctx]
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (hv : value.Lawful) (hc : ctx.Lawful)
    (context : Context E Ctx coeffSign parent) {queries : List (DensePoly E)}
    (signs : SelectedSigns context.root queries)
    (shape : ∀ e ∈ (ofSigns signs).graph.entries, Codec.Shape e.node) :
    (codec value ctx context.root.raw).decode
      ((codec value ctx context.root.raw).encode (ofSigns signs)) = .ok (ofSigns signs) :=
  codec_roundtrip value ctx hv hc context.root.raw (ofSigns signs)
    (Dag.encode_root signs.evidence) shape (ofSigns_bindings context signs)
    (Dag.encode_bounds signs.evidence)

/-- The producer packet survives actual bytes under the parser's lexical
limits and the remaining node-shape and coefficient-coverage premises. -/
theorem bytes_ofSigns [Hashable E] [Hashable Ctx]
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (hv : value.Lawful) (hc : ctx.Lawful)
    (context : Context E Ctx coeffSign parent) {queries : List (DensePoly E)}
    (signs : SelectedSigns context.root queries)
    (shape : ∀ e ∈ (ofSigns signs).graph.entries, Codec.Shape e.node)
    (limits : Codec.Limits)
    (bytes : Codec.checkBytes limits
      ((codec value ctx context.root.raw).encodeBytes (ofSigns signs)) = .ok ()) :
    (codec value ctx context.root.raw).decodeBytes
      ((codec value ctx context.root.raw).encodeBytes (ofSigns signs)) limits = .ok (ofSigns signs) :=
  ValueCodec.decode_encode_of _ _ (codec_ofSigns value ctx hv hc context signs shape) limits bytes

end SignEvidence

variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {coeffSign : E → Int} {parent : Ctx}

/-- Produce a shared child packet for the exact requested sign keys. This is
production, not replay. In particular, it runs the existing BKR producer even
if ordinary scalar arithmetic could use an interval shortcut. -/
@[expose] def Context.buildEvidence [Hashable E] [Hashable Ctx]
    (context : Context E Ctx coeffSign parent) (queries : List (DensePoly E)) :
    Except BuildError (SignEvidence E Ctx) :=
  SignEvidence.ofSigns <$> context.buildSigns queries

theorem Context.buildEvidence_of_success [Hashable E] [Hashable Ctx]
    (context : Context E Ctx coeffSign parent) (queries : List (DensePoly E))
    (signs : SelectedSigns context.root queries)
    (h : context.buildSigns queries = .ok signs) :
    context.buildEvidence queries = .ok (SignEvidence.ofSigns signs) := by
  simp [buildEvidence, h, Functor.map, Except.map]

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.SignEvidence.bytes_ofSigns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.SignEvidence.bytes_ofSigns
