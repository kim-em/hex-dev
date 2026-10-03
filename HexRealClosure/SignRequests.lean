/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts
public import HexSignDet.Codec.Bytes
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json

public section

namespace Hex.RealClosure.Algebraic
open SignDet

/-- A stored polynomial and claimed sign referring to one already checked
graph entry. The enclosing reader fixes the selected-root context. -/
structure SignRequest (E : Type) [Zero E] [DecidableEq E] where
  polynomial : DensePoly E
  sign : Int
  entry : Nat

namespace SignRequest
variable {E Ctx : Type} [Zero E] [DecidableEq E]

@[expose] def encode (value : ValueCodec E) (request : SignRequest E) : Codec.Json :=
  .arr #[Codec.poly value request.polynomial, Codec.Json.of request.sign,
    Codec.Json.of request.entry]

/-- Parsing supplies literal references only. Bounds and the claimed sign
are checked when selecting from the accepted memo. -/
@[expose] def decode (value : ValueCodec E) (j : Codec.Json) : Except String (SignRequest E) := do
  let fields ← Codec.tuple 3 j
  return ⟨← Codec.readPoly value fields[0], ← Codec.Json.decode fields[1],
    ← Codec.Json.decode fields[2]⟩

theorem decode_encode (value : ValueCodec E) (request : SignRequest E)
    (covered : ∀ x ∈ request.polynomial.toArray, value.decode (value.encode x) = .ok x) :
    decode value (encode value request) = .ok request := by
  simp [decode, encode, Codec.tuple, Codec.Json.getArr_arr, Codec.read_poly_of value _ covered,
    bind, Except.bind, pure, Except.pure]

end SignRequest

namespace SignRequest
variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Bind directly to the original stored query. Lookup computes no native
query reduction; any preparation witnesses belong to the checked graph. -/
@[expose] def signs? (request : SignRequest E) (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) :
    Option (SelectedSigns context.root [request.polynomial]) :=
  SelectedSigns.readMemo? context.root [request.polynomial] #v[request.sign] memo request.entry

theorem signs_value {request : SignRequest E} {context : Context E Ctx coeffSign parent}
    {head : DensePoly E} {lower upper : Endpoint E}
    {memo : Array (Dag.Checked coeffSign parent head lower upper)}
    {signs : SelectedSigns context.root [request.polynomial]}
    (h : request.signs? context memo = some signs) : signs.value = request.sign := by
  obtain ⟨bound, _, accepted⟩ := SelectedSigns.readMemo_evidence h
  obtain ⟨_, _, values, _⟩ := SelectedSigns.ofMemo_evidence accepted
  simp [SelectedSigns.value, values]

end SignRequest

namespace SignRequests
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]

/-- Bind the full selected-root subject, including the derivative indices
and signs, rather than merely the graph's polynomial and interval. -/
@[expose] def binding (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) : Codec.Json :=
  .arr #[ctx.encode raw.context, Codec.poly value raw.head,
    Codec.endpoint value raw.lower, Codec.endpoint value raw.upper,
    Codec.list Codec.Json.of raw.indices, Codec.list Codec.Json.of raw.signs]

@[expose] def readRoot (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (j : Codec.Json) : Except String (RawDescriptor E Ctx) := do
  let fields ← Codec.tuple 6 j
  let context ← ctx.decode fields[0]
  let head ← Codec.readPoly value fields[1]
  let lower ← Codec.readEndpoint value fields[2]
  let upper ← Codec.readEndpoint value fields[3]
  let indices ← Codec.readList (Codec.Json.decode (α := Nat)) fields[4]
  let signs ← Codec.readList (Codec.Json.decode (α := Int)) fields[5]
  return ⟨context, head, lower, upper, indices, signs⟩

@[expose] def readBinding (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (j : Codec.Json) : Except String Unit := do
  let decoded ← readRoot value ctx j
  if decoded = raw then return ()
  else throw "selected root binding mismatch"

/-- Successful binding preserves the complete parsed subject literally. -/
theorem readBinding_checked (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (j : Codec.Json)
    (h : readBinding value ctx raw j = .ok ()) : readRoot value ctx j = .ok raw := by
  unfold readBinding at h
  cases hr : readRoot value ctx j with
  | error error => simp [hr, bind, Except.bind] at h
  | ok decoded =>
    simp only [hr, bind, Except.bind] at h
    split at h
    · rename_i same
      simpa only [same] using hr
    · contradiction

private theorem read_endpoint_of (value : ValueCodec E) (endpoint : Endpoint E)
    (covered : ∀ x, endpoint = .finite x → value.decode (value.encode x) = .ok x) :
    Codec.readEndpoint value (Codec.endpoint value endpoint) = .ok endpoint := by
  cases endpoint with
  | negInf => rfl
  | posInf => rfl
  | finite x =>
    simp [Codec.readEndpoint, Codec.endpoint, Codec.Json.getArr_arr, covered x rfl,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- A root subject needs coverage only of its stored head, endpoints and
actual full context value. No global law for a partial coefficient reader is
assumed. -/
theorem readRoot_binding (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx)
    (context : ctx.decode (ctx.encode raw.context) = .ok raw.context)
    (head : ∀ x ∈ raw.head.toArray, value.decode (value.encode x) = .ok x)
    (lower : ∀ x, raw.lower = .finite x → value.decode (value.encode x) = .ok x)
    (upper : ∀ x, raw.upper = .finite x → value.decode (value.encode x) = .ok x) :
    readRoot value ctx (binding value ctx raw) = .ok raw := by
  simp [readRoot, binding, Codec.tuple, Codec.Json.getArr_arr, context,
    Codec.read_poly_of value raw.head head, read_endpoint_of value raw.lower lower,
    read_endpoint_of value raw.upper upper, Codec.read_list _ _ Codec.read_nat,
    Codec.read_list _ _ Codec.read_int, bind, Except.bind, pure, Except.pure]

/-- Version 1 stores one complete root binding followed by ordered sign
references. It does not embed another copy of the shared graph. -/
@[expose] def codec (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) : ValueCodec (Array (SignRequest E)) where
  encode requests := .arr #[Codec.Json.of (1 : Nat), binding value ctx raw,
    Codec.array (SignRequest.encode value) requests]
  decode j := do
    let fields ← Codec.tuple 3 j
    if (← Codec.Json.decode (α := Nat) fields[0]) != 1 then
      throw "unsupported sign request version"
    readBinding value ctx raw fields[1]
    Codec.readArray (SignRequest.decode value) fields[2]

/-- Strict predecessor readers need coverage of the actual binding and request
coefficients only. The ordered requests and all their indices roundtrip. -/
theorem codec_roundtrip (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (requests : Array (SignRequest E))
    (context : ctx.decode (ctx.encode raw.context) = .ok raw.context)
    (head : ∀ x ∈ raw.head.toArray, value.decode (value.encode x) = .ok x)
    (lower : ∀ x, raw.lower = .finite x → value.decode (value.encode x) = .ok x)
    (upper : ∀ x, raw.upper = .finite x → value.decode (value.encode x) = .ok x)
    (covered : ∀ request ∈ requests, ∀ x ∈ request.polynomial.toArray,
      value.decode (value.encode x) = .ok x) :
    (codec value ctx raw).decode ((codec value ctx raw).encode requests) = .ok requests := by
  have root := readRoot_binding value ctx raw context head lower upper
  have refs := Codec.read_array_of (SignRequest.encode value) (SignRequest.decode value) requests
    (fun request h => SignRequest.decode_encode value request (covered request h))
  simp [codec, Codec.tuple, Codec.Json.getArr_arr, readBinding, root, refs,
    bind, Except.bind, pure, Except.pure]

theorem codec_bytes_roundtrip (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (requests : Array (SignRequest E))
    (context : ctx.decode (ctx.encode raw.context) = .ok raw.context)
    (head : ∀ x ∈ raw.head.toArray, value.decode (value.encode x) = .ok x)
    (lower : ∀ x, raw.lower = .finite x → value.decode (value.encode x) = .ok x)
    (upper : ∀ x, raw.upper = .finite x → value.decode (value.encode x) = .ok x)
    (covered : ∀ request ∈ requests, ∀ x ∈ request.polynomial.toArray,
      value.decode (value.encode x) = .ok x)
    (limits : Codec.Limits)
    (bound : Codec.checkBytes limits ((codec value ctx raw).encodeBytes requests) = .ok ()) :
    (codec value ctx raw).decodeBytes ((codec value ctx raw).encodeBytes requests) limits =
      .ok requests :=
  ValueCodec.decode_encode_of _ _ (codec_roundtrip value ctx raw requests
    context head lower upper covered) limits bound

end SignRequests
end Hex.RealClosure.Algebraic
