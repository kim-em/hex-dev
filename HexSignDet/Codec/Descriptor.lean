/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor
public import HexSignDet.Codec.Laws

/-! Literal selected-root subjects for composed certificate packets. The
reader preserves all six fields and checks equality with the caller's full
binding; parsing alone does not validate the selected root. -/

public section

namespace Hex.SignDet.Codec
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]

/-- Bind the full selected-root subject, including the derivative indices
and signs, rather than merely the graph's polynomial and interval. -/
@[expose] def descriptor (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) : Json :=
  .arr #[ctx.encode raw.context, poly value raw.head,
    endpoint value raw.lower, endpoint value raw.upper,
    list Json.of raw.indices, list Json.of raw.signs]

/-- Parse an unchecked literal subject; mathematical root validation is separate. -/
@[expose] def readDescriptor (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (j : Json) : Except String (RawDescriptor E Ctx) := do
  let fields ← tuple 6 j
  let context ← ctx.decode fields[0]
  let head ← readPoly value fields[1]
  let lower ← readEndpoint value fields[2]
  let upper ← readEndpoint value fields[3]
  let indices ← readList (Json.decode (α := Nat)) fields[4]
  let signs ← readList (Json.decode (α := Int)) fields[5]
  return ⟨context, head, lower, upper, indices, signs⟩

/-- Require exact literal subject equality; this does not validate its root. -/
@[expose] def readDescriptorBinding (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (j : Json) : Except String Unit := do
  let decoded ← readDescriptor value ctx j
  if decoded = raw then return ()
  else throw "selected root binding mismatch"

/-- Successful binding preserves the complete parsed subject literally. -/
theorem readDescriptorBinding_checked (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (j : Json)
    (h : readDescriptorBinding value ctx raw j = .ok ()) : readDescriptor value ctx j = .ok raw := by
  unfold readDescriptorBinding at h
  cases hr : readDescriptor value ctx j with
  | error error => simp [hr, bind, Except.bind] at h
  | ok decoded =>
    simp only [hr, bind, Except.bind] at h
    split at h
    · rename_i same
      simp only [same]
    · contradiction

/-- A reader bound to the exact caller subject accepts the complete record. -/
theorem readDescriptorBinding_of (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx) (j : Json)
    (h : readDescriptor value ctx j = .ok raw) :
    readDescriptorBinding value ctx raw j = .ok () := by
  simp [readDescriptorBinding, h, bind, Except.bind, pure, Except.pure]

omit [DecidableEq Ctx] in
/-- A root subject needs coverage only of its stored head, endpoints and
actual full context value. No global law for a partial coefficient reader is
assumed. -/
theorem read_descriptor_of (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (raw : RawDescriptor E Ctx)
    (context : ctx.decode (ctx.encode raw.context) = .ok raw.context)
    (head : ∀ x ∈ raw.head.toArray, value.decode (value.encode x) = .ok x)
    (lower : ∀ x, raw.lower = .finite x → value.decode (value.encode x) = .ok x)
    (upper : ∀ x, raw.upper = .finite x → value.decode (value.encode x) = .ok x) :
    readDescriptor value ctx (descriptor value ctx raw) = .ok raw := by
  simp [readDescriptor, descriptor, tuple, Json.getArr_arr, context,
    read_poly_of value raw.head head, read_endpoint_of value raw.lower lower,
    read_endpoint_of value raw.upper upper, read_list _ _ read_nat,
    read_list _ _ read_int, bind, Except.bind, pure, Except.pure]

end Hex.SignDet.Codec
