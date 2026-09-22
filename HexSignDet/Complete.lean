/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor

public section

namespace Hex.SignDet

/-- Select formal derivative slots without inventing a sign for a missing
slot. Index zero and every out-of-range index fail. -/
@[expose] def Thom.select (indices : List Nat) (signs : List Int) : Option (List Int) :=
  indices.mapM fun i => if 0 < i then signs[i - 1]? else none

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Canonically ordered full derivative slots, including the highest one. -/
@[expose] def RawDescriptor.full (raw : RawDescriptor E Ctx) (signs : List Int) :
    RawDescriptor E Ctx :=
  {raw with indices := (List.range raw.head.natDegree).map (· + 1), signs}

/-- A completion retains the exact domain/context and all the old selected
derivative signs. Both descriptors must separately have count-one evidence. -/
@[expose] def RawDescriptor.completes (source target : RawDescriptor E Ctx) : Bool :=
  decide (target.context = source.context ∧ target.head = source.head ∧
    target.lower = source.lower ∧ target.upper = source.upper ∧
    target.indices = (List.range source.head.natDegree).map (· + 1)) &&
  decide (Thom.select source.indices target.signs = some source.signs)

/-- Checked completion evidence. Unique-root preservation additionally uses
the companion's semantic interpretation of both descriptor replays. -/
structure Completion {sign : E → Int} {context : Ctx}
    (source : Descriptor E Ctx sign context) where
  descriptor : Descriptor E Ctx sign context
  agrees : source.raw.completes descriptor.raw = true

theorem Completion.bindings {sign : E → Int} {context : Ctx}
    {source : Descriptor E Ctx sign context} (c : Completion source) :
    c.descriptor.raw.context = source.raw.context ∧
    c.descriptor.raw.head = source.raw.head ∧
    c.descriptor.raw.lower = source.raw.lower ∧
    c.descriptor.raw.upper = source.raw.upper ∧
    c.descriptor.raw.indices = (List.range source.raw.head.natDegree).map (· + 1) ∧
    Thom.select source.raw.indices c.descriptor.raw.signs = some source.raw.signs := by
  have h := c.agrees
  simp only [RawDescriptor.completes, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2, h.2⟩

variable [Neg E] [Inv E]

/-- Complete a descriptor by a full derivative table and checked restriction
to its old signs. Internal failures remain diagnostic until total producer
completeness and the required Thom foundation have been supplied. -/
def Descriptor.buildCompletion {sign : E → Int} {context : Ctx}
    (source : Descriptor E Ctx sign context) : Except BuildError (Completion source) :=
  match Sturm.prepare sign source.raw.head source.raw.lower source.raw.upper with
  | none => .error .replay
  | some domain =>
    let raw := source.raw.full []
    match buildPrepared context domain raw.queries with
    | .error err => .error err
    | .ok t =>
      let candidates := (t.val.table t.property).rows.toList.filter fun row =>
        decide (Thom.select source.raw.indices row.1 = some source.raw.signs)
      match candidates with
      | [(signs, 1)] =>
        match Descriptor.ofReplay? sign context (source.raw.full signs) t.val with
        | none => .error .replay
        | some target =>
          if h : source.raw.completes target.raw = true then .ok ⟨target, h⟩
          else .error .replay
      | _ => .error .system

end Hex.SignDet
