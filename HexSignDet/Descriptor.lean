/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Thom

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Checked count-one realization on exactly the formal derivatives selected
by the raw descriptor. The full context and root-domain bindings are checked
by the recursive table replay. No caller-supplied derivative vector is trusted. -/
@[expose] def RawDescriptor.check (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx) : Bool :=
  raw.wellFormed && decide (raw.context = context) &&
    evidence.check sign context raw.head raw.lower raw.upper raw.queries &&
    decide (evidence.node.system.count raw.signs = 1)

/-- A raw descriptor with accepted finite count-one evidence. Its semantic
unique-root interpretation is a companion obligation through query soundness.
The sign operation and immutable context are bound in the type. -/
structure Descriptor (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
    (sign : E → Int) (context : Ctx) where
  private mk ::
  raw : RawDescriptor E Ctx
  evidence : Replay E Ctx
  accepted : raw.check sign context evidence = true

/-- Validate supplied replay evidence. Failure says the certificate did not
establish this descriptor; it does not decide mathematical nonexistence. -/
def Descriptor.ofReplay? (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx) :
    Option (Descriptor E Ctx sign context) :=
  if h : raw.check sign context evidence = true then some ⟨raw, evidence, h⟩ else none

theorem Descriptor.ofReplay_isSome (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx) :
    (ofReplay? sign context raw evidence).isSome ↔ raw.check sign context evidence = true := by
  unfold ofReplay?
  split <;> simp_all

/-- Successful replay validation preserves the supplied descriptor literally. -/
theorem Descriptor.ofReplay_raw {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} {evidence : Replay E Ctx}
    {d : Descriptor E Ctx sign context}
    (h : ofReplay? sign context raw evidence = some d) : d.raw = raw := by
  unfold ofReplay? at h
  split at h
  · cases h
    rfl
  · contradiction

/-- Acceptance includes both the exact replay and count-one assertion;
matrix rank or an unrealized derivative word cannot replace either. -/
theorem RawDescriptor.check_eq {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} {evidence : Replay E Ctx}
    (h : raw.check sign context evidence = true) :
    raw.wellFormed = true ∧ raw.context = context ∧
      ∃ hc : evidence.check sign context raw.head raw.lower raw.upper raw.queries = true,
        (evidence.table hc).count raw.signs = 1 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hw, hctx⟩, hc⟩, hone⟩ := h
  exact ⟨hw, hctx, hc, (evidence.table_lookup hc raw.signs).trans hone⟩

/-- Finite moment interpretation makes descriptor replay assert exactly one
matching observation. The companion supplies observations from actual roots. -/
theorem RawDescriptor.check_count {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} {evidence : Replay E Ctx} {xs : List (List Int)}
    (h : raw.check sign context evidence = true)
    (ho : Observations raw.queries.length xs) (hm : evidence.Interprets raw.queries.length xs) :
    xs.countP (fun x => decide (x = raw.signs)) = 1 := by
  obtain ⟨_, _, hc, hone⟩ := check_eq h
  exact (evidence.table_count hc ho hm raw.signs).symm.trans hone

/-- Mathematical input diagnostics are separate from internal BKR failures.
Absent and ambiguous derivative conditions are not conflated. -/
inductive DescriptorError where
  | context
  | malformed
  | domain
  | absent
  | ambiguous
  deriving DecidableEq, Repr

variable [Neg E] [Inv E]

/-- Build count-one descriptor evidence from raw input, preserving internal
construction failures separately from input diagnostics. This diagnostic
constructor is not the final domain-exact `validate` API: removing its outer
error type requires the outstanding general BKR completeness proof. -/
def Descriptor.build (sign : E → Int) (context : Ctx) (raw : RawDescriptor E Ctx) :
    Except BuildError (Except DescriptorError (Descriptor E Ctx sign context)) :=
  if hctx : raw.context = context then
    if hw : raw.wellFormed = true then
      match hd : Sturm.prepare sign raw.head raw.lower raw.upper with
      | none => .ok (.error .domain)
      | some domain =>
        match buildPrepared context domain raw.queries with
        | .error err => .error err
        | .ok t =>
          have bindings := Sturm.prepare_eq_some sign raw.head raw.lower raw.upper domain hd
          have hc : t.val.check sign context raw.head raw.lower raw.upper raw.queries = true := by
            simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
          let count := (t.val.table hc).count raw.signs
          if hone : count = 1 then
            .ok (.ok ⟨raw, t.val, by
              simp only [RawDescriptor.check, hw, hctx, decide_true, Bool.true_and, hc]
              apply decide_eq_true
              exact (t.val.table_lookup hc raw.signs).symm.trans hone⟩)
          else if count = 0 then .ok (.error .absent)
          else .ok (.error .ambiguous)
    else .ok (.error .malformed)
  else .ok (.error .context)

end Hex.SignDet
