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

/-- Reuse an already checked table with exact input bindings and count one.
The proof arguments avoid rerunning the same replay during row extraction. -/
def Descriptor.ofTable {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx)
    (hw : raw.wellFormed = true) (hctx : raw.context = context)
    (hc : evidence.check sign context raw.head raw.lower raw.upper raw.queries = true)
    (hone : (evidence.table hc).count raw.signs = 1) : Descriptor E Ctx sign context :=
  ⟨raw, evidence, by
    simp only [RawDescriptor.check, hw, hctx, decide_true, Bool.true_and, hc]
    apply decide_eq_true
    exact (evidence.table_lookup hc raw.signs).symm.trans hone⟩

theorem Descriptor.ofTable_raw {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx)
    (hw : raw.wellFormed = true) (hctx : raw.context = context)
    (hc : evidence.check sign context raw.head raw.lower raw.upper raw.queries = true)
    (hone : (evidence.table hc).count raw.signs = 1) :
    (ofTable raw evidence hw hctx hc hone).raw = raw := by
  unfold ofTable
  rfl

/-- Reusing a checked table produces exactly the descriptor obtained by
checking that same evidence again. -/
theorem Descriptor.ofReplay_ofTable {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx)
    (hw : raw.wellFormed = true) (hctx : raw.context = context)
    (hc : evidence.check sign context raw.head raw.lower raw.upper raw.queries = true)
    (hone : (evidence.table hc).count raw.signs = 1) :
    ofReplay? sign context raw evidence = some (ofTable raw evidence hw hctx hc hone) := by
  have ha : raw.check sign context evidence = true := by
    simpa only [ofTable] using (ofTable raw evidence hw hctx hc hone).accepted
  unfold ofReplay? ofTable
  rw [dite_eq_left ha]

theorem Descriptor.ofReplay_isSome (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (evidence : Replay E Ctx) :
    (ofReplay? sign context raw evidence).isSome ↔ raw.check sign context evidence = true := by
  unfold ofReplay?
  split <;> simp_all

/-- Rejected raw evidence yields no descriptor. This exposes the failure
case without exposing the descriptor's private constructor. -/
theorem Descriptor.ofReplay_none {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} {evidence : Replay E Ctx}
    (h : raw.check sign context evidence = false) :
    ofReplay? sign context raw evidence = none := by
  simp [ofReplay?, h]

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
constructor is not the final domain-exact `validate` API: the companion now
proves producer success from actual roots relative to the named #10389 bridge,
but the total executable wrapper remains. -/
def Descriptor.build (sign : E → Int) (context : Ctx) (raw : RawDescriptor E Ctx) :
    Except BuildError (Except DescriptorError (Descriptor E Ctx sign context)) :=
  if hctx : raw.context = context then
    match hd : Sturm.prepare sign raw.head raw.lower raw.upper with
    | none => .ok (.error .domain)
    | some domain =>
      if hw : raw.wellFormed = true then
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

/-- Validate a raw descriptor when only success or failure matters. The
diagnostic `build` operation remains available to distinguish invalid inputs. -/
def Descriptor.validate (sign : E → Int) (context : Ctx) (raw : RawDescriptor E Ctx) :
    Option (Descriptor E Ctx sign context) :=
  match Descriptor.build sign context raw with
  | .ok (.ok d) => some d
  | _ => none

/-- The public option succeeds exactly when the diagnostic constructor succeeds. -/
theorem Descriptor.validate_eq_some {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} {d : Descriptor E Ctx sign context} :
    Descriptor.validate sign context raw = some d ↔
      Descriptor.build sign context raw = .ok (.ok d) := by
  unfold Descriptor.validate
  cases h : Descriptor.build sign context raw with
  | error err => simp
  | ok result =>
    cases result with
    | error err => simp
    | ok d' => simp

/-- A successful descriptor build retains the exact supplied raw input. -/
theorem Descriptor.build_raw {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} {d : Descriptor E Ctx sign context}
    (h : Descriptor.build sign context raw = .ok (.ok d)) : d.raw = raw := by
  unfold Descriptor.build at h
  split at h
  · split at h
    · simp at h
    · split at h
      · split at h
        · simp at h
        · dsimp only at h
          split at h
          · cases h
            rfl
          · split at h <;> simp at h
      · simp at h
  · simp at h

/-- A context mismatch has its own input diagnostic. -/
theorem Descriptor.build_context {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} (hctx : raw.context ≠ context) :
    Descriptor.build sign context raw = .ok (.error .context) := by
  unfold Descriptor.build
  simp [hctx]

/-- An invalid root domain has its own input diagnostic. -/
theorem Descriptor.build_domain {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} (hctx : raw.context = context)
    (hd : Sturm.prepare sign raw.head raw.lower raw.upper = none) :
    Descriptor.build sign context raw = .ok (.error .domain) := by
  unfold Descriptor.build
  simp only [hctx, ↓reduceDIte]
  split
  · rfl
  · rename_i domain hsome
    rw [hd] at hsome
    contradiction

/-- A malformed derivative word has its own input diagnostic on a prepared
domain. -/
theorem Descriptor.build_malformed {sign : E → Int} {context : Ctx}
    {raw : RawDescriptor E Ctx} (hctx : raw.context = context)
    {domain : Sturm.PreparedDomain E}
    (hd : Sturm.prepare sign raw.head raw.lower raw.upper = some domain)
    (hw : raw.wellFormed ≠ true) :
    Descriptor.build sign context raw = .ok (.error .malformed) := by
  unfold Descriptor.build
  simp only [hctx, ↓reduceDIte]
  split
  · rename_i hnone
    rw [hd] at hnone
    contradiction
  · rename_i domain' hsome
    have heq : domain' = domain := Option.some.inj (hsome.symm.trans hd)
    subst domain'
    simp [hw]

/-- Producer success rules out internal errors in descriptor validation. -/
theorem Descriptor.build_ok_ofPrepared (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx)
    (hprepared : ∀ domain, Sturm.prepare sign raw.head raw.lower raw.upper = some domain →
      ∃ t, buildPrepared context domain raw.queries = .ok t) :
    ∃ result, Descriptor.build sign context raw = .ok result := by
  unfold Descriptor.build
  split
  · split
    · exact ⟨_, rfl⟩
    · rename_i domain hd
      split
      · obtain ⟨t, ht⟩ := hprepared domain hd
        simp only [ht]
        split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- A prepared table with exactly one matching row builds an accepted
descriptor from the supplied raw input. -/
theorem Descriptor.build_ofCount (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (hctx : raw.context = context)
    (domain : Sturm.PreparedDomain E)
    (hd : Sturm.prepare sign raw.head raw.lower raw.upper = some domain)
    (hw : raw.wellFormed = true)
    (t : {t : Replay E Ctx // t.check domain.sign context domain.head domain.lower domain.upper
      raw.queries = true})
    (ht : buildPrepared context domain raw.queries = .ok t)
    (hone : t.val.node.system.count raw.signs = 1) :
    ∃ d, Descriptor.build sign context raw = .ok (.ok d) := by
  unfold Descriptor.build
  simp only [hctx, ↓reduceDIte, hw, Replay.table_lookup]
  split
  · rename_i hnone
    rw [hd] at hnone
    contradiction
  · rename_i domain' hd'
    have heq : domain' = domain := Option.some.inj (hd'.symm.trans hd)
    subst domain'
    simp only [ht, hone, ↓reduceDIte]
    exact ⟨_, rfl⟩

/-- Zero matching rows produce the absent diagnostic. -/
theorem Descriptor.build_absent_ofCount (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (hctx : raw.context = context)
    (domain : Sturm.PreparedDomain E)
    (hd : Sturm.prepare sign raw.head raw.lower raw.upper = some domain)
    (hw : raw.wellFormed = true)
    (t : {t : Replay E Ctx // t.check domain.sign context domain.head domain.lower domain.upper
      raw.queries = true})
    (ht : buildPrepared context domain raw.queries = .ok t)
    (hzero : t.val.node.system.count raw.signs = 0) :
    Descriptor.build sign context raw = .ok (.error .absent) := by
  unfold Descriptor.build
  simp only [hctx, ↓reduceDIte, hw, Replay.table_lookup]
  split
  · rename_i hnone
    rw [hd] at hnone
    contradiction
  · rename_i domain' hd'
    have heq : domain' = domain := Option.some.inj (hd'.symm.trans hd)
    subst domain'
    simp [ht, hzero]

/-- More than one matching row produces the ambiguous diagnostic. -/
theorem Descriptor.build_ambiguous_ofCount (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (hctx : raw.context = context)
    (domain : Sturm.PreparedDomain E)
    (hd : Sturm.prepare sign raw.head raw.lower raw.upper = some domain)
    (hw : raw.wellFormed = true)
    (t : {t : Replay E Ctx // t.check domain.sign context domain.head domain.lower domain.upper
      raw.queries = true})
    (ht : buildPrepared context domain raw.queries = .ok t)
    (hone : t.val.node.system.count raw.signs ≠ 1)
    (hzero : t.val.node.system.count raw.signs ≠ 0) :
    Descriptor.build sign context raw = .ok (.error .ambiguous) := by
  unfold Descriptor.build
  simp only [hctx, ↓reduceDIte, hw, Replay.table_lookup]
  split
  · rename_i hnone
    rw [hd] at hnone
    contradiction
  · rename_i domain' hd'
    have heq : domain' = domain := Option.some.inj (hd'.symm.trans hd)
    subst domain'
    simp [ht, hone, hzero]

end Hex.SignDet
