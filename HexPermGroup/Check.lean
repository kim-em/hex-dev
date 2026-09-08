/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Chain

public section

namespace Hex.PermGroup

/-- Check every generator's provenance in the preceding generator array. -/
@[expose] def checkWords (S T : Array (Perm n)) (words : Vector Program T.size) : Bool :=
  decide (∀ i : Fin T.size, checkWord S T[i.val] words[i.val] = true)

theorem checkWords_sound {S T : Array (Perm n)} {words : Vector Program T.size}
    (h : checkWords S T words = true) {p : Perm n} (hp : Generated T p) : Generated S p := by
  apply hp.mono
  intro q hq
  rcases Array.mem_iff_getElem.mp hq with ⟨i, hi, rfl⟩
  exact checkWord_sound ((of_decide_eq_true h) ⟨i, hi⟩)

namespace Chain

/-- Replace provenance at the top level. Internal chain checking does not inspect
these words; the caller checks them against the new preceding generator array. -/
@[expose] def reword (c : Chain n) (words : Vector Program c.generators.size) : Chain n :=
  match c with
  | .leaf S _ => .leaf S words
  | .cons level tail => .cons { level with words := words } tail

@[simp] theorem generators_reword (c : Chain n) (words : Vector Program c.generators.size) :
    (c.reword words).generators = c.generators := by cases c <;> rfl

@[simp] theorem words_reword (c : Chain n) (words : Vector Program c.generators.size) :
    (c.reword words).words.toArray = words.toArray := by cases c <;> rfl

@[simp] theorem checkWords_reword (S : Array (Perm n)) (c : Chain n)
    (words : Vector Program c.generators.size) :
    checkWords S (c.reword words).generators (c.reword words).words =
      checkWords S c.generators words := by cases c <;> rfl

/-- Strict lexicographic order of permutation image arrays. -/
@[expose] def before (p q : Perm n) : Prop :=
  compare (p.vec.toList.map Fin.val) (q.vec.toList.map Fin.val) = Ordering.lt

instance (p q : Perm n) : Decidable (before p q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The normalized working-array invariants, checked independently of sorting. -/
@[expose] def Working (S : Array (Perm n)) : Prop :=
  S.toList.Pairwise before ∧ S.toList.Nodup ∧
  ∀ i : Fin S.size, S[i.val] ≠ Perm.id n ∧ S[i.val].inv ∈ S

instance (S : Array (Perm n)) : Decidable (Working S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Every level generator fixes all preceding points of the fixed base. -/
@[expose] def Fixed (base : Nat) (S : Array (Perm n)) : Prop :=
  ∀ i : Fin S.size, ∀ x : Fin n, x.val < base → S[i.val].get x = x

instance (base : Nat) (S : Array (Perm n)) : Decidable (Fixed base S) :=
  inferInstanceAs (Decidable (∀ _ : Fin S.size, ∀ _ : Fin n, _ → _))

/-- The initial working array is exactly the sorted, deduplicated nonidentity
input generators and their inverses. Original indices are retained by the separate
provenance programs. -/
@[expose] def Normalized (S T : Array (Perm n)) : Prop :=
  Working T ∧
  (∀ j : Fin T.size, ∃ i : Fin S.size, T[j.val] = S[i.val] ∨ T[j.val] = S[i.val].inv) ∧
  ∀ i : Fin S.size, S[i.val] = Perm.id n ∨ S[i.val] ∈ T

instance (S T : Array (Perm n)) : Decidable (Normalized S T) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Complete suffix checking. Each level recomputes every Schreier generator;
no producer-supplied list is used as evidence that all pairs were considered. -/
@[expose] def checkFrom : Chain n → Nat → Bool
  | .leaf S _, base =>
    decide (base = n ∧ Fixed base S ∧
      ∀ i : Fin S.size, S[i.val] = Perm.id n)
  | .cons level tail, base =>
    if hb : base < n then
      if h : level.orbit.Valid level.generators ⟨base, hb⟩ then
        let family := Orbit.stabilizerGens h
        decide (Working level.generators ∧ Fixed base level.generators ∧
          checkWords level.generators tail.generators tail.words = true ∧
          tail.checkFrom (base + 1) = true ∧
          ∀ j : Fin family.size,
            tail.accepts (base + 1) family[j.val] = true)
      else false
    else false

/-- Changing top-level provenance preserves the independently checked suffix. -/
@[simp] theorem checkFrom_reword (c : Chain n) (words : Vector Program c.generators.size)
    (base : Nat) : (c.reword words).checkFrom base = c.checkFrom base := by
  cases c <;> rfl

/-- Accepted suffixes retain the fixed-point conditions, including at the terminal stage. -/
theorem checkFrom_fixed {c : Chain n} {base : Nat} (h : c.checkFrom base = true) :
    Fixed base c.generators := by
  cases c with
  | leaf S words => exact (of_decide_eq_true h).2.1
  | cons level tail =>
    unfold checkFrom at h
    split at h
    · split at h
      · exact (of_decide_eq_true h).2.1
      · cases h
    · cases h

/-- Completeness checking enforces the full base length. -/
theorem checkFrom_length {c : Chain n} {base : Nat} (h : c.checkFrom base = true) :
    base + c.length = n := by
  induction c generalizing base with
  | leaf S words => exact (of_decide_eq_true h).1
  | cons level tail ih =>
    unfold checkFrom at h
    split at h
    · split at h
      · have ht := ih (of_decide_eq_true h).2.2.2.1
        simp only [length]
        omega
      · cases h
    · cases h

/-- Successful and failed sifts are exact membership decisions after complete
suffix verification. The induction uses only the already checked suffix when
interpreting its Schreier-pair sifts as membership evidence. -/
theorem checkFrom_sound {c : Chain n} {base : Nat} (h : c.checkFrom base = true)
    (p : Perm n) : c.accepts base p = true ↔ Generated c.generators p := by
  induction c generalizing base p with
  | leaf S words =>
    have hall := (of_decide_eq_true h).2.2
    rw [accepts_leaf]
    simp only [decide_eq_true_eq, generators]
    constructor
    · rintro rfl
      exact .id
    · intro hp
      apply hp.lift (P := fun q => q = Perm.id n) rfl
      · intro q hq
        rcases Array.mem_iff_getElem.mp hq with ⟨i, hi, rfl⟩
        exact hall ⟨i, hi⟩
      · intro q r hq hr
        simp [hq, hr]
      · intro q hq
        simp [hq]
  | cons level tail ih =>
    unfold checkFrom at h
    split at h
    · next hb =>
      split at h
      · next ho =>
        have parts := of_decide_eq_true h
        have ht := parts.2.2.2.1
        have hfixed := checkFrom_fixed ht
        have hstab (q : Perm n) : Generated tail.generators q ↔
            Generated level.generators q ∧ q.get ⟨base, hb⟩ = ⟨base, hb⟩ := by
          constructor
          · intro hq
            apply hq.lift
            · exact ⟨.id, Perm.get_id _⟩
            · intro r hr
              refine ⟨checkWords_sound parts.2.2.1 (.generator hr), ?_⟩
              rcases Array.mem_iff_getElem.mp hr with ⟨i, hi, rfl⟩
              exact hfixed ⟨i, hi⟩ ⟨base, hb⟩ (Nat.lt_succ_self base)
            · intro r t hr ht
              exact ⟨.comp hr.1 ht.1, by simp [hr.2, ht.2]⟩
            · intro r hr
              refine ⟨.inv hr.1, ?_⟩
              apply r.get_inj
              simp [hr.2]
          · intro hq
            apply ((Orbit.stabilizerGens_spec ho q).mpr hq).mono
            intro r hr
            rcases Array.mem_iff_getElem.mp hr with ⟨j, hj, rfl⟩
            exact (ih ht _).mp (parts.2.2.2.2 ⟨j, hj⟩)
        rw [accepts_cons]
        simp only [dite_eq_left hb, generators]
        cases hl : level.orbit.lookup[(p.get ⟨base, hb⟩).val] with
        | none =>
          simp only [Bool.false_eq_true, false_iff]
          intro hp
          have hm := (ho.invariant hp ⟨base, hb⟩).mp ho.2.1
          exact ((ho.2.2.2.1 (p.get ⟨base, hb⟩)).1.mp hl) hm
        | some x =>
          rw [ih ht, hstab]
          constructor
          · intro hr
            have hp := Generated.comp (Orbit.rep_generated ho x) hr.1
            have he : level.orbit.reps[x.val].comp
                (level.orbit.reps[x.val].inv.comp p) = p := by
              apply Perm.ext
              intro i
              simp
            simpa only [he] using hp
          · intro hp
            refine ⟨.comp (.inv (Orbit.rep_generated ho x)) hp, ?_⟩
            apply level.orbit.reps[x.val].get_inj
            simp only [Perm.get_comp, Perm.get_inv_get, Orbit.rep_apply ho x]
            exact ((ho.2.2.2.1 (p.get ⟨base, hb⟩)).2 x hl).symm
      · cases h
    · cases h

end Chain

/-- A complete chain for precisely the original input generators. -/
@[expose] def checkChain (S : Array (Perm n)) (c : Chain n) : Bool :=
  decide (Chain.Normalized S c.generators ∧
    checkWords S c.generators c.words = true ∧ c.checkFrom 0 = true)

/-- A checked chain has exactly one level for every point of the fixed base. -/
theorem checkChain_length {S : Array (Perm n)} {c : Chain n}
    (h : checkChain S c = true) : c.length = n := by
  simpa using Chain.checkFrom_length (of_decide_eq_true h).2.2

/-- Complete checking makes sifting equivalent to membership in the original
generated subgroup, for every query permutation. -/
theorem sift_iff {S : Array (Perm n)} {c : Chain n}
    (h : checkChain S c = true) (p : Perm n) :
    c.accepts 0 p = true ↔ Generated S p := by
  have hc := of_decide_eq_true h
  rw [Chain.checkFrom_sound hc.2.2]
  constructor
  · exact checkWords_sound hc.2.1
  · intro hp
    apply hp.mono
    intro q hq
    rcases Array.mem_iff_getElem.mp hq with ⟨i, hi, rfl⟩
    rcases hc.1.2.2 ⟨i, hi⟩ with hid | hmem
    · rw [hid]
      exact .id
    · exact .generator hmem

/-- Membership soundness of a complete-chain check. -/
theorem checkChain_sound {S : Array (Perm n)} {c : Chain n}
    (h : checkChain S c = true) {p : Perm n} (hp : c.accepts 0 p = true) :
    Generated S p :=
  (sift_iff h p).mp hp

end Hex.PermGroup
