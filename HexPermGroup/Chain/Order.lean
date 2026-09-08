/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Check

public section

namespace Hex.PermGroup.Chain

/-- One representative choice at each chain level. -/
@[expose] def Choice : Chain n → Type
  | .leaf _ _ => PUnit
  | .cons level tail => Fin level.orbit.points.size × tail.Choice

/-- Multiply the selected representatives in sifting order, with level zero
on the left. No group elements are enumerated. -/
@[expose] def value : (c : Chain n) → c.Choice → Perm n
  | .leaf _ _, _ => Perm.id n
  | .cons level tail, digits => level.orbit.reps[digits.1.val].comp (tail.value digits.2)

/-- Fixed-point conditions on generators extend to the whole generated subgroup. -/
theorem fixed_generated {S : Array (Perm n)} {base : Nat} (h : Fixed base S)
    {p : Perm n} (hp : Generated S p) (x : Fin n) (hx : x.val < base) : p.get x = x := by
  apply hp.lift (P := fun q => q.get x = x) (Perm.get_id x)
  · intro q hq
    rcases Array.mem_iff_getElem.mp hq with ⟨i, hi, rfl⟩
    exact h ⟨i, hi⟩ x hx
  · intro q r hq hr
    simp [hq, hr]
  · intro q hq
    apply q.get_inj
    simp [hq]

/-- Every Cartesian choice is an element of the checked suffix group. -/
theorem value_generated {c : Chain n} {base : Nat} (h : c.checkFrom base = true)
    (digits : c.Choice) : Generated c.generators (c.value digits) := by
  induction c generalizing base with
  | leaf S words => exact .id
  | cons level tail ih =>
    unfold checkFrom at h
    split at h
    · split at h
      · next ho =>
        have parts := of_decide_eq_true h
        exact .comp (Orbit.rep_generated ho digits.1)
          (checkWords_sound parts.2.2.1 (ih parts.2.2.2.1 digits.2))
      · cases h
    · cases h

/-- Distinct orbit choices give distinct permutations. The first differing
choice is detected at that level's base point. -/
theorem value_injective {c : Chain n} {base : Nat} (h : c.checkFrom base = true)
    {u v : c.Choice} (he : c.value u = c.value v) : u = v := by
  induction c generalizing base with
  | leaf S words => cases u; cases v; rfl
  | cons level tail ih =>
    unfold checkFrom at h
    split at h
    · next hb =>
      split at h
      · next ho =>
        have parts := of_decide_eq_true h
        have ht := parts.2.2.2.1
        have hu := fixed_generated (checkFrom_fixed ht) (value_generated ht u.2)
          ⟨base, hb⟩ (Nat.lt_succ_self base)
        have hv := fixed_generated (checkFrom_fixed ht) (value_generated ht v.2)
          ⟨base, hb⟩ (Nat.lt_succ_self base)
        have hpoint := congrArg (fun p : Perm n => p.get ⟨base, hb⟩) he
        simp only [value, Perm.get_comp, hu, hv, Orbit.rep_apply ho] at hpoint
        have hfirst := Orbit.point_injective ho hpoint
        apply Prod.ext hfirst
        apply ih ht
        apply Perm.ext
        intro x
        have hx := congrArg (fun p : Perm n => p.get x) he
        simp only [value, Perm.get_comp, hfirst] at hx
        exact level.orbit.reps[v.1.val].get_inj hx
      · cases h
    · cases h

/-- Every member is a product of orbit representatives, obtained by sifting. -/
theorem value_surjective {c : Chain n} {base : Nat} (h : c.checkFrom base = true)
    {p : Perm n} (hp : Generated c.generators p) :
    ∃ digits : c.Choice, c.value digits = p := by
  induction c generalizing base p with
  | leaf S words =>
    have hs := (checkFrom_sound h p).mpr hp
    simp only [accepts_leaf, decide_eq_true_eq] at hs
    exact ⟨PUnit.unit, hs.symm⟩
  | cons level tail ih =>
    have hs := (checkFrom_sound h p).mpr hp
    unfold checkFrom at h
    split at h
    · next hb =>
      split at h
      · next ho =>
        have parts := of_decide_eq_true h
        rw [accepts_cons] at hs
        simp only [dite_eq_left hb] at hs
        cases hl : level.orbit.lookup[(p.get ⟨base, hb⟩).val] with
        | none => simp only [hl, Bool.false_eq_true] at hs
        | some x =>
          simp only [hl] at hs
          have hg := (checkFrom_sound parts.2.2.2.1 _).mp hs
          obtain ⟨rest, hr⟩ := ih parts.2.2.2.1 hg
          refine ⟨(x, rest), ?_⟩
          simp only [value, hr]
          apply Perm.ext
          intro i
          simp
      · cases h
    · cases h

/-- Each radix is positive in a checked chain, including the empty product one. -/
theorem orbitProduct_pos {c : Chain n} {base : Nat} (h : c.checkFrom base = true) :
    0 < c.orbitProduct := by
  induction c generalizing base with
  | leaf S words => exact Nat.zero_lt_one
  | cons level tail ih =>
    unfold checkFrom at h
    split at h
    · split at h
      · next ho =>
        have parts := of_decide_eq_true h
        have ht := ih parts.2.2.2.1
        rcases Array.mem_iff_getElem.mp ho.2.1 with ⟨i, hi, _⟩
        exact Nat.mul_pos (by omega) ht
      · cases h
    · cases h

end Hex.PermGroup.Chain
