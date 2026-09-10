/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Scan

public section

namespace Hex.Perm.Cycle

theorem Valid.fixed_of_dvd {p : Perm n} {c : Array (Fin n)} (h : Valid p c)
    (k : Nat) (hk : c.size ∣ k) (x : Fin n) (hx : x ∈ c) : (p.pow k).get x = x := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [h.pow_get k i hi]
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hk, Nat.mod_eq_of_lt hi]

theorem Valid.fixed_iff {p : Perm n} {c : Array (Fin n)} (h : Valid p c)
    (x : Fin n) (hx : x ∈ c) : p.get x = x ↔ c.size = 1 := by
  constructor
  · intro he
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    have hp := (h.get i hi).symm.trans he
    have hm := get_injective h.1 (Nat.mod_lt _ h.nonempty) hi hp
    by_cases hs : i + 1 < c.size
    · rw [Nat.mod_eq_of_lt hs] at hm
      omega
    · have hs' : i + 1 = c.size := by omega
      rw [hs', Nat.mod_self] at hm
      omega
  · intro he
    have hp := h.period x hx
    simpa [he] using hp

theorem lcm_fold_dvd (cs : List (Array (Fin n))) (a k : Nat) :
    cs.foldl (fun j c => Nat.lcm j c.size) a ∣ k ↔ a ∣ k ∧ ∀ c ∈ cs, c.size ∣ k := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih => simp [ih, Nat.lcm_dvd_iff, and_assoc]

theorem lcm_fold_pos (cs : List (Array (Fin n))) (a : Nat) (ha : 0 < a)
    (hc : ∀ c ∈ cs, 0 < c.size) : 0 < cs.foldl (fun j c => Nat.lcm j c.size) a := by
  induction cs generalizing a with
  | nil => exact ha
  | cons c cs ih =>
    exact ih _ (Nat.lcm_pos ha (hc c (by simp))) (fun d hd => hc d (by simp [hd]))

end Hex.Perm.Cycle

namespace Hex.Perm

theorem cycles_valid (p : Perm n) (c : Array (Fin n)) (hc : c ∈ p.cycles) : Cycle.Valid p c :=
  p.allCycles_valid c (Array.mem_of_mem_filter hc)

/-- The serialized nontrivial cycles contain precisely the moved points. -/
theorem mem_cycles (p : Perm n) (x : Fin n) : (∃ c ∈ p.cycles, x ∈ c) ↔ p.get x ≠ x := by
  constructor
  · rintro ⟨c, hc, hx⟩ he
    have hs : 1 < c.size := by simpa [cycles] using (Array.mem_filter.mp hc).2
    have hf := ((p.cycles_valid c hc).fixed_iff x hx).mp he
    omega
  · intro hn
    obtain ⟨c, hc, hx⟩ := p.mem_allCycles x
    have hv := p.allCycles_valid c hc
    have hs : 1 < c.size := by
      have hp := hv.nonempty
      have hf : c.size ≠ 1 := fun he => hn ((hv.fixed_iff x hx).mpr he)
      omega
    exact ⟨c, by simpa [cycles, hc] using hs, hx⟩

/-- The serialized nontrivial cycles determine the permutation uniquely;
points absent from the serialization are fixed. -/
theorem cycles_ext (p q : Perm n) (h : p.cycles = q.cycles) : p = q := by
  apply Perm.ext
  intro x
  by_cases hp : p.get x = x
  · have hq : q.get x = x := by
      by_cases hq : q.get x = x
      · exact hq
      · obtain ⟨c, hc, hx⟩ := (q.mem_cycles x).mpr hq
        have hc' : c ∈ p.cycles := by rwa [h]
        exact False.elim (((p.mem_cycles x).mp ⟨c, hc', hx⟩) hp)
    exact hp.trans hq.symm
  · obtain ⟨c, hc, hx⟩ := (p.mem_cycles x).mpr hp
    have hc' : c ∈ q.cycles := by rwa [← h]
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    exact ((p.cycles_valid c hc).get i hi).trans ((q.cycles_valid c hc').get i hi).symm

theorem order_pos (p : Perm n) : 0 < p.order := by
  unfold order
  rw [← Array.foldl_toList]
  apply Cycle.lcm_fold_pos _ _ (by decide)
  intro c hc
  exact (p.cycles_valid c (by simpa using hc)).nonempty

/-- A number is a multiple of the computed order exactly when it is a
multiple of every cycle length, including the omitted singleton cycles. -/
theorem order_dvd_iff (p : Perm n) (k : Nat) :
    p.order ∣ k ↔ ∀ c ∈ p.allCycles, c.size ∣ k := by
  unfold order
  rw [← Array.foldl_toList, Cycle.lcm_fold_dvd]
  simp only [Nat.one_dvd, true_and]
  constructor
  · intro h c hc
    by_cases hs : 1 < c.size
    · apply h c
      simpa [cycles, hc] using hs
    · have hp := (p.allCycles_valid c hc).nonempty
      have he : c.size = 1 := by omega
      simp [he]
  · intro h c hc
    apply h c
    have hc' : c ∈ p.cycles := by simpa using hc
    exact Array.mem_of_mem_filter hc'

/-- The lcm calculation recognizes exactly the exponents giving the identity. -/
theorem order_dvd_iff_pow (p : Perm n) (k : Nat) : p.order ∣ k ↔ p.pow k = Perm.id n := by
  rw [p.order_dvd_iff]
  constructor
  · intro h
    apply Perm.ext
    intro x
    obtain ⟨c, hc, hx⟩ := p.mem_allCycles x
    simpa using (p.allCycles_valid c hc).fixed_of_dvd k (h c hc) x hx
  · intro h c hc
    apply (p.allCycles_valid c hc).dvd_period k
    simp [h]

theorem pow_order (p : Perm n) : p.pow p.order = Perm.id n :=
  (p.order_dvd_iff_pow p.order).mp (Nat.dvd_refl _)

/-- No positive exponent smaller than the computed order gives the identity. -/
theorem order_minimal (p : Perm n) (k : Nat) (hk : 0 < k) (hp : p.pow k = Perm.id n) :
    p.order ≤ k := Nat.le_of_dvd hk ((p.order_dvd_iff_pow k).mpr hp)

theorem order_eq_one (p : Perm n) : p.order = 1 ↔ p = Perm.id n := by
  rw [← Nat.dvd_one, p.order_dvd_iff_pow]
  simp

end Hex.Perm
