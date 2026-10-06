/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Kernel.Assemble

public section

namespace Hex.PermGroup

namespace Kernel

open Hex.Kernel

/-- Membership in the bitmask of fixed base points, with raw kernel operations. -/
@[expose] def fixedPoint (fixed i : Nat) : Bool :=
  !(Nat.beq (Nat.land (Nat.shiftRight fixed i) 1) 0)

private theorem fixedPoint_eq (fixed i : Nat) : fixedPoint fixed i = fixed.testBit i := by
  simp only [fixedPoint, Nat.testBit, land_eq, shiftRight_eq, Nat.and_comm]
  rfl

/-- Scan once for an unfixed point; a second unfixed point makes the verdict false. -/
@[expose] def scan (fixed bound k : Nat) : Nat × Bool :=
  Nat.rec (motive := fun _ => Nat × Bool) (bound, true)
    (fun i s => cond (fixedPoint fixed i) s (i, s.2 && Nat.beq s.1 bound)) k

private theorem scan_succ (fixed bound k : Nat) :
    scan fixed bound (k + 1) =
      cond (fixedPoint fixed k) (scan fixed bound k)
        (k, (scan fixed bound k).2 && Nat.beq (scan fixed bound k).1 bound) := rfl

private theorem scan_sound (fixed bound : Nat) : ∀ k, k ≤ bound →
    (scan fixed bound k).2 = true →
    ∀ i < k, fixedPoint fixed i = true ∨ i = (scan fixed bound k).1
  | 0, _, _, _, hi => by omega
  | k + 1, hk, hs, i, hi => by
    rw [scan_succ] at hs ⊢
    cases hf : fixedPoint fixed k with
    | false =>
      simp only [hf, Bool.cond_false, Bool.and_eq_true, beq_eq_decide,
        decide_eq_true_eq] at hs ⊢
      by_cases he : i = k
      · exact Or.inr he
      · rcases scan_sound fixed bound k (by omega) hs.1 i (by omega) with h | h
        · exact Or.inl h
        · rw [hs.2] at h
          omega
    | true =>
      simp only [hf, Bool.cond_true] at hs ⊢
      by_cases he : i = k
      · exact Or.inl (he ▸ hf)
      · exact scan_sound fixed bound k (by omega) hs i (by omega)

/-- Coverage and fixed-point checks for one certified orbit and transversal. -/
@[expose] def fullLevel (n fixed : Nat) (L : Level) : Bool :=
  allRange n (fun i => fixedPoint fixed i || !(Nat.beq (field (width n) L.lookup i) 0)) &&
  allRange L.size (fun j => allRange n fun i =>
    !(fixedPoint fixed i) || Nat.beq (field (width n) (L.reps.get j) i) i)

/-- Check that the certificate covers every permutation fixing the bitmask
`fixed`. Each orbit covers its unfixed points, its transversal fixes `fixed`,
and a single terminal scan leaves at most one point unfixed. -/
@[expose] def full (n fixed : Nat) : Certificate → Bool
  | [] => (scan fixed n n).2
  | L :: rest => fullLevel n fixed L && full n (Nat.lor fixed (Nat.shiftLeft 1 L.base)) rest

/-- Assemble independently checked coverage levels. -/
theorem full_cons_of {n fixed : Nat} {L : Level} {rest : Certificate}
    (hL : fullLevel n fixed L = true)
    (hrest : full n (Nat.lor fixed (Nat.shiftLeft 1 L.base)) rest = true) :
    full n fixed (L :: rest) = true := by
  simp only [full, hL, hrest, Bool.and_self]

private theorem full_sound : ∀ (ls : Certificate) (fixed : Nat),
    levelsOk n (width n) (ident n (width n)) ls = true →
    (∀ s ∈ headGens ls, ∃ σ, Rep n s σ) →
    full n fixed ls = true → ∀ p : Perm n,
    (∀ i : Fin n, fixedPoint fixed i.val = true → p.get i = i) → groupOf n ls p
  | [], fixed, _, _, hf, p, hp => by
    apply Span.empty.mpr
    apply Perm.ext
    intro i
    simp only [Perm.get_id]
    by_cases hi : fixedPoint fixed i.val = true
    · exact hp i hi
    · have hpi : fixedPoint fixed (p.get i).val ≠ true := by
        intro hm
        have he := p.get_inj (hp (p.get i) hm).symm
        exact hi (he ▸ hm)
      have hscan := scan_sound fixed n n (Nat.le_refl n) hf
      rcases hscan i.val i.isLt with hm | he
      · exact False.elim (hi hm)
      rcases hscan (p.get i).val (p.get i).isLt with hm | hpe
      · exact False.elim (hpi hm)
      · exact Fin.ext (hpe.trans he.symm)
  | L :: rest, fixed, hok, hgens, hf, p, hp => by
    obtain ⟨⟨hs, hi, ht, hn⟩, hpair, hrest⟩ := levelsOk_cons.mp hok
    have base : LevelBase n L rest := ⟨hs, hi, ht, hn, hpair, hgens⟩
    have hgens' : ∀ s ∈ headGens rest, ∃ σ, Rep n s σ := by
      match hr : rest with
      | [] => simp [headGens]
      | L' :: rest' =>
        intro s hm
        obtain ⟨τ, hτ, -⟩ := base.next_gens rfl hm
        exact ⟨τ, hτ⟩
    have hyp : LevelHyp n L rest := { base with sift := (levels_sound rest hrest hgens').1 }
    simp only [full, fullLevel, Bool.and_eq_true, allRange_iff,
      Bool.or_eq_true, Bool.not_eq_true', beq_eq_decide,
      decide_eq_true_eq, decide_eq_false_iff_not] at hf
    obtain ⟨⟨hcover, hfix⟩, htail⟩ := hf
    let b : Fin n := ⟨L.base, base.base_lt⟩
    have hm : base.Ω (p.get b) := by
      by_cases hb : fixedPoint fixed b.val = true
      · rw [hp b hb]
        exact hyp.base_mem
      · rcases hcover (p.get b).val (p.get b).isLt with hm | hm
        · have he := p.get_inj (hp (p.get b) hm).symm
          exact False.elim (hb (he ▸ hm))
        · exact hm
    let j := base.idx (p.get b)
    have hj : j < L.size := base.idx_lt hm
    let q := (base.tr j).inv.comp p
    have hqb : q.get b = b := by
      apply (base.tr j).get_inj
      simp only [q, Perm.get_comp, Perm.get_inv_get]
      rw [base.tr_apply hj, base.pt_idx hm]
    have hqfix : ∀ i : Fin n, fixedPoint (Nat.lor fixed (Nat.shiftLeft 1 L.base)) i.val = true → q.get i = i := by
      intro i hi
      simp only [fixedPoint_eq, lor_eq, shiftLeft_eq, Nat.one_shiftLeft,
        Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hi
      rcases hi with hi | he
      · have hi : fixedPoint fixed i.val = true := (fixedPoint_eq ..).trans hi
        have hti : (base.tr j).get i = i := by
          rcases hfix j hj i.val i.isLt with hn | he
          · exact False.elim (Bool.false_ne_true (hn.symm.trans hi))
          · exact Fin.ext ((base.rep_reps hj i).symm.trans he)
        apply (base.tr j).get_inj
        simp only [q, Perm.get_comp, Perm.get_inv_get, hp i hi, hti]
      · have hib : i = b := Fin.ext he.symm
        simpa only [hib] using hqb
    have hq := full_sound rest (Nat.lor fixed (Nat.shiftLeft 1 L.base)) hrest hgens' htail q hqfix
    have hprod := Span.comp (base.tr_mem hj) (hyp.rest_le hq).1
    have he : (base.tr j).comp q = p := by
      ext i
      simp [q]
    rwa [he] at hprod

/-- A full accepted certificate proves that every permutation is generated. -/
theorem all_of_check {gs : List (Perm n)} {inputs : List Nat} {c : Certificate}
    (hS : gs.map pack = inputs) (h : check n inputs c = true)
    (hf : full n 0 c = true) : GeneratesAll gs.toArray := by
  have hc := check_list hS h
  obtain ⟨hin, hlv⟩ := (check_iff _ _).mp hc
  have hgens : ∀ s ∈ headGens c, ∃ σ, Rep n s σ := by
    intro s hs
    simp only [inputsOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
      List.mem_map, Bool.or_eq_true, beq_eq_decide, decide_eq_true_eq] at hin
    obtain ⟨_, ⟨p, _, rfl⟩, hp⟩ := hin.2 s hs
    rcases hp with rfl | hp
    · exact ⟨p, rep_pack p⟩
    · exact ⟨p.inv, rep_inv (rep_pack p) hp⟩
  intro p
  exact (groupOf_iff_generated hc p).mp
    (full_sound c 0 hlv hgens hf p (by simp [fixedPoint]))

end Kernel
end Hex.PermGroup
