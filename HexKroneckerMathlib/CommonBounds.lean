/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.MatrixBounds

public section

namespace Hex.Kronecker

/-- The common box contains this bound, including its coefficient bound. -/
@[expose] def Bounds.Covers (b a : Bounds) : Prop :=
  (∀ i, a.degrees.getD i 0 ≤ b.degrees.getD i 0) ∧ a.height ≤ b.height

theorem Bounds.Covers.trans {a b c : Bounds} (h : c.Covers b) (g : b.Covers a) : c.Covers a :=
  ⟨fun i => (g.1 i).trans (h.1 i), g.2.trans h.2⟩

theorem Bounds.sup_left (a b : Bounds) : (a.sup b).Covers a := by
  constructor
  · intro i; simp only [Bounds.sup, getD_maxDegrees]; exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _

theorem Bounds.sup_right (a b : Bounds) : (a.sup b).Covers b := by
  constructor
  · intro i; simp only [Bounds.sup, getD_maxDegrees]; exact Nat.le_max_right _ _
  · exact Nat.le_max_right _ _

theorem Bounds.add_left (cap : Nat) (a b : Bounds) (ha : a.height ≤ cap) : (a.add cap b).Covers a := by
  constructor
  · intro i; simp only [Bounds.add, getD_maxDegrees]; exact Nat.le_max_left _ _
  · exact Saturating.le_add_left cap _ _ ha

theorem Bounds.add_right (cap : Nat) (a b : Bounds) (hb : b.height ≤ cap) : (a.add cap b).Covers b := by
  constructor
  · intro i; simp only [Bounds.add, getD_maxDegrees]; exact Nat.le_max_right _ _
  · exact Saturating.le_add_right cap _ _ hb

theorem bounded_data {cap k : Nat} {bs : List Bounds} {ps : List (MvPolynomial (Fin k) Int)}
    (h : List.Forall₂ (Bounded cap) bs ps) : ∀ b ∈ bs, b.degrees.length = k ∧ b.height ≤ cap := by
  induction h with
  | nil => simp
  | cons h ht ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨h.length,h.capped⟩
      · exact ih b hb

theorem commonBounds_spec (cap k : Nat) (as bs : List Bounds) (hl : as.length = bs.length)
    (ha : ∀ a ∈ as, a.degrees.length = k ∧ a.height ≤ cap)
    (hb : ∀ b ∈ bs, b.degrees.length = k ∧ b.height ≤ cap) :
    (commonBounds cap k as bs).degrees.length = k ∧
      ∀ b ∈ as ++ bs, (commonBounds cap k as bs).Covers b := by
  induction as generalizing bs with
  | nil =>
      have : bs = [] := List.length_eq_zero_iff.mp hl.symm
      subst bs
      simp [commonBounds, Bounds.zero]
  | cons a as ih =>
      cases bs with
      | nil => simp at hl
      | cons b bs =>
          have ha₀ := ha a (by simp)
          have hb₀ := hb b (by simp)
          have ht := ih bs (by simpa using hl) (fun a h => ha a (by simp [h]))
            (fun b h => hb b (by simp [h]))
          constructor
          · simp [commonBounds, Bounds.sup, Bounds.add, ha₀.1, hb₀.1, ht.1]
          · intro c hc
            have hleft := Bounds.sup_left (a.add cap b) (commonBounds cap k as bs)
            have hright := Bounds.sup_right (a.add cap b) (commonBounds cap k as bs)
            rcases List.mem_append.mp hc with hc | hc
            · rcases List.mem_cons.mp hc with rfl | hc
              · exact hleft.trans (Bounds.add_left cap c b ha₀.2)
              · exact hright.trans (ht.2 c (List.mem_append_left _ hc))
            · rcases List.mem_cons.mp hc with rfl | hc
              · exact hleft.trans (Bounds.add_right cap a c hb₀.2)
              · exact hright.trans (ht.2 c (List.mem_append_right _ hc))

theorem commonBounds_length (cap k : Nat) (as bs : List Bounds)
    (ha : ∀ a ∈ as, a.degrees.length = k) (hb : ∀ b ∈ bs, b.degrees.length = k) :
    (commonBounds cap k as bs).degrees.length = k := by
  induction as generalizing bs with
  | nil => simp [commonBounds, Bounds.zero]
  | cons a as ih =>
      cases bs with
      | nil => simp [commonBounds, Bounds.zero]
      | cons b bs =>
          simp only [commonBounds, Bounds.sup, Bounds.add, length_maxDegrees,
            ha a (by simp), hb b (by simp),
            ih bs (fun a h => ha a (by simp [h])) (fun b h => hb b (by simp [h])), Nat.max_self]

theorem withMode_accept (s : SizeBound) (budget : Budget) (mode : MulMode) (r : Nat)
    (hs : s.packedBits = s.innerBits)
    (h : (s.withMode budget mode r).accepts budget = true) : s.accepts budget = true := by
  cases mode with
  | plain => exact h
  | signedPacked =>
      have h := Bool.and_eq_true_iff.mp h
      apply Bool.and_eq_true_iff.mpr
      refine ⟨h.1, ?_⟩
      have hbit : min (max s.innerBits (2*r*(if r == 0 then 0 else r.log2+2*(s.innerBits-1)+1)+2))
          (budget.maxPackedBits+1) ≤ budget.maxPackedBits := of_decide_eq_true h.2
      apply decide_eq_true
      rw [hs]
      omega

theorem bounded_lists (budget : Budget) (observed : List Bounds) {k : Nat}
    {as bs : List Bounds} {ps qs : List (MvPolynomial (Fin k) Int)}
    (ha : List.Forall₂ (Bounded (2^budget.maxPackedBits)) as ps)
    (hb : List.Forall₂ (Bounded (2^budget.maxPackedBits)) bs qs)
    (ham : ∀ a ∈ as, a ∈ observed) (hbm : ∀ b ∈ bs, b ∈ observed)
    (hacc : (makeSize budget (commonBounds (2^budget.maxPackedBits) k as bs) observed).accepts budget = true)
    (he : let s := makeSize budget (commonBounds (2^budget.maxPackedBits) k as bs) observed
      List.Forall₂ (fun p q =>
        MvPolynomial.eval₂Hom (RingHom.id Int)
          (fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0) p =
        MvPolynomial.eval₂Hom (RingHom.id Int)
          (fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0) q) ps qs) : ps = qs := by
  have hl : as.length = bs.length := ha.length_eq.trans (he.length_eq.trans hb.length_eq.symm)
  have hc := commonBounds_spec _ k as bs hl (bounded_data ha) (bounded_data hb)
  apply List.ext_getElem he.length_eq
  intro i hip hiq
  have hia : i < as.length := by simpa only [ha.length_eq] using hip
  have hib : i < bs.length := by simpa only [hb.length_eq] using hiq
  have hap := ha.get hia hip
  have hbq := hb.get hib hiq
  have hac := hc.2 as[i] (List.mem_append_left _ (List.getElem_mem hia))
  have hbc := hc.2 bs[i] (List.mem_append_right _ (List.getElem_mem hib))
  apply bounded_injective budget _ observed hacc hap hbq
    (ham _ (List.getElem_mem hia)) (hbm _ (List.getElem_mem hib)) hc.1
    (fun i => hac.1 i.val) (fun i => hbc.1 i.val) hac.2 hbc.2
  simpa only [makeSize, Nat.cast_pow, Nat.cast_ofNat] using he.get hip hiq

end Hex.Kronecker
