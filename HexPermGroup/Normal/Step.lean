/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Check
public import HexPermGroup.Group.Adjoin

public section

namespace Hex.PermGroup.Normal

/-- An untrusted normal-closure insertion names an ambient symmetric generator,
a current subgroup generator, and the complete chain after adjoining their
conjugate. The next generator array is reconstructed by the checker. -/
structure Step (n : Nat) where
  conjugator : Nat
  source : Nat
  chain : Chain n

/-- Check a strict, forced conjugate insertion. Arbitrary extra generators
cannot enter through the supplied chain. -/
@[expose] def step (G H : Group n) (s : Step n) : Option (Group n) :=
  if hi : s.conjugator < G.chain.generators.size then
    if hj : s.source < H.generators.size then
      let p := G.chain.generators[s.conjugator].conj H.generators[s.source]
      if H.contains p then none
      else
        if hc : checkChain (H.generators.push p) s.chain = true then
          some ⟨H.generators.push p, s.chain, hc⟩
        else none
    else none
  else none

theorem step_spec {G H K : Group n} {s : Step n} (h : step G H s = some K) :
    ∃ (i : Fin G.chain.generators.size) (j : Fin H.generators.size),
      SameGroup K (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])) ∧
        ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val]) := by
  unfold step at h
  split at h
  · rename_i hi
    split at h
    · rename_i hj
      dsimp only at h
      split at h
      · contradiction
      · rename_i hp
        split at h
        · have he := Option.some.inj h
          subst K
          refine ⟨⟨s.conjugator, hi⟩, ⟨s.source, hj⟩, fun _ => Iff.rfl, ?_⟩
          intro hg
          exact hp ((H.contains_iff _).mpr hg)
        · contradiction
    · contradiction
  · contradiction

theorem step_adjoin (G H : Group n) (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (h : ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val])) :
    let p := G.chain.generators[i.val].conj H.generators[j.val]
    step G H ⟨i.val, j.val, (H.adjoin p).chain⟩ = some (H.adjoin p) := by
  dsimp only
  have hc : H.contains (G.chain.generators[i.val].conj H.generators[j.val]) = false :=
    Bool.eq_false_iff.mpr (fun hp => h ((H.contains_iff _).mp hp))
  have hv : checkChain (H.generators.push (G.chain.generators[i.val].conj H.generators[j.val]))
      (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])).chain = true := by
    simpa only [Group.adjoin, Group.generators_ofGenerators] using
      (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])).valid
  simp only [step, i.isLt, j.isLt, dite_true, hc, Bool.false_eq_true, ite_false]
  rw [dite_eq_left hv]
  rfl

theorem step_grows {G H K : Group n} {s : Step n} (h : step G H s = some K) : H.IsSubgroup K := by
  obtain ⟨i, j, he, _⟩ := step_spec h
  intro p hp
  exact (he p).mpr (H.subgroup_adjoin _ p hp)

theorem step_least {G H K N : Group n} {s : Step n} (h : step G H s = some K)
    (hH : H.IsSubgroup N) (hN : check G N = true) : K.IsSubgroup N := by
  obtain ⟨i, j, he, _⟩ := step_spec h
  have hc := (check_iff G N).mp hN _ _
    ((G.chain_generated _).mp (.generator (Array.getElem_mem i.isLt)))
    (hH _ (.generator (Array.getElem_mem j.isLt)))
  have ha := (H.adjoin_le N _).mpr ⟨hH, hc⟩
  exact fun p hp => ha p ((he p).mp hp)

theorem step_inside {G H K : Group n} {s : Step n} (h : step G H s = some K)
    (hH : H.IsSubgroup G) : K.IsSubgroup G := by
  apply step_least h hH
  apply (check_iff G G).mpr
  intro g p hg hp
  exact hg.comp (hp.comp hg.inv)

theorem step_double {G H K : Group n} {s : Step n} (h : step G H s = some K) :
    2 * H.order ≤ K.order := by
  obtain ⟨i, j, he, hn⟩ := step_spec h
  rw [he.order_eq]
  exact H.order_adjoin _ hn

/-- Replay each complete chain and forced conjugate, preserving the exact
generator order at every stage. -/
@[expose] def replay (G H : Group n) : List (Step n) → Option (Group n)
  | [] => some H
  | s :: rest => (step G H s).bind fun K => replay G K rest

theorem replay_least {G H K N : Group n} {trace : List (Step n)}
    (h : replay G H trace = some K) (hH : H.IsSubgroup N) (hN : check G N = true) : K.IsSubgroup N := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; exact hH
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    exact ih ht (step_least hL hH hN)

theorem replay_inside {G H K : Group n} {trace : List (Step n)}
    (h : replay G H trace = some K) (hH : H.IsSubgroup G) : K.IsSubgroup G := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; exact hH
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    exact ih ht (step_inside hL hH)

theorem replay_grows {G H K : Group n} {trace : List (Step n)}
    (h : replay G H trace = some K) : H.IsSubgroup K := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; exact fun _ hp => hp
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    exact fun p hp => ih ht p (step_grows hL p hp)

/-- Every replayed element belongs to any subgroup predicate containing the
input and closed under ambient conjugation. This also applies to subgroups
that have no computational generator presentation. -/
theorem replay_lift {G H K : Group n} {trace : List (Step n)} {P : Perm n → Prop}
    (h : replay G H trace = some K) (hid : P (Perm.id n))
    (hmul : ∀ p q, P p → P q → P (p.comp q)) (hinv : ∀ p, P p → P p.inv)
    (hconj : ∀ g p, Generated G.generators g → P p → P (g.conj p))
    (hH : ∀ p, Generated H.generators p → P p) :
    ∀ p, Generated K.generators p → P p := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; exact hH
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    apply ih ht
    obtain ⟨i, j, he, _⟩ := step_spec hL
    intro p hp
    apply ((he p).mp hp).lift hid ?_ hmul hinv
    intro q hq
    simp only [Group.adjoin, Group.generators_ofGenerators, Array.mem_push] at hq
    rcases hq with hq | rfl
    · exact hH q (.generator hq)
    · exact hconj _ _ ((G.chain_generated _).mp (.generator (Array.getElem_mem i.isLt)))
        (hH _ (.generator (Array.getElem_mem j.isLt)))

/-- The replay trace grows by a factor of at least two at each step. -/
theorem replay_growth {G H K : Group n} {trace : List (Step n)}
    (h : replay G H trace = some K) : 2 ^ trace.length * H.order ≤ K.order := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; simp
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    have hd := Nat.mul_le_mul_left (2 ^ trace.length) (step_double hL)
    have hh := Nat.le_trans hd (ih ht)
    simpa only [List.length_cons, Nat.pow_succ, Nat.mul_assoc] using hh

end Hex.PermGroup.Normal
