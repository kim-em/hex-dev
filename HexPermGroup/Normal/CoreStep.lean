/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Check
public import HexPermGroup.Group.Order
public import HexPermGroup.Search.Intersection

public section

namespace Hex.PermGroup.Core

/-- Membership in every ambient conjugate of the input subgroup. -/
@[expose] def Member (G H : Group n) (p : Perm n) : Prop :=
  ∀ g, Generated G.generators g → Generated H.generators (g.conj p)

theorem Member.inside {G H : Group n} {p : Perm n} (h : Member G H p) :
    Generated H.generators p := by simpa using h (Perm.id n) .id

theorem Member.conj {G H : Group n} {p g : Perm n} (h : Member G H p)
    (hg : Generated G.generators g) : Member G H (g.conj p) := by
  intro q hq
  simpa only [Perm.comp_conj] using h (q.comp g) (hq.comp hg)

/-- A proposed strict intersection, with a checked group and a complete search
certificate. The conjugate is reconstructed from the ambient generator index. -/
structure Step (n : Nat) where
  conjugator : Nat
  conjugate : Chain n
  group : Group n
  certificate : Search.Certificate Unit

/-- Use inverse conjugation so that a failed normality test immediately
witnesses strict containment. Ambient chain generators are symmetric. -/
@[expose] def step (G H : Group n) (s : Step n) : Option (Group n) :=
  if hi : s.conjugator < G.chain.generators.size then
    if hc : checkChain (H.generators.map G.chain.generators[s.conjugator].inv.conj) s.conjugate = true then
      let C : Group n := ⟨H.generators.map G.chain.generators[s.conjugator].inv.conj, s.conjugate, hc⟩
      if Search.checkSearch (Search.Intersection.constraint H C)
          s.group s.certificate && !s.group.sameGroup H then some s.group
      else none
    else none
  else none

theorem step_spec {G H K : Group n} {s : Step n} (h : step G H s = some K) :
    ∃ i : Fin G.chain.generators.size,
      (∀ p, Generated K.generators p ↔ Generated H.generators p ∧
        Generated H.generators (G.chain.generators[i.val].conj p)) ∧ ¬SameGroup K H := by
  unfold step at h
  split at h
  · rename_i hi
    split at h
    · rename_i hC
      dsimp only at h
      split at h
      · rename_i hc
        cases Option.some.inj h
        simp only [Bool.and_eq_true] at hc
        have hh := hc
        refine ⟨⟨s.conjugator, hi⟩, ?_, ?_⟩
        · intro p
          rw [Search.checkSearch_spec _ _ _ hh.1 p]
          change Generated H.generators p ∧
            (Group.contains ⟨_, s.conjugate, hC⟩ p) = true ↔ _
          rw [Group.contains_iff]
          change Generated H.generators p ∧
            Generated (Group.conjugate G.chain.generators[s.conjugator].inv H).generators p ↔ _
          rw [Group.mem_conjugate]
          simp
        · intro he
          have ht := (s.group.sameGroup_iff H).mpr he
          simp [ht] at hh
      · contradiction
    · contradiction
  · contradiction

theorem step_inside {G H K : Group n} {s : Step n} (h : step G H s = some K) :
    K.IsSubgroup H := by
  obtain ⟨_, hs, _⟩ := step_spec h
  exact fun p hp => ((hs p).mp hp).1

theorem step_retains {G H K : Group n} {s : Step n} {P : Perm n → Prop}
    (h : step G H s = some K) (hH : ∀ p, P p → Generated H.generators p)
    (hc : ∀ g p, Generated G.generators g → P p → P (g.conj p)) :
    ∀ p, P p → Generated K.generators p := by
  obtain ⟨i, hs, _⟩ := step_spec h
  intro p hp
  exact (hs p).mpr ⟨hH p hp, hH _ (hc _ _
    ((G.chain_generated _).mp (.generator (Array.getElem_mem i.isLt))) hp)⟩

theorem step_double {G H K : Group n} {s : Step n} (h : step G H s = some K) :
    2 * K.order ≤ H.order := (step_inside h).order_double (step_spec h).choose_spec.2

@[expose] def replay (G H : Group n) : List (Step n) → Option (Group n)
  | [] => some H
  | s :: rest => (step G H s).bind fun K => replay G K rest

theorem replay_inside {G H K : Group n} {trace : List (Step n)}
    (h : replay G H trace = some K) : K.IsSubgroup H := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; exact fun _ hp => hp
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    exact fun p hp => step_inside hL p (ih ht p hp)

theorem replay_retains {G H K : Group n} {trace : List (Step n)} {P : Perm n → Prop}
    (h : replay G H trace = some K) (hH : ∀ p, P p → Generated H.generators p)
    (hc : ∀ g p, Generated G.generators g → P p → P (g.conj p)) :
    ∀ p, P p → Generated K.generators p := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; exact hH
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    exact ih ht (step_retains hL hH hc)

/-- Each strict intersection at least halves the group order. -/
theorem replay_growth {G H K : Group n} {trace : List (Step n)}
    (h : replay G H trace = some K) : 2 ^ trace.length * K.order ≤ H.order := by
  induction trace generalizing H with
  | nil => cases Option.some.inj h; simp
  | cons s trace ih =>
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, ht⟩ := h
    have hh := Nat.le_trans (Nat.mul_le_mul_left 2 (ih ht)) (step_double hL)
    simpa only [List.length_cons, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hh

end Hex.PermGroup.Core
