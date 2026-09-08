/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.CoreStep

public section

namespace Hex.PermGroup.Core

/-- Replay strict complete intersections and verify the final normality pass. -/
@[expose] def check (G H K : Group n) (trace : List (Step n)) : Bool :=
  match replay G H trace with
  | none => false
  | some L => L.sameGroup K && Normal.check G K

theorem check_spec {G H K : Group n} {trace : List (Step n)}
    (h : check G H K trace = true) (p : Perm n) :
    Generated K.generators p ↔ Member G H p := by
  unfold check at h
  split at h
  · contradiction
  · rename_i L hL
    simp only [Bool.and_eq_true] at h
    have he := (L.sameGroup_iff K).mp h.1
    constructor
    · intro hp g hg
      exact replay_inside hL _ ((he _).mpr ((Normal.check_iff G K).mp h.2 g p hg hp))
    · intro hp
      exact (he p).mp (replay_retains hL (fun _ hm => hm.inside)
        (fun _ _ hg hm => hm.conj hg) p hp)

/-- Complete replay data certifies both containment and maximality. -/
structure Result (G H : Group n) where
  group : Group n
  trace : List (Step n)
  replayed : replay G H trace = some group
  normal : Normal.check G group = true

namespace Result

variable {G H : Group n}

theorem checked (c : Result G H) : check G H c.group c.trace = true := by
  simp only [check, c.replayed, Bool.and_eq_true]
  exact ⟨(c.group.sameGroup_iff c.group).mpr (fun _ => Iff.rfl), c.normal⟩

theorem spec (c : Result G H) (p : Perm n) : Generated c.group.generators p ↔ Member G H p :=
  check_spec c.checked p

theorem inside (c : Result G H) : c.group.IsSubgroup H := replay_inside c.replayed

theorem greatest (c : Result G H) (N : Group n) (hN : N.IsSubgroup H) (hn : Normal.check G N = true) :
    N.IsSubgroup c.group := by
  intro p hp
  exact (c.spec p).mpr fun g hg => hN _ ((Normal.check_iff G N).mp hn g p hg hp)

theorem growth (c : Result G H) : 2 ^ c.trace.length * c.group.order ≤ H.order :=
  replay_growth c.replayed

@[expose] def prepend {G H K : Group n} (s : Step n) (hs : step G H s = some K)
    (child : Result G K) : Result G H where
  group := child.group
  trace := s :: child.trace
  replayed := by simpa only [replay, hs, Option.bind_some] using child.replayed
  normal := child.normal

end Result

/-- A complete intersection with the inverse conjugate named by a failed
normality test. Its generators and search tree are retained for replay. -/
@[expose] def cut (G H : Group n) (i : Fin G.chain.generators.size) :=
  H.intersectionSearch (Group.conjugate G.chain.generators[i.val].inv H)

theorem cut_spec (G H : Group n) (i : Fin G.chain.generators.size) (p : Perm n) :
    Generated (cut G H i).group.generators p ↔
      Generated H.generators p ∧ Generated H.generators (G.chain.generators[i.val].conj p) := by
  change Generated (H.intersection (Group.conjugate G.chain.generators[i.val].inv H)).generators p ↔ _
  rw [Group.mem_intersection, Group.mem_conjugate]
  simp

theorem cut_strict (G H : Group n) (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (hn : ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val])) :
    ¬SameGroup (cut G H i).group H := by
  intro he
  exact hn (((cut_spec G H i _).mp ((he _).mpr (.generator (Array.getElem_mem j.isLt)))).2)

theorem cut_step (G H : Group n) (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (hn : ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val])) :
    step G H ⟨i.val, (Group.conjugate G.chain.generators[i.val].inv H).chain,
      (cut G H i).group, (cut G H i).certificate⟩ = some (cut G H i).group := by
  have he : (cut G H i).group.sameGroup H = false :=
    Bool.eq_false_iff.mpr fun hh => cut_strict G H i j hn (((cut G H i).group.sameGroup_iff H).mp hh)
  unfold step
  rw [dite_eq_left i.isLt]
  split
  · dsimp only
    simp only [he, Bool.not_false, Bool.and_true]
    split
    · rfl
    · rename_i hf
      exact False.elim (hf (cut G H i).checked)
  · rename_i hn
    exact False.elim (hn (Group.conjugate G.chain.generators[i.val].inv H).valid)

theorem cut_decreases (G H : Group n) (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (hn : ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val])) :
    (cut G H i).group.order < H.order :=
  (step_inside (cut_step G H i j hn)).order_lt (cut_strict G H i j hn)

/-- The order bound cannot be exhausted before the subgroup is normal. -/
@[expose] def iterate (G : Group n) (remaining : Nat) (H : Group n) (bound : H.order ≤ remaining) :
    Result G H :=
  match hf : Normal.failure? G H with
  | none => ⟨H, [], rfl, (Normal.failure_none G H).mp hf⟩
  | some (i, j) =>
    have hn := Normal.failure_sound G H i j hf
    have hd := cut_decreases G H i j hn
    match remaining with
    | 0 => False.elim (by omega)
    | remaining + 1 =>
      let C := Group.conjugate G.chain.generators[i.val].inv H
      let c := H.intersectionSearch C
      have hb : c.group.order ≤ remaining := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hd bound)
      Result.prepend ⟨i.val, C.chain, c.group, c.certificate⟩ (cut_step G H i j hn)
        (iterate G remaining c.group hb)

@[expose] def build (G H : Group n) : Result G H := iterate G H.order H (Nat.le_refl _)

end Hex.PermGroup.Core

namespace Hex.PermGroup.Group

/-- The greatest normal subgroup of `G` contained in `H`, with complete
intersection certificates and a terminal normality check. -/
@[expose] def coreCert (G H : Group n) (_h : H.IsSubgroup G) : Core.Result G H := Core.build G H

@[expose] def core (G H : Group n) (h : H.IsSubgroup G) : Group n := (G.coreCert H h).group

theorem mem_core (G H : Group n) (h : H.IsSubgroup G) (p : Perm n) :
    Generated (G.core H h).generators p ↔
      ∀ g, Generated G.generators g → Generated H.generators (g.conj p) := (G.coreCert H h).spec p

theorem core_inside (G H : Group n) (h : H.IsSubgroup G) : (G.core H h).IsSubgroup H :=
  (G.coreCert H h).inside

theorem core_subgroup (G H : Group n) (h : H.IsSubgroup G) : (G.core H h).IsSubgroup G :=
  fun p hp => h p (G.core_inside H h p hp)

theorem core_normal (G H : Group n) (h : H.IsSubgroup G) :
    (G.core H h).isNormal G (G.core_subgroup H h) = true :=
  (Normal.check_normal G _ (G.core_subgroup H h)).mp (G.coreCert H h).normal

theorem le_core (G H N : Group n) (h : H.IsSubgroup G) (hn : Normal.check G N = true) :
    N.IsSubgroup (G.core H h) ↔ N.IsSubgroup H := by
  constructor
  · exact fun hN p hp => G.core_inside H h p (hN p hp)
  · exact fun hN => (G.coreCert H h).greatest N hN hn

end Hex.PermGroup.Group
