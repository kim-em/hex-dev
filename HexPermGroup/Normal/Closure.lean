/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Step

public section

namespace Hex.PermGroup.Normal

/-- A complete normal-closure certificate. The insertion trace reconstructs
the generated subgroup; a terminal full pass verifies normality. -/
@[expose] def checkClosure (G H K : Group n) (trace : List (Step n)) : Bool :=
  match replay G H trace with
  | none => false
  | some L => L.sameGroup K && check G K

theorem checkClosure_spec {G H K : Group n} {trace : List (Step n)}
    (hH : H.IsSubgroup G) (h : checkClosure G H K trace = true) :
    K.IsSubgroup G ∧ H.IsSubgroup K ∧ check G K = true ∧
      ∀ N : Group n, H.IsSubgroup N → check G N = true → K.IsSubgroup N := by
  unfold checkClosure at h
  split at h
  · contradiction
  · rename_i L hL
    have hh : L.sameGroup K = true ∧ check G K = true := by
      simpa only [Bool.and_eq_true] using h
    have he := (L.sameGroup_iff K).mp hh.1
    refine ⟨fun p hp => replay_inside hL hH p ((he p).mpr hp),
      fun p hp => (he p).mp (replay_grows hL p hp), hh.2, ?_⟩
    intro N hN hn p hp
    exact replay_least hL hN hn p ((he p).mpr hp)

/-- Exact output and raw chains for every strict conjugate insertion. -/
structure Closure (G H : Group n) where
  group : Group n
  trace : List (Step n)
  replayed : replay G H trace = some group
  normal : check G group = true

namespace Closure

variable {G H : Group n}

theorem checked (c : Closure G H) : checkClosure G H c.group c.trace = true := by
  simp only [checkClosure, c.replayed, Bool.and_eq_true]
  exact ⟨(c.group.sameGroup_iff c.group).mpr (fun _ => Iff.rfl), c.normal⟩

theorem inside (c : Closure G H) (hH : H.IsSubgroup G) : c.group.IsSubgroup G :=
  replay_inside c.replayed hH

theorem contains (c : Closure G H) : H.IsSubgroup c.group := replay_grows c.replayed

theorem least (c : Closure G H) (N : Group n) (hN : H.IsSubgroup N) (hn : check G N = true) :
    c.group.IsSubgroup N := replay_least c.replayed hN hn

/-- Exact order bounds the number of strict chain rebuilds logarithmically. -/
theorem growth (c : Closure G H) (hH : H.IsSubgroup G) :
    2 ^ c.trace.length * H.order ≤ G.order :=
  Nat.le_trans (replay_growth c.replayed) (c.inside hH).order_le

/-- Prepend a certified strict conjugate insertion to the remaining closure. -/
@[expose] def prepend (G H : Group n) (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (hn : ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val]))
    (child : Closure G (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val]))) : Closure G H where
  group := child.group
  trace := ⟨i.val, j.val, (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])).chain⟩ :: child.trace
  replayed := by
    simp only [replay, step_adjoin G H i j hn, Option.bind_some]
    exact child.replayed
  normal := child.normal

end Closure

theorem adjoin_decreases (G H : Group n) (hH : H.IsSubgroup G)
    (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (hn : ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val])) :
    G.order - (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])).order <
      G.order - H.order := by
  have hi := (G.chain_generated _).mp (Generated.generator (Array.getElem_mem i.isLt))
  have hj := hH _ (Generated.generator (Array.getElem_mem j.isLt))
  have hK : (H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])).IsSubgroup G :=
    (H.adjoin_le G _).mpr ⟨hH, hi.comp (hj.comp hi.inv)⟩
  have hd := H.order_adjoin _ hn
  have hb := hK.order_le
  have hp := H.order_pos
  omega

/-- Iterate strict insertions under the proved order bound. The zero case
cannot truncate an unfinished normal closure. -/
@[expose] def iterate (G : Group n) (remaining : Nat) (H : Group n) (hH : H.IsSubgroup G)
    (bound : G.order - H.order ≤ remaining) : Closure G H :=
  match hf : failure? G H with
  | none => ⟨H, [], rfl, (failure_none G H).mp hf⟩
  | some (i, j) =>
    have hn := failure_sound G H i j hf
    have hd := adjoin_decreases G H hH i j hn
    match remaining with
    | 0 => False.elim (by omega)
    | remaining + 1 =>
      let K := H.adjoin (G.chain.generators[i.val].conj H.generators[j.val])
      have hK : K.IsSubgroup G := step_inside (step_adjoin G H i j hn) hH
      have hb : G.order - K.order ≤ remaining := by
        dsimp only [K]
        omega
      Closure.prepend G H i j hn (iterate G remaining K hK hb)

/-- Insert missing conjugates until a full pass adds nothing. The iteration
bound follows from strict order growth and cannot produce an incomplete answer. -/
@[expose] def close (G H : Group n) (hH : H.IsSubgroup G) : Closure G H :=
  iterate G (G.order - H.order) H hH (Nat.le_refl _)

end Hex.PermGroup.Normal

namespace Hex.PermGroup.Group

/-- The least normal subgroup of `G` containing `H`, with complete replay data. -/
@[expose] def normalClosureCert (G H : Group n) (h : H.IsSubgroup G) : Normal.Closure G H :=
  Normal.close G H h

/-- Start from the subgroup and adjoin forced conjugates until it is normal. -/
@[expose] def normalClosure (G H : Group n) (h : H.IsSubgroup G) : Group n :=
  (G.normalClosureCert H h).group

theorem normalClosure_inside (G H : Group n) (h : H.IsSubgroup G) :
    (G.normalClosure H h).IsSubgroup G := (G.normalClosureCert H h).inside h

theorem normalClosure_contains (G H : Group n) (h : H.IsSubgroup G) :
    H.IsSubgroup (G.normalClosure H h) := (G.normalClosureCert H h).contains

theorem normalClosure_normal (G H : Group n) (h : H.IsSubgroup G) :
    (G.normalClosure H h).isNormal G (G.normalClosure_inside H h) = true :=
  (Normal.check_normal G _ (G.normalClosure_inside H h)).mp (G.normalClosureCert H h).normal

/-- The universal property rules out extraneous elements, not merely failures
of normality. The containing subgroup need only be closed under `G` conjugation. -/
theorem normalClosure_le (G H N : Group n) (h : H.IsSubgroup G) (hn : Normal.check G N = true) :
    (G.normalClosure H h).IsSubgroup N ↔ H.IsSubgroup N := by
  constructor
  · intro hN p hp
    exact hN p (G.normalClosure_contains H h p hp)
  · intro hN
    exact (G.normalClosureCert H h).least N hN hn

end Hex.PermGroup.Group
