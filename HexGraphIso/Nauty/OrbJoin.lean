/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOrbit
public import HexGraphIso.Nauty.Search

public section

/-!
Soundness of the transcription's orbit bookkeeping. The search keeps
one global union-find array `st.orbits`, joined with every admitted
generator through `orbjoin`; prune sites consult its parent pointers
directly. This file proves that every parent pointer is justified by
a forward word of joined generators: `WordConn` is the connectivity
relation (a word over the store carrying one vertex to the other),
and `OrbSound` states that each pointer strictly descends and is
`WordConn`-connected to its vertex. `orbjoin_orbSound` shows one
`orbjoin` call preserves `OrbSound` when the joining map is itself
word-connected pointwise, and `orbSound_init` seeds the identity
array, so the run-level invariant threads through the search with no
other touch points.

Symmetry of `WordConn` is where the group theory lives: the chase
loops inside `orbjoin` link roots found from both ends of a
generator edge, so the pointer being justified can point against the
direction of the discovered word. Forward words still suffice —
a bounded injective array has finite order pointwise
(`exists_applyWord_replicate_self`, by pigeonhole on the trajectory),
so the inverse of a generator is one of its forward powers
(`wordConn_symm`). No inverse arrays are ever materialized, matching
`orbitClose_sound`'s forward-only discipline on the model side.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Connectivity by a forward word over a generator store: some list
of stored arrays, applied leftmost first, carries `u` to `v`. -/
def WordConn (gens : List (Array Nat)) (u v : Nat) : Prop :=
  ∃ w : List (Array Nat), (∀ γ ∈ w, γ ∈ gens) ∧ applyWord w u = v

theorem wordConn_refl (gens : List (Array Nat)) (u : Nat) :
    WordConn gens u u :=
  ⟨[], by simp, rfl⟩

theorem applyWord_append (w₁ w₂ : List (Array Nat)) (u : Nat) :
    applyWord (w₁ ++ w₂) u = applyWord w₂ (applyWord w₁ u) :=
  List.foldl_append

theorem wordConn_trans {gens : List (Array Nat)} {u v x : Nat}
    (h₁ : WordConn gens u v) (h₂ : WordConn gens v x) :
    WordConn gens u x := by
  obtain ⟨w₁, hw₁, ha₁⟩ := h₁
  obtain ⟨w₂, hw₂, ha₂⟩ := h₂
  refine ⟨w₁ ++ w₂, fun γ hγ => ?_, ?_⟩
  · rcases List.mem_append.mp hγ with h | h
    · exact hw₁ γ h
    · exact hw₂ γ h
  · rw [applyWord_append, ha₁, ha₂]

theorem wordConn_step {gens : List (Array Nat)} {γ : Array Nat}
    (hγ : γ ∈ gens) (u : Nat) : WordConn gens u γ[u]! :=
  ⟨[γ], fun γ' hγ' => by rw [List.mem_singleton.mp hγ']; exact hγ, rfl⟩

theorem wordConn_mono {gens gens' : List (Array Nat)} {u v : Nat}
    (hsub : ∀ γ ∈ gens, γ ∈ gens')
    (h : WordConn gens u v) : WordConn gens' u v := by
  obtain ⟨w, hw, ha⟩ := h
  exact ⟨w, fun γ hγ => hsub γ (hw γ hγ), ha⟩

/-! # Pointwise finite order of a bounded injective array -/

theorem applyWord_replicate_succ (γ : Array Nat) (k u : Nat) :
    applyWord (List.replicate (k + 1) γ) u =
      applyWord (List.replicate k γ) γ[u]! := by
  rw [List.replicate_succ, applyWord, List.foldl_cons]
  rfl

theorem applyWord_replicate_lt {γ : Array Nat}
    (hb : ∀ v, v < n → γ[v]! < n) :
    ∀ (k : Nat) {u : Nat}, u < n →
      applyWord (List.replicate k γ) u < n
  | 0, _, hu => hu
  | k + 1, u, hu => by
    rw [applyWord_replicate_succ]
    exact applyWord_replicate_lt hb k (hb u hu)

theorem applyWord_replicate_inj {γ : Array Nat}
    (hb : ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b) :
    ∀ (k : Nat) {a b : Nat}, a < n → b < n →
      applyWord (List.replicate k γ) a =
        applyWord (List.replicate k γ) b → a = b
  | 0, _, _, _, _, h => h
  | k + 1, a, b, ha, hb', h => by
    rw [applyWord_replicate_succ, applyWord_replicate_succ] at h
    exact hinj a b ha hb'
      (applyWord_replicate_inj hb hinj k (hb a ha) (hb b hb') h)

/-- Pigeonhole on a trajectory: `n + 1` values below `n` repeat. -/
private theorem exists_repeat :
    ∀ (n : Nat) (s : Nat → Nat), (∀ j, j ≤ n → s j < n) →
      ∃ a b, a < b ∧ b ≤ n ∧ s a = s b
  | 0, s, hs => absurd (hs 0 (Nat.le_refl 0)) (by omega)
  | n + 1, s, hs => by
    rcases Classical.em (∃ j, j ≤ n ∧ s j = s (n + 1)) with h | h
    · obtain ⟨j, hj, heq⟩ := h
      exact ⟨j, n + 1, by omega, Nat.le_refl _, heq⟩
    · have hne : ∀ j, j ≤ n → s j ≠ s (n + 1) := by
        intro j hj hcontra
        exact h ⟨j, hj, hcontra⟩
      have hlast : s (n + 1) < n + 1 := hs (n + 1) (Nat.le_refl _)
      obtain ⟨a, b, hab, hbn, heq⟩ := exists_repeat n
        (fun j => if s j = n then s (n + 1) else s j)
        (fun j hj => by
          rcases Decidable.em (s j = n) with hc | hc
          · rw [ite_eq_left hc]
            have := hne j hj
            omega
          · rw [ite_eq_right hc]
            have := hs j (by omega)
            omega)
      refine ⟨a, b, hab, by omega, ?_⟩
      rcases Decidable.em (s a = n) with ha | ha <;>
        rcases Decidable.em (s b = n) with hb | hb
      · rw [ha, hb]
      · rw [ite_eq_left ha, ite_eq_right hb] at heq
        exact absurd heq.symm (hne b (by omega))
      · rw [ite_eq_right ha, ite_eq_left hb] at heq
        exact absurd heq (hne a (by omega))
      · rw [ite_eq_right ha, ite_eq_right hb] at heq
        exact heq

/-- A bounded injective array returns every vertex to itself under
some positive number of forward applications. -/
theorem exists_applyWord_replicate_self {γ : Array Nat}
    (hb : ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b)
    {u : Nat} (hu : u < n) :
    ∃ k, 0 < k ∧ applyWord (List.replicate k γ) u = u := by
  obtain ⟨a, b, hab, hbn, heq⟩ := exists_repeat n
    (fun j => applyWord (List.replicate j γ) u)
    (fun j _ => applyWord_replicate_lt hb j hu)
  refine ⟨b - a, by omega, ?_⟩
  have hsplit : applyWord (List.replicate a γ)
      (applyWord (List.replicate (b - a) γ) u) =
      applyWord (List.replicate a γ) u := by
    rw [← applyWord_append, List.replicate_append_replicate]
    have : b - a + a = b := by omega
    rw [this]
    exact heq.symm
  exact applyWord_replicate_inj hb hinj a
    (applyWord_replicate_lt hb _ hu) hu hsplit

/-- Symmetry of forward-word connectivity over bounded injective
generators: the inverse of each letter is one of its forward
powers. -/
theorem wordConn_symm {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b) :
    ∀ (w : List (Array Nat)) {u v : Nat}, u < n →
      (∀ γ ∈ w, γ ∈ gens) → applyWord w u = v →
      WordConn gens v u
  | [], u, v, _, _, happ => happ ▸ wordConn_refl gens u
  | γ :: w, u, v, hu, hmem, happ => by
    have hγ := hmem γ (List.mem_cons_self ..)
    have hγu : γ[u]! < n := hb γ hγ u hu
    have happ' : applyWord w γ[u]! = v := happ
    have htail := wordConn_symm hb hinj w hγu
      (fun γ' hγ' => hmem γ' (List.mem_cons_of_mem _ hγ')) happ'
    obtain ⟨k, hk, hret⟩ :=
      exists_applyWord_replicate_self (hb γ hγ) (hinj γ hγ) hu
    refine wordConn_trans htail ⟨List.replicate (k - 1) γ,
      fun γ' hγ' => (List.eq_of_mem_replicate hγ') ▸ hγ, ?_⟩
    have : applyWord (List.replicate k γ) u =
        applyWord (List.replicate (k - 1) γ) γ[u]! := by
      have hks : k - 1 + 1 = k := by omega
      rw [← hks, applyWord_replicate_succ, hks]
    rw [← this, hret]

end Hex.GraphIso.Nauty
