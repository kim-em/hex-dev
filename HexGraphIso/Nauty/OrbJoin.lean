/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOrbit
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.Refine

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

/-! # The union-find layer -/

/-- Soundness of an orbit-pointer array: every parent pointer
descends weakly and is `R`-connected to its vertex. Descent keeps
every pointer below `n` and makes the chase loops terminate within
their fuel, but soundness never needs the latter fact. -/
def OrbSound (R : Nat → Nat → Prop) (orbits : Array Nat) (n : Nat) :
    Prop :=
  orbits.size = n ∧ ∀ v, v < n → orbits[v]! ≤ v ∧ R v orbits[v]!

/-- The consumption form at prune sites: a consulted parent pointer
is justified by `R`. -/
theorem orbSound_ptr {R : Nat → Nat → Prop} {orbits : Array Nat}
    (h : OrbSound R orbits n) {v : Nat} (hv : v < n) :
    R v orbits[v]! :=
  (h.2 v hv).2

/-- The `k`-fold iterated parent pointer, as any chase computes it. -/
def ptrIter (orbits : Array Nat) (v : Nat) : Nat → Nat
  | 0 => v
  | k + 1 => orbits[ptrIter orbits v k]!

/-- Any pointer chase from a sound array descends and stays
`R`-connected. -/
theorem orbSound_iter {R : Nat → Nat → Prop} {orbits : Array Nat}
    (hrefl : ∀ v, R v v)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (h : OrbSound R orbits n) :
    ∀ (k : Nat) {v : Nat}, v < n →
      ptrIter orbits v k ≤ v ∧ R v (ptrIter orbits v k)
  | 0, v, _ => ⟨Nat.le_refl v, hrefl v⟩
  | k + 1, v, hv => by
    obtain ⟨hle, hR⟩ := orbSound_iter hrefl htrans h k hv
    have hlt : ptrIter orbits v k < n := by omega
    obtain ⟨hle', hR'⟩ := h.2 _ hlt
    exact ⟨by rw [ptrIter]; omega, htrans _ _ _ hR (by rw [ptrIter]; exact hR')⟩

theorem orbSound_init (R : Nat → Nat → Prop)
    (hrefl : ∀ v, v < n → R v v) :
    OrbSound R (Array.ofFn (n := n) fun i => i.val) n := by
  refine ⟨by simp, fun v hv => ?_⟩
  have hv' : (Array.ofFn (n := n) fun i => i.val)[v]! = v := by
    rw [getElem!_pos _ _ (by simpa using hv)]
    simp
  rw [hv']
  exact ⟨Nat.le_refl v, hrefl v hv⟩

theorem orbSound_set {R : Nat → Nat → Prop} {orbits : Array Nat}
    (h : OrbSound R orbits n) {p q : Nat} (hq : q < n) (hpq : p ≤ q)
    (hR : R q p) : OrbSound R (orbits.set! q p) n := by
  refine ⟨by rw [Array.size_set!]; exact h.1, fun v hv => ?_⟩
  rcases Decidable.em (q = v) with rfl | hne
  · rw [Array.getElem!_set!_self _ _ _ (by rw [h.1]; exact hq)]
    exact ⟨hpq, hR⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact h.2 v hv

theorem orbSound_mono {R R' : Nat → Nat → Prop} {orbits : Array Nat}
    (himp : ∀ a b, R a b → R' a b)
    (h : OrbSound R orbits n) : OrbSound R' orbits n :=
  ⟨h.1, fun v hv => ⟨(h.2 v hv).1, himp _ _ (h.2 v hv).2⟩⟩

/-- The state a `ForInStep` hands to the rest of the loop. -/
private def stepVal {β : Type} : ForInStep β → β
  | ForInStep.yield b => b
  | ForInStep.done b => b

private theorem stepVal_yield {β : Type} (b : β) :
    stepVal (ForInStep.yield b) = b := rfl

private theorem stepVal_done {β : Type} (b : β) :
    stepVal (ForInStep.done b) = b := rfl

/-- Invariant preservation through a `forIn` loop in `Id`: `break`
and normal exit both preserve `P`. -/
private theorem forIn_list_invariant {β : Type} {P : β → Prop} :
    ∀ (l : List Nat) (init : β) (f : Nat → β → Id (ForInStep β)),
      P init →
      (∀ i b, i ∈ l → P b → P (stepVal (Id.run (f i b)))) →
      P (forIn l init f : Id β)
  | [], _, _, hinit, _ => hinit
  | i :: l, init, f, hinit, hstep => by
    rw [List.forIn_cons]
    have hs := hstep i init (List.mem_cons_self ..) hinit
    match hf : f i init with
    | .yield b =>
      rw [show Id.run (f i init) = ForInStep.yield b from hf] at hs
      exact forIn_list_invariant l b f hs
        (fun i' b' hi' => hstep i' b' (List.mem_cons_of_mem _ hi'))
    | .done b =>
      rw [show Id.run (f i init) = ForInStep.done b from hf] at hs
      exact hs

private theorem forIn_range_eq₀ {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [:n].start [:n].size [:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

/-- The chase loop as a structural recursion: follow parent pointers
until a fixpoint or the fuel list runs out. -/
private def chaseList (orbits : Array Nat) : List Nat → Nat → Nat
  | [], j => j
  | _ :: l, j =>
    if orbits[j]! == j then j else chaseList orbits l orbits[j]!

private theorem forIn_chase_eq {orbits : Array Nat} :
    ∀ (l : List Nat) (j : Nat),
      (forIn l j (fun _ j =>
        if orbits[j]! == j then pure (ForInStep.done j)
        else pure (ForInStep.yield orbits[j]!)) : Id Nat) =
      chaseList orbits l j
  | [], _ => rfl
  | _ :: l, j => by
    rw [List.forIn_cons, chaseList]
    rcases Decidable.em ((orbits[j]! == j) = true) with hc | hc
    · rw [ite_eq_left hc, ite_eq_left hc]
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc]
      exact forIn_chase_eq l _

private theorem run_chase_eq {orbits : Array Nat}
    (l : List Nat) (j : Nat) :
    Id.run (forIn l j (fun _ j =>
      if orbits[j]! == j then pure (ForInStep.done j)
      else pure (ForInStep.yield orbits[j]!))) =
    chaseList orbits l j :=
  forIn_chase_eq l j

private theorem chaseList_sound {R : Nat → Nat → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {orbits : Array Nat} (h : OrbSound R orbits n) :
    ∀ (l : List Nat) (x j : Nat), j < n → R x j →
      chaseList orbits l j < n ∧ R x (chaseList orbits l j) := by
  intro l
  induction l with
  | nil => exact fun x j hj hR => ⟨hj, hR⟩
  | cons head tail ih =>
    intro x j hj hR
    rw [chaseList]
    rcases Decidable.em ((orbits[j]! == j) = true) with hc | hc
    · rw [ite_eq_left hc]
      exact ⟨hj, hR⟩
    · rw [ite_eq_right hc]
      obtain ⟨hle, hstep⟩ := h.2 j hj
      exact ih x orbits[j]! (Nat.lt_of_le_of_lt hle hj)
        (htrans _ _ _ hR hstep)

private theorem bind_invariant {β γ : Type} {P : β → Prop}
    {Q : γ → Prop} (x : Id β) (f : β → Id γ)
    (hx : P x) (hf : ∀ b, P b → Q (f b)) : Q (x >>= f) := hf x hx

theorem orbjoin_orbSound {R : Nat → Nat → Prop}
    (hsymm : ∀ a b, R a b → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {orbits map : Array Nat}
    (h : OrbSound R orbits n)
    (hmap : ∀ i, i < n → map[i]! < n ∧ R i map[i]!) :
    OrbSound R (orbjoin orbits map n).1 n := by
  rw [orbjoin]
  refine bind_invariant (P := fun o : Array Nat => OrbSound R o n)
    (Q := fun oc : Array Nat × Nat => OrbSound R oc.1 n) _ _ ?_ ?_
  · -- pass 1: each join step preserves soundness
    rw [forIn_range_eq₀]
    refine forIn_list_invariant (P := fun o => OrbSound R o n) _ _ _ h ?_
    intro i b hi hb
    have hi' : i < n := List.mem_range.mp hi
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite stepVal, stepVal_yield,
      forIn_range_eq₀, run_chase_eq]
    rcases Decidable.em ((map[i]! != i) = true) with hg | hg
    · rw [ite_eq_left hg]
      obtain ⟨hp1, hR1⟩ := hb.2 i hi'
      obtain ⟨hm, hRm⟩ := hmap i hi'
      obtain ⟨hp2, hR2⟩ := hb.2 map[i]! hm
      obtain ⟨hj1, hRj1⟩ :=
        chaseList_sound htrans hb (List.range n) i b[i]!
          (Nat.lt_of_le_of_lt hp1 hi') hR1
      obtain ⟨hj2, hRj2⟩ :=
        chaseList_sound htrans hb (List.range n) map[i]! b[map[i]!]!
          (Nat.lt_of_le_of_lt hp2 hm) hR2
      have hR12 : R (chaseList b (List.range n) b[map[i]!]!)
          (chaseList b (List.range n) b[i]!) :=
        htrans _ _ _ (hsymm _ _ hRj2)
          (htrans _ _ _ (hsymm _ _ hRm) hRj1)
      rcases Decidable.em (chaseList b (List.range n) b[i]! <
          chaseList b (List.range n) b[map[i]!]!) with hlt | hlt
      · rw [ite_eq_left hlt]
        exact orbSound_set hb hj2 (by omega) hR12
      · rw [ite_eq_right hlt]
        rcases Decidable.em (chaseList b (List.range n) b[i]! >
            chaseList b (List.range n) b[map[i]!]!) with hgt | hgt
        · rw [ite_eq_left hgt]
          exact orbSound_set hb hj1 (by omega) (hsymm _ _ hR12)
        · rw [ite_eq_right hgt]
          exact hb
    · rw [ite_eq_right hg]
      exact hb
  · -- pass 2: path halving preserves soundness pointwise
    intro b hbsound
    refine bind_invariant
      (P := fun s : Array Nat × Nat => OrbSound R s.1 n)
      (Q := fun p : Array Nat × Nat => OrbSound R p.1 n) _ _ ?_ ?_
    · rw [forIn_range_eq₀]
      refine forIn_list_invariant
        (P := fun s : Array Nat × Nat => OrbSound R s.1 n)
        _ _ _ hbsound ?_
      intro i s hi hs
      have hi' : i < n := List.mem_range.mp hi
      simp only [Id.run_pure, apply_ite Id.run,
        apply_ite stepVal, stepVal_yield]
      obtain ⟨hp, hRp⟩ := hs.2 i hi'
      obtain ⟨hq, hRq⟩ := hs.2 s.fst[i]! (Nat.lt_of_le_of_lt hp hi')
      have hset : OrbSound R (s.fst.set! i s.fst[s.fst[i]!]!) n :=
        orbSound_set hs hi' (Nat.le_trans hq hp)
          (htrans _ _ _ hRp hRq)
      rcases Decidable.em
          (((s.fst.set! i s.fst[s.fst[i]!]!)[i]! == i) = true) with
        hc | hc
      · rw [ite_eq_left hc]
        exact hset
      · rw [ite_eq_right hc]
        exact hset
    · intro s hs
      exact hs

/-! # Instantiation: pointers justified by generator words -/

/-- The connectivity relation the search's orbit array maintains:
both vertices in range, joined by a forward word over the store. -/
def OrbConn (gens : List (Array Nat)) (n : Nat) (a b : Nat) : Prop :=
  a < n ∧ b < n ∧ WordConn gens a b

theorem orbConn_symm {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b) :
    ∀ a b, OrbConn gens n a b → OrbConn gens n b a := by
  intro a b ⟨ha, hb', ⟨w, hw, happ⟩⟩
  exact ⟨hb', ha, wordConn_symm hb hinj w ha hw happ⟩

theorem orbConn_trans (gens : List (Array Nat)) :
    ∀ a b c, OrbConn gens n a b → OrbConn gens n b c →
      OrbConn gens n a c := by
  intro a b c ⟨ha, hb', hab⟩ ⟨_, hc, hbc⟩
  exact ⟨ha, hc, wordConn_trans hab hbc⟩

theorem orbConn_mono {gens gens' : List (Array Nat)}
    (hsub : ∀ γ ∈ gens, γ ∈ gens') :
    ∀ a b, OrbConn gens n a b → OrbConn gens' n a b := by
  intro a b ⟨ha, hb', hab⟩
  exact ⟨ha, hb', wordConn_mono hsub hab⟩

/-- Injectivity on `[0, n)` extracted from a checked automorphism's
permutation conjunct. -/
theorem checkAutom_inj {g : Array (VSet n)} {γ : Array Nat}
    (h : checkAutom g γ = true) :
    ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
  rw [checkAutom] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, hperm⟩, -⟩ := h
  intro a b ha hb heq
  have hnd : (((List.range n).map fun v => γ[v]!)).Nodup :=
    ((List.isPerm_iff.mp hperm).symm.nodup List.nodup_range)
  have hga : (((List.range n).map fun v => γ[v]!))[a]'(by
      simpa using ha) = γ[a]! := by
    rw [List.getElem_map, List.getElem_range]
  have hgb : (((List.range n).map fun v => γ[v]!))[b]'(by
      simpa using hb) = γ[b]! := by
    rw [List.getElem_map, List.getElem_range]
  exact hnd.eq_of_getElem_eq (by simpa using ha) (by simpa using hb)
    (by rw [hga, hgb, heq])

/-- The identity orbit array is sound for any store. -/
theorem orbSound_orbConn_init (gens : List (Array Nat)) :
    OrbSound (OrbConn gens n)
      (Array.ofFn (n := n) fun i => i.val) n :=
  orbSound_init _ fun v hv => ⟨hv, hv, wordConn_refl gens v⟩

/-- `orbjoin` with a stored generator keeps every pointer justified:
the run-level per-admission step. `hγ` names the workperm's
membership in the store the pointers are read against, so joining
with a newly admitted generator instantiates `gens` to the store
after admission (earlier pointers transport by `orbSound_orbConn_mono`). -/
theorem orbjoin_orbConn {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b)
    {orbits γ : Array Nat} (hγ : γ ∈ gens)
    (h : OrbSound (OrbConn gens n) orbits n) :
    OrbSound (OrbConn gens n) (orbjoin orbits γ n).1 n :=
  orbjoin_orbSound (orbConn_symm hb hinj) (orbConn_trans gens) h
    (fun i hi => ⟨hb γ hγ i hi,
      ⟨hi, hb γ hγ i hi, wordConn_step hγ i⟩⟩)

/-- Store growth transports pointer soundness. -/
theorem orbSound_orbConn_mono {gens gens' : List (Array Nat)}
    (hsub : ∀ γ ∈ gens, γ ∈ gens') {orbits : Array Nat}
    (h : OrbSound (OrbConn gens n) orbits n) :
    OrbSound (OrbConn gens' n) orbits n :=
  orbSound_mono (orbConn_mono hsub) h

/-- The consumption form at the transcription's prune sites: a
consulted parent pointer is a forward word of stored generators,
with both endpoints in range. -/
theorem orbConn_of_ptr {gens : List (Array Nat)} {orbits : Array Nat}
    (h : OrbSound (OrbConn gens n) orbits n) {v : Nat} (hv : v < n) :
    orbits[v]! < n ∧ WordConn gens v orbits[v]! := by
  obtain ⟨-, h1, h2⟩ := orbSound_ptr h hv
  exact ⟨h1, h2⟩

end Hex.GraphIso.Nauty
