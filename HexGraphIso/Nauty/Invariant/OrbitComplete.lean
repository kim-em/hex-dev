/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Search.Refine

public section

namespace Hex.GraphIso.Nauty

namespace Orbit

variable {n : Nat}

/-- Every parent pointer lies below its vertex. -/
def Descending (o : Array Nat) (n : Nat) : Prop :=
  o.size = n ∧ ∀ v, v < n → o[v]! ≤ v

/-- A function constant along all parent pointers. -/
def Stable {α : Sort u} (o : Array Nat) (n : Nat) (f : Nat → α) : Prop :=
  ∀ v, v < n → f o[v]! = f v

/-- All parent pointers already point to roots. -/
def Flat (o : Array Nat) (n : Nat) : Prop :=
  ∀ v, v < n → o[o[v]!]! = o[v]!

theorem Descending.ofSound {R : Nat → Nat → Prop} {o : Array Nat}
    (h : OrbSound R o n) : Descending o n :=
  ⟨h.1, fun v hv => (h.2 v hv).1⟩

theorem Descending.sound {o : Array Nat} (h : Descending o n) :
    OrbSound (fun _ _ => True) o n :=
  ⟨h.1, fun v hv => ⟨h.2 v hv, trivial⟩⟩

theorem Descending.set {o : Array Nat} (h : Descending o n)
    {p q : Nat} (hq : q < n) (hp : p ≤ q) :
    Descending (o.set! q p) n :=
  .ofSound (orbSound_set h.sound hq hp trivial)

private theorem chase_root {o : Array Nat} (h : Descending o n) :
    ∀ (l : List Nat) (j : Nat), j < n → j < l.length →
      o[chaseList o l j]! = chaseList o l j := by
  intro l
  induction l with
  | nil => intro j hj hf; simp at hf
  | cons a l ih =>
    intro j hj hf
    rw [chaseList]
    split
    · rename_i heq
      exact beq_iff_eq.mp heq
    · rename_i hne
      have hle := h.2 j hj
      have hne' : o[j]! ≠ j := by simpa using hne
      exact ih _ (by omega) (by simp only [List.length_cons] at hf; omega)

private theorem chase_lt {o : Array Nat} (h : Descending o n)
    (l : List Nat) {j : Nat} (hj : j < n) : chaseList o l j < n :=
  (chaseList_sound (fun _ _ _ _ _ => trivial) h.sound l j j hj trivial).1

private theorem Stable.chase {α : Sort u} {o : Array Nat} {f : Nat → α}
    (hd : Descending o n) (h : Stable o n f) (l : List Nat)
    {j : Nat} (hj : j < n) : f (chaseList o l j) = f j := by
  have hs : OrbSound (fun a b => f b = f a) o n :=
    ⟨hd.1, fun v hv => ⟨hd.2 v hv, h v hv⟩⟩
  exact (chaseList_sound (fun _ _ _ hab hbc => hbc.trans hab)
    hs l j j hj rfl).2

/-- Joining two roots preserves every previous parent equation. -/
theorem Stable.of_set_root {α : Sort u} {o : Array Nat} {f : Nat → α}
    {q p : Nat} (hroot : o[q]! = q)
    (h : Stable (o.set! q p) n f) : Stable o n f := by
  intro v hv
  by_cases heq : q = v
  · subst v
    rw [hroot]
  · simpa only [Array.getElem!_set!_ne _ _ _ _ heq] using h v hv

/-- Replacing a parent by its parent preserves the original equations. -/
theorem Stable.of_compress {α : Sort u} {o : Array Nat} {f : Nat → α}
    (hd : Descending o n) {q : Nat} (hq : q < n)
    (h : Stable (o.set! q o[o[q]!]!) n f) : Stable o n f := by
  intro v hv
  by_cases heq : q = v
  · subst v
    by_cases hroot : o[q]! = q
    · rw [hroot]
    · have hp : o[q]! < n := Nat.lt_of_le_of_lt (hd.2 q hq) hq
      have hparent := h o[q]! hp
      rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hroot he.symm)] at hparent
      have hq' := h q hq
      rw [Array.getElem!_set!_self _ _ _ (by simpa [hd.1] using hq)] at hq'
      exact hparent.symm.trans hq'
  · simpa only [Array.getElem!_set!_ne _ _ _ _ heq] using h v hv

private def join (map : Array Nat) (n : Nat) (o : Array Nat) (i : Nat) : Array Nat :=
  if map[i]! != i then
    let a := chaseList o (List.range n) o[i]!
    let b := chaseList o (List.range n) o[map[i]!]!
    if a < b then o.set! b a else if a > b then o.set! a b else o
  else o

private def compress (s : Array Nat × Nat) (i : Nat) : Array Nat × Nat :=
  let o := s.1.set! i s.1[s.1[i]!]!
  (o, if o[i]! == i then s.2 + 1 else s.2)

private theorem forIn_fold {β : Type} (l : List Nat) (f : β → Nat → β) (b : β) :
    (forIn l b (fun i b => pure (ForInStep.yield (f b i))) : Id β) =
      l.foldl f b := by
  induction l generalizing b with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    exact ih _

private theorem orbjoin_eq (o map : Array Nat) (n : Nat) :
    orbjoin o map n = (List.range n).foldl compress
      ((List.range n).foldl (join map n) o, 0) := by
  rw [orbjoin]
  simp only [forIn_range_eq₀, forIn_chase_eq]
  have hjoin : ∀ o : Array Nat,
      (forIn (List.range n) o (fun i o => do
        if map[i]! != i then
          let a := chaseList o (List.range n) o[i]!
          let b := chaseList o (List.range n) o[map[i]!]!
          if a < b then pure (.yield (o.set! b a))
          else if a > b then pure (.yield (o.set! a b))
          else pure (.yield o)
        else pure (.yield o)) : Id (Array Nat)) =
        (List.range n).foldl (join map n) o := by
    intro o
    rw [← forIn_fold]
    congr 1
    funext i o
    simp only [join]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  simp only [bind, pure, Id.run] at hjoin ⊢
  rw [hjoin]
  change (forIn (List.range n) _ _ : Id (Array Nat × Nat)) = _
  rw [← forIn_fold (List.range n) compress]
  congr 1
  funext i s
  simp only [compress]
  split <;> rfl

private theorem join_desc {o map : Array Nat} (hd : Descending o n)
    {i : Nat} (hi : i < n) (hm : map[i]! < n) :
    Descending (join map n o i) n := by
  have ha := chase_lt hd (List.range n) (Nat.lt_of_le_of_lt (hd.2 i hi) hi)
  have hb := chase_lt hd (List.range n) (Nat.lt_of_le_of_lt (hd.2 _ hm) hm)
  unfold join
  split
  · dsimp only
    split
    · exact hd.set hb (by omega)
    · split
      · exact hd.set ha (by omega)
      · exact hd
  · exact hd

private theorem stable_join {α : Sort u} {o map : Array Nat} {f : Nat → α}
    (hd : Descending o n) {i : Nat} (hi : i < n) (hm : map[i]! < n)
    (h : Stable (join map n o i) n f) : Stable o n f ∧ f map[i]! = f i := by
  let a := chaseList o (List.range n) o[i]!
  let b := chaseList o (List.range n) o[map[i]!]!
  have hi' := Nat.lt_of_le_of_lt (hd.2 i hi) hi
  have hm' := Nat.lt_of_le_of_lt (hd.2 _ hm) hm
  have ha : a < n := chase_lt hd _ hi'
  have hb : b < n := chase_lt hd _ hm'
  have hra : o[a]! = a := chase_root hd _ _ hi' (by simpa using hi')
  have hrb : o[b]! = b := chase_root hd _ _ hm' (by simpa using hm')
  have hfa : Stable o n f → f a = f i :=
    fun hs => (hs.chase hd _ hi').trans (hs i hi)
  have hfb : Stable o n f → f b = f map[i]! :=
    fun hs => (hs.chase hd _ hm').trans (hs _ hm)
  unfold join at h
  split at h
  · change Stable (if a < b then o.set! b a else if a > b then o.set! a b else o) n f at h
    split at h
    · have hs := h.of_set_root hrb
      have he := h b hb
      rw [Array.getElem!_set!_self _ _ _ (by simpa [hd.1] using hb)] at he
      exact ⟨hs, (hfb hs).symm.trans (he.symm.trans (hfa hs))⟩
    · split at h
      · have hs := h.of_set_root hra
        have he := h a ha
        rw [Array.getElem!_set!_self _ _ _ (by simpa [hd.1] using ha)] at he
        exact ⟨hs, (hfb hs).symm.trans (he.trans (hfa hs))⟩
      · have hab : a = b := by omega
        exact ⟨h, (hfb h).symm.trans (hab ▸ hfa h)⟩
  · rename_i heq
    have he : map[i]! = i := by simpa using heq
    exact ⟨h, congrArg f he⟩

private theorem compress_desc {s : Array Nat × Nat} (hd : Descending s.1 n)
    {i : Nat} (hi : i < n) : Descending (compress s i).1 n := by
  have hp := hd.2 i hi
  exact hd.set hi (Nat.le_trans (hd.2 _ (by omega)) hp)

private theorem compress_flat {s : Array Nat × Nat} (hd : Descending s.1 n)
    {i : Nat} (hi : i < n) (hf : ∀ v, v < i → s.1[s.1[v]!]! = s.1[v]!) :
    ∀ v, v < i + 1 → (compress s i).1[(compress s i).1[v]!]! =
      (compress s i).1[v]! := by
  let o := s.1
  have hp : o[i]! ≤ i := hd.2 i hi
  have hpp : o[o[i]!]! ≤ o[i]! := hd.2 _ (by omega)
  have hroot : o[o[o[i]!]!]! = o[o[i]!]! := by
    by_cases he : o[i]! = i
    · simp only [he]
    · exact hf _ (by omega)
  intro v hv
  change (o.set! i o[o[i]!]!)[(o.set! i o[o[i]!]!)[v]!]! =
    (o.set! i o[o[i]!]!)[v]!
  by_cases he : i = v
  · subst v
    rw [Array.getElem!_set!_self _ _ _ (by simpa [o, hd.1] using hi)]
    by_cases hr : i = o[o[i]!]!
    · rw [← hr, Array.getElem!_set!_self _ _ _ (by simpa [o, hd.1] using hi)]
    · rw [Array.getElem!_set!_ne _ _ _ _ hr]
      exact hroot
  · rw [Array.getElem!_set!_ne _ _ _ _ he]
    have hvn : v < n := by omega
    have hpv : o[v]! ≤ v := hd.2 v hvn
    rw [Array.getElem!_set!_ne _ _ _ _ (show i ≠ o[v]! by omega)]
    exact hf v (by omega)

private theorem joins_desc {map : Array Nat}
    (hm : ∀ i, i < n → map[i]! < n) :
    ∀ (l : List Nat), (∀ i ∈ l, i < n) → ∀ o, Descending o n →
      Descending (l.foldl (join map n) o) n := by
  intro l
  induction l with
  | nil => intro hl o hd; exact hd
  | cons i l ih =>
    intro hl o hd
    exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
      (join_desc hd (hl _ List.mem_cons_self) (hm _ (hl _ List.mem_cons_self)))

private theorem stable_joins {α : Sort u} {map : Array Nat} {f : Nat → α}
    (hm : ∀ i, i < n → map[i]! < n) :
    ∀ (l : List Nat), (∀ i ∈ l, i < n) → ∀ o, Descending o n →
      Stable (l.foldl (join map n) o) n f →
      Stable o n f ∧ ∀ i ∈ l, f map[i]! = f i := by
  intro l
  induction l with
  | nil => intro hl o hd hs; exact ⟨hs, by simp⟩
  | cons i l ih =>
    intro hl o hd hs
    have hi := hl i List.mem_cons_self
    have hm' := hm i hi
    obtain ⟨hrest, hedges⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
      (join_desc hd hi hm') hs
    obtain ⟨hold, hedge⟩ := stable_join hd hi hm' hrest
    refine ⟨hold, fun j hj => ?_⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hedge
    · exact hedges j hj

private theorem stable_compressions {α : Sort u} {f : Nat → α} :
    ∀ (l : List Nat), (∀ i ∈ l, i < n) → ∀ s : Array Nat × Nat,
      Descending s.1 n → Stable (l.foldl compress s).1 n f → Stable s.1 n f := by
  intro l
  induction l with
  | nil => intro hl s hd hs; exact hs
  | cons i l ih =>
    intro hl s hd hs
    have hi := hl i List.mem_cons_self
    have hrest := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
      (compress_desc hd hi) hs
    exact hrest.of_compress hd hi

private theorem compressions_flat : ∀ count start (s : Array Nat × Nat),
    start + count ≤ n → Descending s.1 n →
    (∀ v, v < start → s.1[s.1[v]!]! = s.1[v]!) →
    ∀ v, v < start + count →
      ((List.range' start count).foldl compress s).1[
        ((List.range' start count).foldl compress s).1[v]!]! =
      ((List.range' start count).foldl compress s).1[v]! := by
  intro count
  induction count with
  | zero => intro start s hn hd hf; simpa using hf
  | succ count ih =>
    intro start s hn hd hf
    rw [List.range'_succ, List.foldl_cons]
    have hi : start < n := by omega
    have h := ih (start + 1) (compress s start) (by omega)
      (compress_desc hd hi) (compress_flat hd hi hf)
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using h

/-- After joining and compressing, every stored representative is a root. -/
theorem flat_orbjoin {o map : Array Nat} (hd : Descending o n)
    (hm : ∀ i, i < n → map[i]! < n) : Flat (orbjoin o map n).1 n := by
  rw [orbjoin_eq]
  have hj := joins_desc hm (List.range n) (fun _ => List.mem_range.mp) o hd
  have h := compressions_flat n 0
    ((List.range n).foldl (join map n) o, 0) (by omega) hj (by simp)
  simpa only [Flat, Nat.zero_add, ← List.range_eq_range'] using h

/-- Any function constant on the final orbit cells is constant on every
old cell and on every edge introduced by this join. -/
theorem stable_orbjoin {α : Sort u} {o map : Array Nat} {f : Nat → α}
    (hd : Descending o n) (hm : ∀ i, i < n → map[i]! < n)
    (h : Stable (orbjoin o map n).1 n f) :
    Stable o n f ∧ ∀ i, i < n → f map[i]! = f i := by
  rw [orbjoin_eq] at h
  have hj := joins_desc hm (List.range n) (fun _ => List.mem_range.mp) o hd
  have hs := stable_compressions (List.range n) (fun _ => List.mem_range.mp) _ hj h
  obtain ⟨hold, hedge⟩ := stable_joins hm (List.range n)
    (fun _ => List.mem_range.mp) o hd hs
  exact ⟨hold, fun i hi => hedge i (List.mem_range.mpr hi)⟩

theorem Descending.orbjoin {o map : Array Nat} (hd : Descending o n)
    (hm : ∀ i, i < n → map[i]! < n) : Descending (orbjoin o map n).1 n :=
  .ofSound (orbjoin_orbSound (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    hd.sound (fun i hi => ⟨hm i hi, trivial⟩))

/-- Repeated joins preserve the property that entries are roots. -/
theorem flat_fold : ∀ (maps : List (Array Nat)),
    (∀ γ ∈ maps, ∀ i, i < n → γ[i]! < n) → ∀ o,
    Descending o n → Flat o n →
    Flat (maps.foldl (fun o γ => (orbjoin o γ n).1) o) n := by
  intro maps
  induction maps with
  | nil => intro hm o hd hf; exact hf
  | cons γ maps ih =>
    intro hm o hd hf
    have hγ := hm γ List.mem_cons_self
    exact ih (fun δ hδ => hm δ (List.mem_cons_of_mem _ hδ)) _
      (hd.orbjoin hγ) (flat_orbjoin hd hγ)

/-- A function constant on the final cells respects every generator edge. -/
theorem stable_fold {α : Sort u} {f : Nat → α} : ∀ (maps : List (Array Nat)),
    (∀ γ ∈ maps, ∀ i, i < n → γ[i]! < n) → ∀ o,
    Descending o n → Stable (maps.foldl (fun o γ => (orbjoin o γ n).1) o) n f →
    Stable o n f ∧ ∀ γ ∈ maps, ∀ i, i < n → f γ[i]! = f i := by
  intro maps
  induction maps with
  | nil => intro hm o hd hs; exact ⟨hs, by simp⟩
  | cons γ maps ih =>
    intro hm o hd hs
    have hγ := hm γ List.mem_cons_self
    obtain ⟨hrest, hedges⟩ := ih (fun δ hδ => hm δ (List.mem_cons_of_mem _ hδ)) _
      (hd.orbjoin hγ) hs
    obtain ⟨hold, hedge⟩ := stable_orbjoin hd hγ hrest
    refine ⟨hold, fun δ hδ => ?_⟩
    rcases List.mem_cons.mp hδ with rfl | hδ
    · exact hedge
    · exact hedges δ hδ

end Orbit

end Hex.GraphIso.Nauty
