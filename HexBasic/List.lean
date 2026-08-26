/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ListShim

public section

/-!
Reusable list lemmas that are candidates for upstreaming.

Unlike `HexBasic.ListShim`, whose declarations deliberately mirror existing
Batteries signatures, this file owns Hex-local additions to the `List` API.
-/

namespace List

/-- Mapping a list without duplicates by a function injective on that list
preserves the absence of duplicates. -/
theorem nodup_map_on {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have : x = y := hinj x (by simp) y (by simp [hy]) hxy.symm
        exact hxs.1 (by simpa [this] using hy)
      · exact ih hxs.2 fun a ha b hb hab =>
          hinj a (by simp [ha]) b (by simp [hb]) hab

/-- A flat map is duplicate-free when every row is duplicate-free and rows
coming from distinct source elements are disjoint. -/
theorem nodup_flatMap_of_disjoint {α β} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hrow : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisj :
      ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
        ∀ z, z ∈ f x → z ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [nodup_cons] at hxs
      rw [flatMap_cons, nodup_append]
      refine ⟨hrow x (by simp), ?_, ?_⟩
      · exact ih hxs.2
          (by intro y hy; exact hrow y (by simp [hy]))
          (by
            intro y hy z hz hyz t hty htz
            exact hdisj y (by simp [hy]) z (by simp [hz]) hyz t hty htz)
      · intro a ha b hb hab
        rcases mem_flatMap.mp hb with ⟨y, hy, hby⟩
        exact hdisj x (by simp) y (by simp [hy])
          (fun hxy => hxs.1 (hxy ▸ hy)) a ha (hab ▸ hby)

/-- Lexicographic comparison is unchanged by pointwise combining both lists
with the same third list when the element comparison has the corresponding
invariance. The length hypotheses ensure `zipWith` does not truncate. -/
theorem compareLex_zipWith {α β} (cmp : α → α → Ordering) (f : α → β → α)
    (hcmp : ∀ a b c, cmp a b = cmp (f a c) (f b c)) :
    ∀ (as bs : List α) (cs : List β),
      as.length = bs.length →
      as.length = cs.length →
      List.compareLex cmp as bs =
        List.compareLex cmp (zipWith f as cs) (zipWith f bs cs)
  | [], [], [], _, _ => rfl
  | a :: as, b :: bs, c :: cs, hab, hac => by
      simp only [length] at hab hac
      have hab' : as.length = bs.length := by omega
      have hac' : as.length = cs.length := by omega
      simp only [List.zipWith]
      rw [List.compareLex_cons_cons, List.compareLex_cons_cons,
        ← hcmp a b c, compareLex_zipWith cmp f hcmp as bs cs hab' hac']

end List
