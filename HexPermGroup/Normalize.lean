/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Check
public import HexPermGroup.Word.Compose

public section

namespace Hex.PermGroup

namespace Chain

theorem before_irrefl (p : Perm n) : ¬ before p p := by
  simp [before, Std.ReflOrd.compare_self]

theorem before_trans {p q r : Perm n} (hpq : before p q) (hqr : before q r) :
    before p r :=
  Std.TransCmp.lt_of_lt_of_isLE hpq (Ordering.isLE_of_eq_lt hqr)

end Chain

/-- A working generator with its signed input reference. Its permutation is
cached, so sorting never recomputes inverses. -/
structure Generator (S : Array (Perm n)) where
  value : Perm n
  source : Fin S.size × Bool
  valid : value = Word.letter S source

namespace Generator

variable {n : Nat} {S : Array (Perm n)}

@[expose] def ofIndex (S : Array (Perm n)) (i : Fin S.size) (inverse : Bool) : Generator S :=
  ⟨Word.letter S (i, inverse), (i, inverse), rfl⟩

@[expose] def images (p : Perm n) : List Nat := p.vec.toList.map Fin.val

theorem images_injective {p q : Perm n} (h : images p = images q) : p = q :=
  Perm.ext_vec (Vector.toList_inj.mp ((List.map_inj_right (fun _ _ => Fin.ext)).mp h))

/-- The non-strict ordering used by merge sort; the checker retains its separate
strict comparison on image arrays. -/
@[expose] def le (x y : Generator S) : Bool := (compare (images x.value) (images y.value)).isLE

theorem le_trans (x y z : Generator S) (hxy : le x y) (hyz : le y z) : le x z :=
  Std.TransOrd.isLE_trans hxy hyz

theorem le_total (x y : Generator S) : le x y || le y x := by
  unfold le
  rw [Std.OrientedOrd.eq_swap (a := images y.value)]
  cases compare (images x.value) (images y.value) <;> rfl

theorem before_of_le {x y : Generator S} (hle : le x y) (hne : x.value ≠ y.value) :
    Chain.before x.value y.value := by
  change compare (images x.value) (images y.value) = .lt
  cases h : compare (images x.value) (images y.value) with
  | lt => rfl
  | eq => exact False.elim (hne (images_injective (Std.LawfulEqOrd.eq_of_compare h)))
  | gt => simp [le, h] at hle

/-- Remove adjacent equal values from a sorted list. Equal values keep the last
input reference in their stable-sort block. -/
@[expose] def compact : List (Generator S) → List (Generator S)
  | [] => []
  | x :: xs =>
    match compact xs with
    | [] => [x]
    | y :: ys => if x.value = y.value then y :: ys else x :: y :: ys

theorem compact_sublist (xs : List (Generator S)) : (compact xs).Sublist xs := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [compact]
    cases hc : compact xs with
    | nil => exact .cons_cons _ (List.nil_sublist _)
    | cons y ys =>
      rw [hc] at ih
      dsimp only
      split
      · exact .cons _ ih
      · exact .cons_cons _ ih

theorem mem_compact (xs : List (Generator S)) (p : Perm n) :
    p ∈ (compact xs).map value ↔ p ∈ xs.map value := by
  induction xs with
  | nil => simp [compact]
  | cons x xs ih =>
    simp only [compact]
    cases hc : compact xs with
    | nil =>
      simp only [List.map_cons, List.mem_cons]
      rw [← ih]
      simp [hc]
    | cons y ys =>
      dsimp only
      simp only [hc, List.map_cons, List.mem_cons] at ih
      split
      · rename_i he
        simp [he, ← ih]
      · simp only [List.map_cons, List.mem_cons, ih]

theorem compact_sorted (xs : List (Generator S)) (hs : xs.Pairwise (fun x y => le x y = true)) :
    (compact xs).Pairwise (fun x y => Chain.before x.value y.value) := by
  induction xs with
  | nil => simp [compact]
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.pairwise_cons.mp hs
    have hi := ih hs
    simp only [compact]
    cases hc : compact xs with
    | nil => simp
    | cons y ys =>
      rw [hc] at hi
      dsimp only
      split
      · exact hi
      · rename_i hne
        have hxy := before_of_le (hx y ((compact_sublist xs).subset (by simp [hc]))) hne
        apply List.pairwise_cons.mpr ⟨?_, hi⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact Chain.before_trans hxy ((List.pairwise_cons.mp hi).1 z hz)

/-- Expand signed references in input-index order. -/
@[expose] def candidates (S : Array (Perm n)) : List (Generator S) :=
  (List.finRange S.size).flatMap fun i => [ofIndex S i false, ofIndex S i true]

theorem mem_candidates (S : Array (Perm n)) (p : Perm n) :
    p ∈ (candidates S).map value ↔ ∃ i : Fin S.size, p = S[i.val] ∨ p = S[i.val].inv := by
  simp [candidates, ofIndex, Word.letter, eq_comm]
  constructor
  · rintro ⟨x, ⟨i, rfl | rfl⟩, rfl⟩
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨_, ⟨i, Or.inl rfl⟩, rfl⟩
    · exact ⟨_, ⟨i, Or.inr rfl⟩, rfl⟩

/-- Sort the nonidentity signed inputs and keep one reference per permutation. -/
@[expose] def ordered (S : Array (Perm n)) : List (Generator S) :=
  compact (((candidates S).filter fun x => x.value ≠ Perm.id n).mergeSort le)

theorem mem_ordered (S : Array (Perm n)) (p : Perm n) :
    p ∈ (ordered S).map value ↔
      p ≠ Perm.id n ∧ ∃ i : Fin S.size, p = S[i.val] ∨ p = S[i.val].inv := by
  rw [ordered, mem_compact]
  simp only [List.mem_map, List.mem_mergeSort, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hne⟩, rfl⟩
    exact ⟨hne, (mem_candidates S x.value).mp (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
  · rintro ⟨hne, hp⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((mem_candidates S p).mpr hp)
    exact ⟨x, ⟨hx, hne⟩, rfl⟩

theorem ordered_pairwise (S : Array (Perm n)) :
    ((ordered S).map value).Pairwise Chain.before := by
  apply List.pairwise_map.mpr
  exact compact_sorted _ (List.pairwise_mergeSort le_trans le_total _)

theorem ordered_nodup (S : Array (Perm n)) : ((ordered S).map value).Nodup := by
  change ((ordered S).map value).Pairwise (fun x y => x ≠ y)
  apply (ordered_pairwise S).imp
  intro x y h he
  exact Chain.before_irrefl _ (he ▸ h)

/-- A signed original-generator reference needs at most two program nodes. -/
@[expose] def program (x : Generator S) : Program :=
  if x.source.2 then ⟨#[.generator x.source.1.val, .inv 0], 1⟩
  else ⟨#[.generator x.source.1.val], 0⟩

theorem check_program (x : Generator S) : checkWord S x.value x.program = true := by
  rw [x.valid]
  obtain ⟨p, ⟨i, b⟩, hv⟩ := x
  cases b <;> simp [program, checkWord, Word.letter, Program.eval, Program.evalCertified,
    Program.evalNodes, Program.evalNode, i.isLt]

end Generator

/-- A normalized symmetric working array with checked provenance in the original
input. Construction establishes both checker predicates unconditionally. -/
structure Normalized (S : Array (Perm n)) where
  generators : Array (Perm n)
  sources : Vector (Fin S.size × Bool) generators.size
  source_valid : ∀ j : Fin generators.size, generators[j.val] = Word.letter S sources[j.val]
  words : Vector Program generators.size
  normalized : Chain.Normalized S generators
  valid : checkWords S generators words = true

/-- Normalize without changing the original generator indexing used by programs. -/
@[expose] def normalize (S : Array (Perm n)) : Normalized S where
  generators := ((Generator.ordered S).map Generator.value).toArray
  sources := ⟨((Generator.ordered S).map Generator.source).toArray, by simp⟩
  source_valid := by
    intro j
    simpa using ((Generator.ordered S)[j.val]'(by simpa using j.isLt)).valid
  words := ⟨((Generator.ordered S).map Generator.program).toArray, by simp⟩
  normalized := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa using Generator.ordered_pairwise S
    · simpa using Generator.ordered_nodup S
    · intro j
      have hj := (Generator.mem_ordered S _).mp (by simpa using Array.getElem_mem j.isLt)
      refine ⟨by simpa using hj.1, ?_⟩
      apply List.mem_toArray.mpr
      apply (Generator.mem_ordered S _).mpr
      constructor
      · intro h
        have he := congrArg Perm.inv h
        simp at he
        exact hj.1 he
      · obtain ⟨i, hi | hi⟩ := hj.2
        · exact ⟨i, Or.inr (by simpa using congrArg Perm.inv hi)⟩
        · exact ⟨i, Or.inl (by simpa using congrArg Perm.inv hi)⟩
    · intro j
      exact ((Generator.mem_ordered S _).mp (by simpa using Array.getElem_mem j.isLt)).2
    · intro i
      by_cases hi : S[i.val] = Perm.id n
      · exact Or.inl hi
      · exact Or.inr (List.mem_toArray.mpr ((Generator.mem_ordered S _).mpr ⟨hi, i, Or.inl rfl⟩))
  valid := by
    apply decide_eq_true
    intro j
    simpa using ((Generator.ordered S)[j.val]'(by simpa using j.isLt)).check_program

namespace Normalized

variable {n : Nat} {S : Array (Perm n)}

theorem symmetric (c : Normalized S) (p : Perm n) (hp : p ∈ c.generators) :
    p.inv ∈ c.generators := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
  exact (c.normalized.1.2.2 ⟨i, hi⟩).2

theorem generated_iff (c : Normalized S) (p : Perm n) :
    Generated c.generators p ↔ Generated S p := by
  refine ⟨checkWords_sound c.valid, ?_⟩
  apply Generated.mono
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hq
  rcases c.normalized.2.2 ⟨i, hi⟩ with he | hm
  · exact he ▸ Generated.id
  · exact .generator hm

theorem fixed (c : Normalized S) {base : Nat} (h : Chain.Fixed base S) :
    Chain.Fixed base c.generators := by
  intro j x hx
  obtain ⟨i, hi | hi⟩ := c.normalized.2.1 j
  · simpa only [hi] using h i x hx
  · have he := congrArg S[i.val].inv.get (h i x hx)
    simpa only [hi, Perm.inv_get_get] using he.symm

/-- Transfer provenance through the signed original references retained by
normalization. Each output program uses one input program, optionally inverted. -/
@[expose] def wordsFrom (c : Normalized S) (words : Vector Program S.size) :
    Vector Program c.generators.size :=
  Hex.Vector.ofFn' fun j =>
    let source := c.sources[j.val]
    if source.2 then words[source.1.val].inv else words[source.1.val]

theorem check_wordsFrom (c : Normalized S) {T : Array (Perm n)}
    (words : Vector Program S.size) (h : checkWords T S words = true) :
    checkWords T c.generators (c.wordsFrom words) = true := by
  apply decide_eq_true
  intro j
  have hw := (of_decide_eq_true h) c.sources[j.val].1
  have hv := c.source_valid j
  simp only [wordsFrom, Hex.Vector.getElem_ofFn']
  unfold Word.letter at hv
  split
  · rename_i hb
    simp [hb] at hv
    apply decide_eq_true
    simpa only [hv] using Program.eval_inv (of_decide_eq_true hw)
  · rename_i hb
    simp [hb] at hv
    simpa only [hv] using hw

end Normalized

end Hex.PermGroup
