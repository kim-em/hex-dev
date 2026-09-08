/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Rank
public import HexPermGroup.Subgroup
public import HexPermGroup.Word.Substitute

public section

namespace Hex.PermGroup.Chain

theorem base_lt {level : Level n} {tail : Chain n} {base : Nat}
    (h : (cons level tail).checkFrom base = true) : base < n := by
  unfold checkFrom at h
  split at h
  · assumption
  · cases h

theorem orbit_valid {level : Level n} {tail : Chain n} {base : Nat}
    (h : (cons level tail).checkFrom base = true) :
    level.orbit.Valid level.generators ⟨base, base_lt h⟩ := by
  unfold checkFrom at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

theorem suffix_checked {level : Level n} {tail : Chain n} {base : Nat}
    (h : (cons level tail).checkFrom base = true) : tail.checkFrom (base + 1) = true := by
  unfold checkFrom at h
  split at h
  · split at h
    · exact (of_decide_eq_true h).2.2.2.1
    · cases h
  · cases h

theorem suffix_words {level : Level n} {tail : Chain n} {base : Nat}
    (h : (cons level tail).checkFrom base = true) :
    checkWords level.generators tail.generators tail.words = true := by
  unfold checkFrom at h
  split at h
  · split at h
    · exact (of_decide_eq_true h).2.2.1
    · cases h
  · cases h

/-- Compile the representative product for a successful sift. Each transition
substitutes the next level's generators by their checked provenance programs,
sharing those replacements rather than expanding repeated references. -/
@[expose] def program : (c : Chain n) → (base : Nat) → c.checkFrom base = true →
    (digits : c.Choice) → {w : Program // checkWord c.generators (c.value digits) w = true}
  | .leaf S _, _, _, _ => ⟨⟨#[.id], 0⟩, by
      apply decide_eq_true
      simp [value, Program.eval, Program.evalCertified, Program.evalNodes, Program.evalNode]⟩
  | .cons level tail, base, h, digits =>
    let child := tail.program (base + 1) (suffix_checked h) digits.2
    let translated := Program.substitute level.generators tail.generators tail.words
      (suffix_words h) child.val child.property
    ⟨level.orbit.words[digits.1.val].comp translated, by
      apply decide_eq_true
      apply Program.eval_comp
      · exact of_decide_eq_true ((orbit_valid h).2.2.2.2.1 digits.1).1
      · exact of_decide_eq_true (Program.check_substitute ..)⟩

end Hex.PermGroup.Chain

namespace Hex.PermGroup.Group

/-- Translate a chain representative product into the original input generators. -/
@[expose] def program (G : Group n) (digits : G.chain.Choice) : Program :=
  let localWord := G.chain.program 0 G.checked digits
  Program.substitute G.generators G.chain.generators G.chain.words
    (of_decide_eq_true G.valid).2.1 localWord.val localWord.property

theorem check_program (G : Group n) (digits : G.chain.Choice) :
    checkWord G.generators (G.chain.value digits) (G.program digits) = true :=
  Program.check_substitute ..

/-- A checked program in the original generators exactly when the complete sift
accepts. Negative queries do not allocate membership programs. -/
@[expose] def word? (G : Group n) (p : Perm n) : Option Program :=
  (G.chain.choose 0 p).map G.program

theorem word?_isSome (G : Group n) (p : Perm n) : (G.word? p).isSome = G.contains p := by
  rw [word?, Option.isSome_map, Chain.choose_isSome]
  rfl

theorem word?_sound (G : Group n) (p : Perm n) (w : Program) (h : G.word? p = some w) :
    checkWord G.generators p w = true := by
  obtain ⟨digits, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  have he := Chain.choose_sound hd
  simpa only [he] using G.check_program digits

theorem word?_complete (G : Group n) (p : Perm n) :
    (∃ w : Program, G.word? p = some w ∧ checkWord G.generators p w = true) ↔
      Generated G.generators p := by
  constructor
  · rintro ⟨w, _, hw⟩
    exact checkWord_sound hw
  · intro hp
    have he : (G.word? p).isSome = true := by rw [word?_isSome]; exact (G.contains_iff p).mpr hp
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp he
    exact ⟨w, hw, G.word?_sound p w hw⟩

/-- Positive containment certificates, one checked membership program for each
original generator of the smaller group. -/
@[expose] def subgroupWords (H G : Group n) (h : H.IsSubgroup G) :
    Vector Program H.generators.size :=
  Hex.Vector.ofFn' fun i => (G.word? H.generators[i.val]).get (by
    rw [word?_isSome]
    exact (G.contains_iff _).mpr (h _ (.generator (Array.getElem_mem i.isLt))))

theorem check_subgroupWords (H G : Group n) (h : H.IsSubgroup G) :
    checkWords G.generators H.generators (H.subgroupWords G h) = true := by
  apply decide_eq_true
  intro i
  apply G.word?_sound
  simp [subgroupWords]

/-- Decide containment and, on success, retain the original generators' words. -/
@[expose] def subgroupWords? (H G : Group n) : Option (Vector Program H.generators.size) :=
  if h : H.isSubgroup G = true then some (H.subgroupWords G ((isSubgroup_iff H G).mp h))
  else none

theorem subgroupWords?_isSome (H G : Group n) :
    (H.subgroupWords? G).isSome = H.isSubgroup G := by
  unfold subgroupWords?
  split <;> simp_all

theorem subgroupWords?_sound (H G : Group n) (words : Vector Program H.generators.size)
    (h : H.subgroupWords? G = some words) : checkWords G.generators H.generators words = true := by
  unfold subgroupWords? at h
  split at h
  · cases Option.some.inj h
    exact check_subgroupWords ..
  · cases h

end Hex.PermGroup.Group
