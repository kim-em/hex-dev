/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Node
public import HexPermGroup.Search.Trials

public section

namespace Hex.PermGroup.Search

/-- An executable subgroup predicate. Closure is proved for the actual test
used at leaves and on the result group's generators. -/
structure Predicate (n : Nat) where
  test : Perm n → Bool
  id : test (Perm.id n) = true
  comp : ∀ p q, test p = true → test q = true → test (p.comp q) = true
  inv : ∀ p, test p = true → test p.inv = true

theorem Predicate.generated (P : Predicate n) {S : Array (Perm n)}
    (h : ∀ i : Fin S.size, P.test S[i.val] = true) {p : Perm n} (hp : Generated S p) : P.test p = true := by
  apply hp.lift (P := fun p => P.test p = true) P.id
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hq
    exact h ⟨i, hi⟩
  · exact P.comp
  · exact P.inv

/-- Membership in a second checked group is a subgroup predicate even when
neither group is contained in the other. -/
@[expose] def Predicate.subgroup (H : Group n) : Predicate n where
  test := H.contains
  id := (H.contains_iff _).mpr .id
  comp _ _ hp hq := (H.contains_iff _).mpr
    (((H.contains_iff _).mp hp).comp ((H.contains_iff _).mp hq))
  inv _ hp := (H.contains_iff _).mpr (((H.contains_iff _).mp hp).inv)

/-- A refinement provides a replayable reason for excluding a whole prefix
coset. Its checker must prove impossibility for every completion of that node. -/
structure Pruner (G : Group n) (test : Perm n → Bool) where
  Reason : Type
  reject : Node G → Reason → Bool
  sound : ∀ t r, reject t r = true → ∀ p, t.Contains p → test p = false
  trials : Node G → Trials Reason

@[expose] def Pruner.find {G : Group n} {test : Perm n → Bool} (C : Pruner G test) (t : Node G) :
    Option C.Reason := (C.trials t).find (C.reject t)

theorem Pruner.checked {G : Group n} {test : Perm n → Bool} (C : Pruner G test) (t : Node G) (r : C.Reason)
    (h : C.find t = some r) : C.reject t r = true := (C.trials t).find_checked (C.reject t) r h

theorem Pruner.find_none {G : Group n} {test : Perm n → Bool} (C : Pruner G test) (t : Node G) :
    C.find t = none ↔ ∀ i : Fin (C.trials t).size, C.reject t ((C.trials t).get i) = false :=
  (C.trials t).find_none (C.reject t)

/-- Bounded refinement counts individual rejection tests and distinguishes an
unfinished scan from a completed scan that found no rejecting reason. -/
@[expose] def Pruner.findWith {G : Group n} {test : Perm n → Bool} (C : Pruner G test)
    (t : Node G) (capacity : Nat) : Trials.Run (C.trials t) (C.reject t) 0 capacity :=
  (C.trials t).scan (C.reject t) 0 capacity

/-- Subgroup search specializes the same pruning interface used by transporter
search to a predicate closed under the group operations. -/
abbrev Constraint (G : Group n) (P : Predicate n) := Pruner G P.test

/-- The absence of additional refinement still leaves exact leaf checking and
the subgroup-containment pruning rule available. -/
@[expose] def Constraint.none (G : Group n) (P : Predicate n) : Constraint G P where
  Reason := Empty
  reject _ r := nomatch r
  sound _ r := nomatch r
  trials _ := .empty

/-- A deterministic impossibility test whose complete input is already in
the node needs no additional witness data. -/
@[expose] def Constraint.ofTest {G : Group n} {P : Predicate n} (reject : Node G → Bool)
    (sound : ∀ t, reject t = true → ∀ p, t.Contains p → P.test p = false) : Constraint G P where
  Reason := Unit
  reject t _ := reject t
  sound t _ := sound t
  trials _ := .singleton ()

/-- Try the first refinement, then the second, preserving which rejection
checker must be replayed. -/
@[expose] def Constraint.combine {G : Group n} {P : Predicate n}
    (C D : Constraint G P) : Constraint G P where
  Reason := Sum C.Reason D.Reason
  reject t r := match r with
    | .inl r => C.reject t r
    | .inr r => D.reject t r
  sound t r := by
    cases r with
    | inl r => exact C.sound t r
    | inr r => exact D.sound t r
  trials t := ((C.trials t).map Sum.inl).append ((D.trials t).map Sum.inr)

namespace Node

variable {G : Group n}

/-- A whole prefix coset is contained in a checked group when its prefix and
all suffix generators belong to that group. -/
@[expose] def covered (t : Node G) (K : Group n) : Bool :=
  K.contains t.rep.val && decide (∀ i : Fin t.suffix.generators.size, K.contains t.suffix.generators[i.val] = true)

theorem covered_sound (t : Node G) (K : Group n) (h : t.covered K = true)
    {p : Perm n} (hp : t.Contains p) : Generated K.generators p := by
  simp only [covered, Bool.and_eq_true] at h
  obtain ⟨hr, hs⟩ := h
  have hrep := (K.contains_iff t.rep.val).mp hr
  have htail : Generated K.generators (t.rep.val.inv.comp p) := by
    apply hp.mono
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hq
    exact (K.contains_iff _).mp ((of_decide_eq_true hs) ⟨i, hi⟩)
  simpa [← Perm.comp_assoc] using hrep.comp htail

theorem covered_mono (t : Node G) {K L : Group n} (hkl : K.IsSubgroup L)
    (h : t.covered K = true) : t.covered L = true := by
  simp only [covered, Bool.and_eq_true] at h
  obtain ⟨hr, hs⟩ := h
  rw [covered, Bool.and_eq_true]
  refine ⟨(L.contains_iff _).mpr (hkl _ ((K.contains_iff _).mp hr)), ?_⟩
  apply decide_eq_true
  intro i
  exact (L.contains_iff _).mpr (hkl _ ((K.contains_iff _).mp ((of_decide_eq_true hs) i)))

end Node

end Hex.PermGroup.Search
