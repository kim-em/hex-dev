/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Partition.Merge

public section

namespace Hex.PermGroup.Blocks

/-- A relation preserved by every supplied generator. -/
@[expose] def Invariant (S : Array (Perm n)) (R : Fin n → Fin n → Prop) : Prop :=
  ∀ s ∈ S, ∀ x y, R x y → R (s.get x) (s.get y)

/-- The equivalence relations admitted by a seeded block problem. -/
structure Admissible (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (R : Fin n → Fin n → Prop) : Prop where
  equivalence : Equivalence R
  invariant : Invariant S R
  seeds : ∀ q ∈ seeds, R q.1 q.2

/-- A merge is justified by a seed or by the image of two points already
in the same block. Its preimage is obtained from the checked permutation. -/
@[expose] def Forced (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (p : Partition n) (x y : Fin n) : Prop :=
  (x, y) ∈ seeds ∨ ∃ i : Fin S.size, p.Same (S[i.val].inv.get x) (S[i.val].inv.get y)

instance (S : Array (Perm n)) (seeds : List (Fin n × Fin n)) (p : Partition n)
    (x y : Fin n) : Decidable (Forced S seeds p x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Forced.mono {S : Array (Perm n)} {seeds : List (Fin n × Fin n)}
    {p q : Partition n} (h : p.Refines q.Same) {x y : Fin n}
    (hf : Forced S seeds p x y) : Forced S seeds q x y := by
  rcases hf with hs | ⟨i, hi⟩
  · exact Or.inl hs
  · exact Or.inr ⟨i, h _ _ hi⟩

theorem Forced.sound {S : Array (Perm n)} {seeds : List (Fin n × Fin n)}
    {p : Partition n} {R : Fin n → Fin n → Prop} (hR : Admissible S seeds R)
    (hp : p.Refines R) {x y : Fin n} (hf : Forced S seeds p x y) : R x y := by
  rcases hf with hs | ⟨i, hi⟩
  · exact hR.seeds _ hs
  · simpa using hR.invariant _ (Array.getElem_mem i.isLt) _ _ (hp _ _ hi)

/-- One test per point and generator suffices: a point's image must share a
block with its representative's image. No pair table is allocated. -/
@[expose] def checkInvariant (S : Array (Perm n)) (p : Partition n) : Bool :=
  decide (∀ i : Fin S.size, ∀ x : Fin n,
    p.Same (S[i.val].get x) (S[i.val].get p.labels[x.val]))

theorem checkInvariant_iff (S : Array (Perm n)) (p : Partition n) :
    checkInvariant S p = true ↔ Invariant S p.Same := by
  constructor
  · intro h s hs x y hxy
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hs
    have hx := of_decide_eq_true h ⟨i, hi⟩ x
    have hy := of_decide_eq_true h ⟨i, hi⟩ y
    exact hx.trans ((congrArg (fun a => p.labels[(S[i].get a).val]) hxy).trans hy.symm)
  · intro h
    exact decide_eq_true (fun i x => h _ (Array.getElem_mem i.isLt) _ _ (p.idem x).symm)

/-- Replay only effective forced unions. An untrusted trace may not introduce
an arbitrary merge, even if its final partition happens to be invariant. -/
@[expose] def replay (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (p : Partition n) : List (Fin n × Fin n) → Option (Partition n)
  | [] => some p
  | (x, y) :: rest =>
    if Forced S seeds p x y ∧ ¬p.Same x y then replay S seeds (p.merge x y) rest
    else none

theorem replay_append (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (p : Partition n) (xs ys : List (Fin n × Fin n)) :
    replay S seeds p (xs ++ ys) = (replay S seeds p xs).bind (fun q => replay S seeds q ys) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, replay]
    split
    · exact ih _
    · rfl

theorem replay_least {S : Array (Perm n)} {seeds trace : List (Fin n × Fin n)}
    {p q : Partition n} (h : replay S seeds p trace = some q)
    {R : Fin n → Fin n → Prop} (hR : Admissible S seeds R) (hp : p.Refines R) : q.Refines R := by
  induction trace generalizing p with
  | nil => cases Option.some.inj h; exact hp
  | cons x xs ih =>
    simp only [replay] at h
    split at h
    · rename_i hx
      exact ih h (p.merge_least _ _ hR.equivalence hp (hx.1.sound hR hp))
    · contradiction

/-- A successful replay records exactly one union per deleted root. -/
theorem replay_length {S : Array (Perm n)} {seeds trace : List (Fin n × Fin n)}
    {p q : Partition n} (h : replay S seeds p trace = some q) :
    q.roots.length + trace.length = p.roots.length := by
  induction trace generalizing p with
  | nil => cases Option.some.inj h; rfl
  | cons x xs ih =>
    simp only [replay] at h
    split at h
    · rename_i hx
      have hr := p.roots_merge _ _ hx.2
      have ht := ih h
      simp only [List.length_cons]
      omega
    · contradiction

/-- Completeness checks both the input seeds and terminal generator closure,
in addition to replaying the forced unions from the discrete partition. -/
@[expose] def check (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (p : Partition n) (trace : List (Fin n × Fin n)) : Bool :=
  decide (replay S seeds (Partition.discrete n) trace = some p) &&
    checkInvariant S p && decide (∀ q ∈ seeds, p.Same q.1 q.2)

/-- The checked partition is admissible and refines every admissible relation.
The second conclusion is the minimality obligation. -/
theorem check_spec {S : Array (Perm n)} {seeds trace : List (Fin n × Fin n)}
    {p : Partition n} (h : check S seeds p trace = true) :
    Admissible S seeds p.Same ∧
      ∀ R, Admissible S seeds R → p.Refines R := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, checkInvariant_iff] at h
  refine ⟨⟨p.equivalence, h.1.2, h.2⟩, ?_⟩
  intro R hR
  apply replay_least h.1.1 hR
  intro x y he
  exact (Partition.discrete_same x y).mp he ▸ hR.equivalence.refl x

end Hex.PermGroup.Blocks
