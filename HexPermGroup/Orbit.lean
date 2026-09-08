/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word

public section

namespace Hex.PermGroup

/-- Raw orbit certificate. Shape indices are checked when decoding the arrays;
mathematical validity is established independently by `checkOrbit`. -/
structure Orbit (n : Nat) where
  points : Array (Fin n)
  lookup : Vector (Option (Fin points.size)) n
  reps : Vector (Perm n) points.size
  words : Vector Program points.size

namespace Orbit

/-- Finite checks for both reachability and closure. Closure includes inverse
input generators, so the check accepts arbitrary original generator arrays. -/
@[expose] def Valid (S : Array (Perm n)) (a : Fin n) (c : Orbit n) : Prop :=
  c.points.toList.Nodup ∧ a ∈ c.points ∧
  (∀ j : Fin c.points.size, c.lookup[c.points[j.val].val] = some j) ∧
  (∀ x : Fin n,
    (c.lookup[x.val] = none ↔ x ∉ c.points) ∧
    ∀ j : Fin c.points.size, c.lookup[x.val] = some j → c.points[j.val] = x) ∧
  (∀ j : Fin c.points.size,
    checkWord S c.reps[j.val] c.words[j.val] = true ∧
    c.reps[j.val].get a = c.points[j.val] ∧
    (c.points[j.val] = a → c.reps[j.val] = Perm.id n)) ∧
  (∀ i : Fin S.size, ∀ j : Fin c.points.size,
    S[i.val].get c.points[j.val] ∈ c.points ∧
    S[i.val].inv.get c.points[j.val] ∈ c.points)

instance (S : Array (Perm n)) (a : Fin n) (c : Orbit n) : Decidable (Valid S a c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Generator closure implies invariance under every generated permutation. -/
theorem Valid.invariant {S : Array (Perm n)} {a : Fin n} {c : Orbit n}
    (h : Valid S a c) {p : Perm n} (hp : Generated S p) (x : Fin n) :
    x ∈ c.points ↔ p.get x ∈ c.points := by
  induction hp generalizing x with
  | id => simp
  | generator hs =>
    rcases Array.mem_iff_getElem.mp hs with ⟨i, hi, rfl⟩
    have hc : ∀ y ∈ c.points,
        S[i].get y ∈ c.points ∧ S[i].inv.get y ∈ c.points := by
      intro y hy
      rcases Array.mem_iff_getElem.mp hy with ⟨j, hj, rfl⟩
      exact h.2.2.2.2.2 ⟨i, hi⟩ ⟨j, hj⟩
    constructor
    · exact fun hx => (hc x hx).1
    · intro hx
      simpa using (hc (S[i].get x) hx).2
  | @comp p q _ _ hp hq =>
    simpa using (hq x).trans (hp (q.get x))
  | @inv p _ hp =>
    simpa using (hp (p.inv.get x)).symm

/-- Reachability and closure together identify the full orbit. -/
theorem Valid.mem_iff {S : Array (Perm n)} {a : Fin n} {c : Orbit n}
    (h : Valid S a c) (x : Fin n) :
    x ∈ c.points ↔ ∃ p : Perm n, Generated S p ∧ p.get a = x := by
  constructor
  · intro hx
    rcases Array.mem_iff_getElem.mp hx with ⟨j, hj, hpoint⟩
    have hw := h.2.2.2.2.1 ⟨j, hj⟩
    exact ⟨c.reps[j], checkWord_sound hw.1, hw.2.1.trans hpoint⟩
  · rintro ⟨p, hp, rfl⟩
    exact (h.invariant hp a).mp h.2.1

end Orbit

/-- Independently check a complete point orbit and its transporters. -/
@[expose] def checkOrbit (S : Array (Perm n)) (a : Fin n) (c : Orbit n) : Bool :=
  decide (c.Valid S a)

theorem checkOrbit_sound {S : Array (Perm n)} {a : Fin n} {c : Orbit n}
    (h : checkOrbit S a c = true) (x : Fin n) :
    x ∈ c.points ↔ ∃ p : Perm n, Generated S p ∧ p.get a = x :=
  (of_decide_eq_true h : c.Valid S a).mem_iff x

end Hex.PermGroup
