/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Series

public section

namespace Hex.PermGroup.Series

/-- Every strict derived subgroup is retained. A negative terminal certificate
also retains the derived subgroup and its checked equality with its parent. -/
inductive Certificate (n : Nat) where
  | trivial
  | perfect (group : Group n) (derived : Derived.Certificate n)
  | step (group : Group n) (derived : Derived.Certificate n) (tail : Certificate n)

@[expose] def Certificate.accepted : Certificate n → Bool
  | .trivial => true
  | .perfect _ _ => false
  | .step _ _ tail => tail.accepted

/-- Include the repeated terminal term when the series stops at a fixed point. -/
@[expose] def Certificate.orders (G : Group n) : Certificate n → List Nat
  | .trivial => [G.order]
  | .perfect H _ => [G.order, H.order]
  | .step H _ tail => G.order :: tail.orders H

@[expose] def Certificate.depth : Certificate n → Nat
  | .trivial | .perfect _ _ => 0
  | .step _ _ tail => tail.depth + 1

/-- Derived constructions include the terminal perfectness test. -/
@[expose] def Certificate.terms : Certificate n → Nat
  | .trivial => 0
  | .perfect _ _ => 1
  | .step _ _ tail => tail.terms + 1

@[expose] def Certificate.terminal (G : Group n) : Certificate n → Group n
  | .trivial | .perfect _ _ => G
  | .step H _ tail => tail.terminal H

/-- Complete series replay rejects missing derived steps, false fixed points
and nontrivial groups claimed to be trivial. -/
@[expose] def check (G : Group n) : Certificate n → Bool
  | .trivial => G.isTrivial
  | .perfect H c => !G.isTrivial && Derived.check G H c && H.sameGroup G
  | .step H c tail => Derived.check G H c && !H.sameGroup G && check H tail

theorem step_equiv {G H : Group n} {c : Derived.Certificate n} (h : Derived.check G H c = true) :
    G.IsSolvable ↔ H.IsSolvable :=
  G.solvable_derived.trans (Derived.check_spec h).solvable.symm

theorem perfect_false {G H : Group n} {c : Derived.Certificate n}
    (h : check G (.perfect H c) = true) : ¬G.IsSolvable := by
  simp only [check, Bool.and_eq_true] at h
  have hd := Derived.check_spec h.1.2
  have he := (H.sameGroup_iff G).mp h.2
  apply G.not_solvable_of_perfect (fun p => (hd p).symm.trans (he p))
  intro ht
  simp [Group.isTrivial, ht] at h

/-- Both positive and negative checked answers have the mathematical meaning
of solvability; no exhaustion branch is interpreted as a negative answer. -/
theorem check_spec {G : Group n} {c : Certificate n} (h : check G c = true) :
    c.accepted = true ↔ G.IsSolvable := by
  induction c generalizing G with
  | trivial =>
    have ht : G.order = 1 := of_decide_eq_true h
    exact ⟨fun _ => G.solvable_of_trivial ht, fun _ => rfl⟩
  | perfect H c =>
    have hn := perfect_false h
    exact ⟨fun h => Bool.noConfusion h, fun hs => False.elim (hn hs)⟩
  | step H c tail ih =>
    simp only [check, Bool.and_eq_true] at h
    exact (ih h.2).trans (step_equiv h.1.1).symm

/-- Complete replay proves the logarithmic bound on strict series steps. -/
theorem check_growth {G : Group n} {c : Certificate n} (h : check G c = true) :
    2 ^ c.depth * (c.terminal G).order ≤ G.order := by
  induction c generalizing G with
  | trivial => simp [Certificate.depth, Certificate.terminal]
  | perfect H d => simp [Certificate.depth, Certificate.terminal]
  | step H d tail ih =>
    simp only [check, Bool.and_eq_true] at h
    have hi : H.IsSubgroup G := fun p hp => G.derived_inside p ((Derived.check_spec h.1.1 p).mp hp)
    have hn : ¬SameGroup H G := by
      intro he
      have hh := (H.sameGroup_iff G).mpr he
      simp [hh] at h
    have hd := hi.order_double hn
    have hh := Nat.le_trans (Nat.mul_le_mul_left 2 (ih h.2)) hd
    simpa only [Certificate.depth, Certificate.terminal, Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

/-- A complete certificate, whose terminal tag determines the answer. -/
structure Result (G : Group n) where
  certificate : Certificate n
  checked : check G certificate = true

namespace Result

variable {G : Group n}

@[expose] def accepted (r : Result G) : Bool := r.certificate.accepted

theorem accepted_iff (r : Result G) : r.accepted = true ↔ G.IsSolvable := check_spec r.checked

@[expose] def trivial (G : Group n) (h : G.isTrivial = true) : Result G := ⟨.trivial, h⟩

@[expose] def perfect (G : Group n) (d : Derived.Result G) (ht : G.isTrivial ≠ true)
    (he : d.group.sameGroup G = true) : Result G :=
  ⟨.perfect d.group d.certificate, by
    simp only [check, Bool.and_eq_true]
    exact ⟨⟨by simp [Bool.eq_false_iff.mpr ht], d.checked⟩, he⟩⟩

@[expose] def prepend (G : Group n) (d : Derived.Result G) (he : d.group.sameGroup G ≠ true)
    (tail : Result d.group) : Result G :=
  ⟨.step d.group d.certificate tail.certificate, by
    simp only [check, Bool.and_eq_true]
    exact ⟨⟨d.checked, by simp [Bool.eq_false_iff.mpr he]⟩, tail.checked⟩⟩

end Result

theorem derived_decreases (G : Group n) (d : Derived.Result G) (he : d.group.sameGroup G ≠ true) :
    d.group.order < G.order := d.inside.order_lt fun hs => he ((d.group.sameGroup_iff G).mpr hs)

/-- A strict decrease at least halves the order. The proved bound cannot
expire before a trivial term or a certified nontrivial fixed point. -/
@[expose] def iterate (remaining : Nat) (G : Group n) (bound : G.order ≤ remaining) : Result G :=
  if ht : G.isTrivial = true then Result.trivial G ht
  else
    let d := Derived.build G
    if he : d.group.sameGroup G = true then Result.perfect G d ht he
    else
      have hd := derived_decreases G d he
      match remaining with
      | 0 => False.elim (by omega)
      | remaining + 1 =>
        Result.prepend G d he (iterate remaining d.group (by omega))

@[expose] def build (G : Group n) : Result G := iterate G.order G (Nat.le_refl _)

end Hex.PermGroup.Series

namespace Hex.PermGroup.Group

/-- Compute the complete derived series through its certified terminal term. -/
@[expose] def derivedSeries (G : Group n) : Series.Result G := Series.build G

@[expose] def isSolvable (G : Group n) : Bool := G.derivedSeries.accepted

theorem isSolvable_iff (G : Group n) : G.isSolvable = true ↔ G.IsSolvable := G.derivedSeries.accepted_iff

end Hex.PermGroup.Group
