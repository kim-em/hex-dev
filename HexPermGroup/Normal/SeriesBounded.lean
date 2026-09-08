/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Solvable

public section

namespace Hex.PermGroup.Series

/-- A bounded run either has a complete terminal certificate or retains a
checked prefix ending at a pending group. Pending does not mean nonsolvable. -/
inductive Partial (n : Nat) where
  | pending
  | complete (certificate : Certificate n)
  | step (group : Group n) (derived : Derived.Certificate n) (tail : Partial n)

@[expose] def Partial.check (G : Group n) : Partial n → Bool
  | .pending => !G.isTrivial
  | .complete c => Series.check G c
  | .step H c tail => Derived.check G H c && !H.sameGroup G && tail.check H

@[expose] def Partial.complete? : Partial n → Option (Certificate n)
  | .pending => none
  | .complete c => some c
  | .step H c tail => tail.complete?.map (Certificate.step H c)

@[expose] def Partial.terms : Partial n → Nat
  | .pending => 0
  | .complete c => c.terms
  | .step _ _ tail => tail.terms + 1

theorem Partial.complete_checked {G : Group n} {p : Partial n} {c : Certificate n}
    (h : p.check G = true) (hc : p.complete? = some c) : Series.check G c = true := by
  induction p generalizing G c with
  | pending => cases hc
  | complete d => cases Option.some.inj hc; exact h
  | step H d tail ih =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hc
    simp only [Partial.check, Bool.and_eq_true] at h
    simp only [Series.check, Bool.and_eq_true]
    exact ⟨h.1, ih h.2 ht⟩

structure BoundedResult (G : Group n) where
  certificate : Partial n
  checked : certificate.check G = true

namespace BoundedResult

variable {G : Group n}

/-- `none` means the checked prefix has not reached a terminal group. -/
@[expose] def answer? (r : BoundedResult G) : Option Bool := r.certificate.complete?.map Certificate.accepted

theorem answer_spec (r : BoundedResult G) {b : Bool} (h : r.answer? = some b) :
    b = true ↔ G.IsSolvable := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  exact check_spec (r.certificate.complete_checked r.checked hc)

@[expose] def ofResult (r : Result G) : BoundedResult G := ⟨.complete r.certificate, r.checked⟩

@[expose] def pending (G : Group n) (h : G.isTrivial ≠ true) : BoundedResult G :=
  ⟨.pending, by simp [Partial.check, Bool.eq_false_iff.mpr h]⟩

@[expose] def prepend (G : Group n) (d : Derived.Result G) (h : d.group.sameGroup G ≠ true)
    (tail : BoundedResult d.group) : BoundedResult G :=
  ⟨.step d.group d.certificate tail.certificate, by
    simp only [Partial.check, Bool.and_eq_true]
    exact ⟨⟨d.checked, by simp [Bool.eq_false_iff.mpr h]⟩, tail.checked⟩⟩

end BoundedResult

/-- The cap counts derived-subgroup constructions, including the terminal
fixed-point check. It is checked before the next commutator array is built. -/
@[expose] def bounded (terms : Nat) (G : Group n) : BoundedResult G :=
  if ht : G.isTrivial = true then .ofResult (Result.trivial G ht)
  else
    match terms with
    | 0 => .pending G ht
    | terms + 1 =>
      let d := Derived.build G
      if he : d.group.sameGroup G = true then .ofResult (Result.perfect G d ht he)
      else .prepend G d he (bounded terms d.group)

theorem bounded_terms (terms : Nat) (G : Group n) : (bounded terms G).certificate.terms ≤ terms := by
  induction terms generalizing G with
  | zero =>
    rw [bounded]
    split <;> simp [BoundedResult.ofResult, Result.trivial, BoundedResult.pending,
      Partial.terms, Certificate.terms]
  | succ terms ih =>
    rw [bounded]
    split
    · simp [BoundedResult.ofResult, Result.trivial, Partial.terms, Certificate.terms]
    · dsimp only
      split
      · simp [BoundedResult.ofResult, Result.perfect, Partial.terms, Certificate.terms]
      · simpa only [BoundedResult.prepend, Partial.terms] using
          Nat.succ_le_succ (ih (Derived.build G).group)

end Hex.PermGroup.Series

namespace Hex.PermGroup.Group

/-- A bounded derived series preserves its complete checked prefix on
exhaustion; only terminal certificates produce a Boolean solvability answer. -/
@[expose] def derivedSeriesWith (G : Group n) (terms : Nat) : Series.BoundedResult G := Series.bounded terms G

end Hex.PermGroup.Group
