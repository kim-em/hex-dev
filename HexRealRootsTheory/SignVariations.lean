/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Var
public import Mathlib.Data.List.SignVariations
import all HexRealRoots.Var

public section

namespace HexRealRootsTheory

/-- Two nonzero leading entries: `signVar` peels one sign-change decision and
recurses. Phrased through the public `Hex.signVar` (the internal `go` recursor is
module-private), using that a nonzero head survives the zero-filter. -/
private theorem signVar_cons_cons {a b : Int} (rest : List Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    Hex.signVar (a :: b :: rest)
      = (if a * b < 0 then 1 else 0) + Hex.signVar (b :: rest) := by
  have fa : (a :: b :: rest).filter (· != 0) = a :: b :: rest.filter (· != 0) := by
    rw [List.filter_cons, ite_eq_left (by simpa using ha), List.filter_cons, ite_eq_left (by simpa using hb)]
  have fb : (b :: rest).filter (· != 0) = b :: rest.filter (· != 0) := by
    rw [List.filter_cons, ite_eq_left (by simpa using hb)]
  unfold Hex.signVar
  rw [fa, fb]
  rfl

/-- On a zero-free integer list, the executable count agrees with Mathlib's count. -/
private theorem signVar_zeroFree : ∀ m : List Int, (∀ x ∈ m, x ≠ 0) →
    Hex.signVar m = m.signVariations
  | [], _ => rfl
  | [a], ha => by
      have ha0 : a ≠ 0 := ha a (by simp)
      simp [Hex.signVar, Hex.signVar.go, ha0]
  | a :: b :: rest, hne => by
      have ha : a ≠ 0 := hne a (by simp)
      have hb : b ≠ 0 := hne b (by simp)
      have hbne : ∀ x ∈ b :: rest, x ≠ 0 := fun x hx => hne x (List.mem_cons_of_mem _ hx)
      rw [signVar_cons_cons rest ha hb, List.signVariations_cons_cons_of_ne_zero rest ha hb,
        signVar_zeroFree (b :: rest) hbne, Nat.add_comm]
      congr 1
      simp only [← sign_eq_neg_one_iff, sign_mul]
      have ha' : SignType.sign a ≠ 0 := by simpa using ha
      have hb' : SignType.sign b ≠ 0 := by simpa using hb
      revert ha' hb'
      cases SignType.sign a <;> cases SignType.sign b <;> decide

/-- `signVar` reads only the zero-filtered list, so it is unchanged by
pre-filtering out zeros. -/
private theorem signVar_filter (l : List Int) :
    Hex.signVar l = Hex.signVar (l.filter (· != 0)) := by
  unfold Hex.signVar
  rw [List.filter_filter]
  simp only [Bool.and_self]

/-- The executable integer sign-variation count agrees with Mathlib's list API. -/
theorem signVar_eq_list (l : List Int) : Hex.signVar l = l.signVariations := by
  rw [signVar_filter, ← List.signVariations_filter_ne_zero l]
  exact signVar_zeroFree (l.filter (· != 0))
    (fun x hx => by simpa using (List.mem_filter.mp hx).2)

end HexRealRootsTheory
