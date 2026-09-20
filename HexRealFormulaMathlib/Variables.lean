/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.Semantics
public import Mathlib.Algebra.BigOperators.Fin

public section

/-! Interpretation laws for coordinate removal, reordering, and binder exchange. -/

namespace Hex.RealFormula

open scoped BigOperators HexMvPolyMathlib

theorem QF.moveLast_correct (i : Fin (n + 1)) (p : QF (n + 1)) (ρ : Fin (n + 1) → ℝ) :
    (p.moveLast i).toProp ρ ↔ p.toProp (ρ ∘ exchange i ⟨n, Nat.lt_succ_self n⟩) :=
  p.rename_correct _ ρ

private theorem prod_remove (i : Fin (n + 1)) (m : Mono (n + 1))
    (ρ : Fin (n + 1) → ℝ) (h : m[i] = 0) :
    Mono.prod (ρ ∘ i.succAbove) (MvPoly.removeVar i m) = Mono.prod ρ m := by
  rw [HexMvPolyMathlib.monoProd_eq_prod, HexMvPolyMathlib.monoProd_eq_prod,
    Fin.prod_univ_succAbove _ i]
  have hm : HexMvPolyMathlib.monoEquiv m i = 0 := by simpa using h
  rw [hm, pow_zero, one_mul]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  by_cases hj : j.val < i.val <;> simp [MvPoly.removeVar, Fin.succAbove, Fin.lt_def, hj]

private theorem eval_remove (i : Fin (n + 1)) (p : Poly (n + 1))
    (ρ : Fin (n + 1) → ℝ) (h : p.degreeOf i = 0) :
    Poly.eval (MvPoly.ofTerms (p.termsList.map fun (m, c) => (MvPoly.removeVar i m, c)))
      (ρ ∘ i.succAbove) = p.eval ρ := by
  unfold Poly.eval
  rw [MvPoly.eval₂_ofTerms (f := Int.castRingHom ℝ) (x := ρ ∘ i.succAbove)
      (by simp) (by intros; simp),
    MvPoly.eval₂_eq, List.foldl_map]
  apply List.foldl_congr
  intro acc t ht
  have ht' : t.1 ∈ p.monomials := List.mem_map.mpr ⟨t, ht, rfl⟩
  have hm := MvPoly.degreeOf_monomial_le i p ht'
  rw [h] at hm
  rw [prod_remove i t.1 ρ (Nat.eq_zero_of_le_zero hm)]

/-- Removing an absent coordinate preserves the formula at the restricted valuation. -/
theorem QF.drop_correct (i : Fin (n + 1)) (p : QF (n + 1))
    (h : p.degree i = 0) (ρ : Fin (n + 1) → ℝ) :
    (p.drop i h).toProp (ρ ∘ i.succAbove) ↔ p.toProp ρ := by
  induction p with
  | atom a =>
    change a.cmp.toProp _ ↔ a.cmp.toProp _
    rw [eval_remove i a.p ρ h]
  | tt | ff => rfl
  | not p ih => exact not_congr (ih h)
  | and p q ihp ihq =>
    have hp : p.degree i = 0 := Nat.eq_zero_of_le_zero ((Nat.le_max_left ..).trans_eq h)
    have hq : q.degree i = 0 := Nat.eq_zero_of_le_zero ((Nat.le_max_right ..).trans_eq h)
    exact and_congr (ihp hp) (ihq hq)
  | or p q ihp ihq =>
    have hp : p.degree i = 0 := Nat.eq_zero_of_le_zero ((Nat.le_max_left ..).trans_eq h)
    have hq : q.degree i = 0 := Nat.eq_zero_of_le_zero ((Nat.le_max_right ..).trans_eq h)
    exact or_congr (ihp hp) (ihq hq)

/-- Converting another lawful order to the public lexicographic order preserves evaluation. -/
theorem Poly.reorder_correct {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (p : MvPoly n Int cmp) (ρ : Fin n → ℝ) :
    Poly.eval (MvPoly.reorder Mono.lex p) ρ = MvPoly.eval₂ (Int.castRingHom ℝ) ρ p := by
  unfold Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    HexMvPolyMathlib.toMvPolynomial_reorder, HexMvPolyMathlib.eval₂_toMvPolynomial]

theorem append_swap (ρ : Fin n → ℝ) (x y : ℝ) :
    append (append ρ x) y ∘ swapLast = append (append ρ y) x := by
  funext i
  by_cases hi : i.val = n
  · simp [swapLast, append, hi]
  · by_cases hj : i.val = n + 1
    · simp [swapLast, append, hj]
    · have hn : i.val < n := by omega
      simp [swapLast, append, hi, hj, hn, Nat.lt_succ_of_lt hn]

/-- The checked exchange never permutes a quantifier alternation. -/
theorem Prenex.swap_correct (depth : Nat) (p q : Prenex n) (ρ : Fin n → ℝ)
    (h : p.swap? depth = some q) : q.toProp ρ ↔ p.toProp ρ := by
  induction depth generalizing n with
  | zero =>
    cases p with
    | matrix _ => simp [swap?] at h
    | quant k p =>
      cases p with
      | matrix _ => simp [swap?] at h
      | quant l p =>
        simp only [swap?] at h
        split at h
        · rename_i hkl
          have : k = l := by simpa using hkl
          subst l
          cases h
          cases k <;> simp only [toProp, rename_correct, append_swap]
          · exact exists_comm
          · exact forall_comm
        · contradiction
  | succ depth ih =>
    cases p with
    | matrix _ => simp [swap?] at h
    | quant k p =>
      cases hs : p.swap? depth with
      | none => simp [swap?, hs] at h
      | some p' =>
        simp [swap?, hs] at h
        subst q
        cases k
        · exact exists_congr fun x => ih p p' (append ρ x) hs
        · exact forall_congr' fun x => ih p p' (append ρ x) hs

end Hex.RealFormula
