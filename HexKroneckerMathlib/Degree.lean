/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Injectivity

public section

namespace Hex.Kronecker

@[simp] theorem length_zeroDegrees (k : Nat) : (zeroDegrees k).length = k := by
  induction k <;> simp [zeroDegrees, *]

@[simp] theorem length_atomDegrees (k i : Nat) : (atomDegrees k i).length = k := by
  induction k generalizing i <;> cases i <;> simp [atomDegrees, *]

@[simp] theorem length_maxDegrees (a b : List Nat) :
    (maxDegrees a b).length = max a.length b.length := by
  induction a generalizing b <;> cases b <;> simp [maxDegrees, *, Nat.succ_max_succ]

@[simp] theorem length_addDegrees (a b : List Nat) :
    (addDegrees a b).length = max a.length b.length := by
  induction a generalizing b <;> cases b <;> simp [addDegrees, *, Nat.succ_max_succ]

@[simp] theorem length_scaleDegrees (n : Nat) (a : List Nat) :
    (scaleDegrees n a).length = a.length := by
  induction a <;> simp [scaleDegrees, *]

@[simp] theorem Expr.length_degrees (k : Nat) (e : Expr) : (e.degrees k).length = k := by
  induction e <;> simp_all [Expr.degrees]

@[simp] theorem getD_zeroDegrees (k i : Nat) : (zeroDegrees k).getD i 0 = 0 := by
  induction k generalizing i <;> cases i <;>
    simp only [zeroDegrees, List.getD_nil, List.getD_cons_zero, List.getD_cons_succ, *]

theorem getD_atomDegrees (k i j : Nat) (hj : j < k) :
    (atomDegrees k i).getD j 0 = if j = i then 1 else 0 := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
      cases i with
      | zero => cases j <;> simp only [atomDegrees, List.getD_cons_zero,
          List.getD_cons_succ, getD_zeroDegrees, Nat.succ_ne_zero, ↓reduceIte]
      | succ i => cases j with
        | zero => simp [atomDegrees]
        | succ j =>
            simpa only [atomDegrees, List.getD_cons_succ, Nat.succ.injEq] using
              ih i j (by omega)

@[simp] theorem getD_maxDegrees (a b : List Nat) (i : Nat) :
    (maxDegrees a b).getD i 0 = max (a.getD i 0) (b.getD i 0) := by
  induction a generalizing b i with
  | nil => simp only [maxDegrees, List.getD_nil, Nat.zero_max]
  | cons a as ih => cases b <;> cases i <;> simp only [maxDegrees,
      List.getD_nil, List.getD_cons_zero, List.getD_cons_succ, ih, Nat.max_zero]

@[simp] theorem getD_addDegrees (a b : List Nat) (i : Nat) :
    (addDegrees a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp only [addDegrees, List.getD_nil, Nat.zero_add]
  | cons a as ih => cases b <;> cases i <;> simp only [addDegrees,
      List.getD_nil, List.getD_cons_zero, List.getD_cons_succ, ih, Nat.add_zero]

@[simp] theorem getD_scaleDegrees (n : Nat) (a : List Nat) (i : Nat) :
    (scaleDegrees n a).getD i 0 = n * a.getD i 0 := by
  induction a generalizing i <;> cases i <;> simp only [scaleDegrees,
    List.getD_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, *]

theorem Expr.degreeOf_le {k : Nat} (e : Expr) (h : e.WellFormed k) (i : Fin k) :
    MvPolynomial.degreeOf i (e.toMvPolynomial h) ≤ (e.degrees k).getD i.val 0 := by
  induction e with
  | int z =>
      change MvPolynomial.degreeOf i (MvPolynomial.C z) ≤ (zeroDegrees k).getD i.val 0
      rw [MvPolynomial.degreeOf_C, getD_zeroDegrees]
  | atom j =>
      change MvPolynomial.degreeOf i (MvPolynomial.X (⟨j, Nat.le_of_ble_eq_true h⟩ : Fin k)) ≤
        (atomDegrees k j).getD i.val 0
      rw [MvPolynomial.degreeOf_X, getD_atomDegrees k j i.val i.isLt]
      simp only [Fin.ext_iff, le_refl]
  | add a b ha hb =>
      rw [Expr.degrees, getD_maxDegrees]
      exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le_max (ha _) (hb _))
  | sub a b ha hb =>
      rw [Expr.degrees, getD_maxDegrees]
      exact (MvPolynomial.degreeOf_sub_le i _ _).trans (max_le_max (ha _) (hb _))
  | neg a ha =>
      change MvPolynomial.degreeOf i (-a.toMvPolynomial h) ≤ (a.degrees k).getD i.val 0
      rw [MvPolynomial.degreeOf_neg]
      exact ha h
  | mul a b ha hb =>
      rw [Expr.degrees, getD_addDegrees]
      exact (MvPolynomial.degreeOf_mul_le i _ _).trans (Nat.add_le_add (ha _) (hb _))
  | pow a n ha =>
      rw [Expr.degrees, getD_scaleDegrees]
      exact (MvPolynomial.degreeOf_pow_le i _ n).trans (Nat.mul_le_mul_left n (ha _))

theorem Expr.inBox {k : Nat} (e : Expr) (h : e.WellFormed k) :
    InBox (e.degrees k) (e.toMvPolynomial h) := by
  intro d hd
  apply box_ofFn _ (e.length_degrees k) (fun i => d i)
  intro i
  exact (MvPolynomial.monomial_le_degreeOf i hd).trans (e.degreeOf_le h i)

theorem forall₂_getD {a b : List Nat} (h : List.Forall₂ (· ≤ ·) a b) (i : Nat) :
    a.getD i 0 ≤ b.getD i 0 := by
  induction h generalizing i <;> cases i <;> simp only [List.getD_nil,
    List.getD_cons_zero, List.getD_cons_succ, Nat.le_refl, *]

theorem InBox.mono {k : Nat} {ds es : List Nat} (he : es.length = k)
    {p : MvPolynomial (Fin k) Int} (hp : InBox ds p)
    (h : ∀ i : Fin k, ds.getD i.val 0 ≤ es.getD i.val 0) : InBox es p := by
  intro d hdp
  apply box_ofFn es he (fun i => d i)
  intro i
  have ht := hp d hdp
  have hi := forall₂_getD ht i.val
  have hz : (List.ofFn fun j => d j).getD i.val 0 = d i := by
    simp [i.isLt]
  rw [hz] at hi
  exact hi.trans (h i)

end Hex.Kronecker
