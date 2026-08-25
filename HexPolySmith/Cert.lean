/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Structure

public section

/-! Direct and evaluation-based certificate checkers. -/

namespace Hex.PolyMatrix

universe u

open Hex

/-- Accept `(S,T)` as a Smith form of `A`, where `T = S.left * A`. -/
@[expose]
def snfCert {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (S : SmithData F n m)
    (T : Matrix (DensePoly F) n m) : Bool :=
  (S.left * A == T)
    && (T * S.right == Matrix.diagMatrix S.diag n m)
    && (S.left * S.leftInv == polyIdentity n)
    && (S.right * S.rightInv == polyIdentity m)
    && isSNFShape S

/-- Every accepted direct certificate satisfies the Smith contract. -/
theorem snfCert_sound {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {S : SmithData F n m}
    {T : Matrix (DensePoly F) n m} (h : snfCert A S T = true) :
    IsSNF A S := by
  simp only [snfCert, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hleft, hright⟩, hleftInv⟩, hrightInv⟩, hshape⟩
  have hleft' : S.left * A = T := eq_of_beq hleft
  have hright' : T * S.right = Matrix.diagMatrix S.diag n m := eq_of_beq hright
  have hleftInv' : S.left * S.leftInv = polyIdentity n := eq_of_beq hleftInv
  have hrightInv' : S.right * S.rightInv = polyIdentity m := eq_of_beq hrightInv
  rw [polyIdentity_eq_identity] at hleftInv'
  rw [polyIdentity_eq_identity] at hrightInv'
  rcases isSNFShape_sound hshape with ⟨hrn, hrm, hmonic, hchain⟩
  refine
    { left_inv := hleftInv'
      right_inv := hrightInv'
      mul_eq := ?_
      rank_le_n := hrn
      rank_le_m := hrm
      diag_monic := hmonic
      chain := hchain }
  calc
    S.left * A * S.right = T * S.right := by rw [hleft']
    _ = Matrix.diagMatrix S.diag n m := hright'

/-- Evaluate every entry of a polynomial matrix at `x`. -/
@[expose]
def evalMatrix {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (x : F) : Matrix F n m :=
  Matrix.ofFn fun i j => DensePoly.evalImpl A[(i, j)] x

private theorem eval_foldl_products {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {k : Nat} (xs : List (Fin k))
    (p q : Fin k → DensePoly F) (acc : DensePoly F) (x : F) :
    DensePoly.eval
        (xs.foldl (fun z i => z + p i * q i) acc) x =
      xs.foldl
        (fun z i => z + DensePoly.eval (p i) x * DensePoly.eval (q i) x)
        (DensePoly.eval acc x) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih, DensePoly.eval_add_semiring, DensePoly.eval_mul_commring]

private theorem evalImpl_foldl_products {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {k : Nat} (xs : List (Fin k))
    (p q : Fin k → DensePoly F) (acc : DensePoly F) (x : F) :
    DensePoly.evalImpl
        (xs.foldl (fun z i => z + p i * q i) acc) x =
      xs.foldl
        (fun z i => z + DensePoly.evalImpl (p i) x * DensePoly.evalImpl (q i) x)
        (DensePoly.evalImpl acc x) := by
  rw [← DensePoly.eval_eq_evalImpl]
  have h := eval_foldl_products xs p q acc x
  simpa only [DensePoly.eval_eq_evalImpl] using h

/-- Entrywise polynomial evaluation commutes with matrix multiplication. -/
theorem evalMatrix_mul {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m k : Nat} (A : Matrix (DensePoly F) n m)
    (B : Matrix (DensePoly F) m k) (x : F) :
    evalMatrix (A * B) x = Matrix.mulImpl (evalMatrix A x) (evalMatrix B x) := by
  rw [← Matrix.mul_eq_mulImpl]
  apply Matrix.ext_getElem
  intro i j
  unfold evalMatrix
  rw [Matrix.getElem_ofFn, Matrix.getElem_pair_eq_nested, Matrix.getElem_mul]
  unfold Matrix.mul
  rw [Matrix.getElem_ofFn]
  simp only [Matrix.getElem_row, Matrix.getElem_col, Matrix.getElem_ofFn,
    Vector.dotProduct]
  have hzero : DensePoly.evalImpl (0 : DensePoly F) x = 0 := by
    rw [← DensePoly.eval_eq_evalImpl]
    exact DensePoly.eval_zero x
  simpa only [Matrix.getElem_pair_eq_nested, hzero] using
    (evalImpl_foldl_products (List.finRange m)
      (fun l => A[i][l]) (fun l => B[l][j]) 0 x)

/-- The supplied points separate polynomials through degree `D`. This is the
semantic premise used by the evaluation checker; pairwise-distinct point sets
of cardinality greater than `D` satisfy it. -/
@[expose]
def EvaluationSeparatesUpTo {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {k : Nat} (pts : Vector F k) (D : Nat) : Prop :=
  ∀ p q : DensePoly F,
    p.degree?.getD 0 ≤ D → q.degree?.getD 0 ≤ D →
      (∀ x ∈ pts.toList, DensePoly.evalImpl p x = DensePoly.evalImpl q x) →
        p = q

/-- Check `U * A = C` at the supplied scalar points. Its soundness theorem
requires the usual distinctness and degree-bound hypotheses. -/
@[expose]
def mulEqCertAt {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m k : Nat} (pts : Vector F k) (U : Matrix (DensePoly F) n n)
    (A C : Matrix (DensePoly F) n m) : Bool :=
  pts.toList.all fun x =>
    Matrix.mulImpl (evalMatrix U x) (evalMatrix A x) == evalMatrix C x

/-- An accepted evaluation certificate proves the product identity whenever
the checked point set separates all entries in the advertised degree range. -/
theorem mulEqCertAt_sound {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m k D : Nat} {pts : Vector F k}
    {U : Matrix (DensePoly F) n n} {A C : Matrix (DensePoly F) n m}
    (hsep : EvaluationSeparatesUpTo pts D)
    (hprodDegree : ∀ i : Fin n, ∀ j : Fin m,
      (U * A)[(i, j)].degree?.getD 0 ≤ D)
    (hresultDegree : ∀ i : Fin n, ∀ j : Fin m,
      C[(i, j)].degree?.getD 0 ≤ D)
    (h : mulEqCertAt pts U A C = true) :
    U * A = C := by
  apply Matrix.ext_getElem
  intro i j
  apply hsep
  · simpa only [Matrix.getElem_pair_eq_nested] using hprodDegree i j
  · simpa only [Matrix.getElem_pair_eq_nested] using hresultDegree i j
  · intro x hx
    simp only [mulEqCertAt, List.all_eq_true] at h
    have hmatrix :
        Matrix.mulImpl (evalMatrix U x) (evalMatrix A x) = evalMatrix C x :=
      eq_of_beq (h x hx)
    have heval := congrArg (fun M : Matrix F n m => M[(i, j)]) hmatrix
    rw [← evalMatrix_mul U A x] at heval
    unfold evalMatrix at heval
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested] at heval
    simpa only [Matrix.getElem_ofFn, Matrix.getElem_pair_eq_nested] using heval

end Hex.PolyMatrix
