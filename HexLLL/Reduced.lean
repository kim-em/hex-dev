/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Lattice

public section

/-!
The `(δ, η)`-reducedness predicate `isLLLReduced` and the short-vector
bound `short_vector_bound_of_size_bound`: a reduced independent basis has
a first row no longer than `(1 / (δ - η²)) ^ (n - 1)` (squared) times any
nonzero lattice vector.
-/

namespace Hex

namespace Internal.LLLCore

/-- Recover the squared norm of a Gram-Schmidt basis vector. -/
@[expose]
def basisNormSq (basis : Matrix Rat n m) (i : Fin n) : Rat :=
  (basis.row i).normSq



end Internal.LLLCore

open Hex.Internal

/-- A basis is `(δ, η)`-LLL-reduced when it is size-reduced with bound `η`
(`|μ| ≤ η` for every below-diagonal entry of the Gram-Schmidt coefficient
matrix) and satisfies the Lovasz condition at every adjacent pair. The
size-reduction clause is stored in squared form `μ² ≤ η²`, which is equivalent
to `|μ| ≤ η` exactly when `η ≥ 0`; every consumer supplies `1/2 ≤ η`. -/
@[expose]
def isLLLReduced (b : Matrix Int n m) (δ η : Rat) : Prop :=
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  (∀ i j, (hi : i < n) → (hji : j < i) →
      let iFin : Fin n := ⟨i, hi⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hji hi⟩
      let μ := coeffs[iFin][jFin]
      μ * μ ≤ η * η) ∧
    ∀ i, (hi : i + 1 < n) →
      let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
      let ip1Fin : Fin n := ⟨i + 1, hi⟩
      let μ := coeffs[ip1Fin][iFin]
      δ * LLLCore.basisNormSq basis iFin ≤
        LLLCore.basisNormSq basis ip1Fin + μ * μ * LLLCore.basisNormSq basis iFin

namespace Internal.LLLCore

/-- `ratMulSelfNonneg` states that a rational square `x * x` is nonnegative, the
per-entry fact underlying every sum-of-squares norm bound in this file. -/
private theorem ratMulSelfNonneg (x : Rat) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using (Lean.Grind.OrderedRing.sq_nonneg (a := x))

/-- `foldlNonneg` states that a left fold accumulating nonnegative summands
`f x` onto a nonnegative accumulator stays nonnegative, the inductive step
behind `basisNormSq_nonneg`. -/
private theorem foldlNonneg {α : Type} (xs : List α) (f : α → Rat)
    (acc : Rat) (hacc : 0 ≤ acc) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ xs.foldl (fun sum x => sum + f x) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (acc + f x) (Rat.add_nonneg hacc (hf x))

/-- The squared norm of any basis row is nonnegative, being a sum of squares of
its rational entries. -/
theorem basisNormSq_nonneg (basis : Matrix Rat n m) (i : Fin n) :
    0 ≤ basisNormSq basis i := by
  simp only [basisNormSq, Vector.normSq, Vector.dotProduct]
  exact foldlNonneg (List.finRange m) (fun j => (basis.row i)[j] * (basis.row i)[j]) 0
    (by grind) (fun j => ratMulSelfNonneg ((basis.row i)[j]))

/-- `stepBound_arith` rearranges the Lovasz condition `δ * N ≤ Np + μ² * N`
together with the size-reduced bound `μ² ≤ η²` into the adjacent norm bound
`(δ - η²) * N ≤ Np`. -/
private theorem stepBound_arith (δ η μ N Np : Rat)
    (hN : 0 ≤ N) (hsize : μ * μ ≤ η * η)
    (hlov : δ * N ≤ Np + μ * μ * N) :
    (δ - η * η) * N ≤ Np := by
  have hcoef : δ - η * η ≤ δ - μ * μ := by grind
  have hleft : (δ - η * η) * N ≤ (δ - μ * μ) * N :=
    Rat.mul_le_mul_of_nonneg_right hcoef hN
  have hlov' : (δ - μ * μ) * N ≤ Np := by
    have hsub : δ * N - μ * μ * N ≤ (Np + μ * μ * N) - μ * μ * N := by
      grind
    calc
      (δ - μ * μ) * N = δ * N - μ * μ * N := by grind
      _ ≤ (Np + μ * μ * N) - μ * μ * N := hsub
      _ = Np := by grind
  exact Rat.le_trans hleft hlov'

/-- `divStep_arith` divides the step bound `d * N ≤ Np` (with `0 < d`) through
by `d` to yield the reciprocal form `N ≤ (1 / d) * Np`. -/
private theorem divStep_arith (d N Np : Rat) (hd : 0 < d)
    (h : d * N ≤ Np) :
    N ≤ (1 / d) * Np := by
  have hdne : d ≠ 0 := by grind
  have hinv_pos : 0 < (1 / d : Rat) := by
    rw [Rat.div_def]
    simpa using (Rat.inv_pos.mpr hd)
  have hinv_nonneg : 0 ≤ (1 / d : Rat) := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_left h hinv_nonneg
  have hleft : (1 / d : Rat) * (d * N) = N := by
    rw [Rat.div_def, show (1 : Rat) * d⁻¹ = d⁻¹ by grind,
      ← Rat.mul_assoc, Rat.inv_mul_cancel d hdne]
    grind
  simpa [hleft] using hmul

/-- `ratPow_nonneg` states that a nonnegative rational `a` raised to a natural
power `k` stays nonnegative, used when bounding the geometric `α ^ i` factors of
the step bounds. -/
private theorem ratPow_nonneg (a : Rat) (ha : 0 ≤ a) (k : Nat) :
    0 ≤ a ^ k := by
  induction k with
  | zero =>
      rw [Lean.Grind.Semiring.pow_zero]
      grind
  | succ k ih =>
      rw [Lean.Grind.Semiring.pow_succ]
      exact Rat.mul_nonneg ih ha

/-- Adjacent Gram-Schmidt norm bound from size reduction and Lovasz. -/
theorem stepBound (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (_hδη : η * η < δ)
    (i : Nat) (hi : i + 1 < n) :
    (δ - η * η) *
        basisNormSq (GramSchmidt.Int.basis b)
          ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ ≤
      basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ := by
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
  let ip1Fin : Fin n := ⟨i + 1, hi⟩
  let μ := coeffs[ip1Fin][iFin]
  rcases hred with ⟨hsize, hlov⟩
  have hsize' : μ * μ ≤ η * η := by
    simpa [basis, coeffs, iFin, ip1Fin, μ] using
      hsize (i + 1) i hi (Nat.lt_succ_self i)
  have hlov' :
      δ * basisNormSq basis iFin ≤
        basisNormSq basis ip1Fin + μ * μ * basisNormSq basis iFin := by
    simpa [basis, coeffs, iFin, ip1Fin, μ] using hlov i hi
  exact stepBound_arith δ η μ (basisNormSq basis iFin) (basisNormSq basis ip1Fin)
    (basisNormSq_nonneg basis iFin) hsize' hlov'

/-- Adjacent Gram-Schmidt norm bound in reciprocal form. -/
theorem stepAlpha (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hδη : η * η < δ)
    (i : Nat) (hi : i + 1 < n) :
    basisNormSq (GramSchmidt.Int.basis b)
        ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ ≤
      (1 / (δ - η * η)) *
        basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ := by
  have hpos : 0 < δ - η * η := by grind
  exact divStep_arith (δ - η * η)
    (basisNormSq (GramSchmidt.Int.basis b)
      ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
    (basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩)
    hpos (stepBound b hred hδη i hi)

/-- Telescoped Gram-Schmidt norm bound from the first vector to index `i`. -/
theorem teleBound (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hδη : η * η < δ)
    (i : Nat) (hi : i < n) :
    basisNormSq (GramSchmidt.Int.basis b)
        ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le i) hi⟩ ≤
      (1 / (δ - η * η)) ^ i *
        basisNormSq (GramSchmidt.Int.basis b) ⟨i, hi⟩ := by
  let α : Rat := 1 / (δ - η * η)
  induction i with
  | zero =>
      rw [Lean.Grind.Semiring.pow_zero]
      have hfin :
          (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le 0) hi⟩ : Fin n) = ⟨0, hi⟩ :=
        Fin.ext rfl
      rw [hfin]
      grind
  | succ i ih =>
      have hiPrev : i < n := Nat.lt_trans (Nat.lt_succ_self i) hi
      have hih := ih hiPrev
      have hzero :
          (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le i) hiPrev⟩ : Fin n) =
            ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le (i + 1)) hi⟩ :=
        Fin.ext rfl
      rw [hzero] at hih
      have hstep := stepAlpha b hred hδη i hi
      have hifin :
          (⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ : Fin n) = ⟨i, hiPrev⟩ :=
        Fin.ext rfl
      rw [hifin] at hstep
      have hα_nonneg : 0 ≤ α := by
        have hpos : 0 < δ - η * η := by grind
        have hα_pos : 0 < α := by
          dsimp [α]
          rw [Rat.div_def]
          simpa using (Rat.inv_pos.mpr hpos)
        grind
      have hpow_nonneg : 0 ≤ α ^ i := ratPow_nonneg α hα_nonneg i
      have hmul := Rat.mul_le_mul_of_nonneg_left hstep hpow_nonneg
      have hchain := Rat.le_trans hih hmul
      calc
        basisNormSq (GramSchmidt.Int.basis b)
            ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le (i + 1)) hi⟩
            ≤ α ^ i *
                (α * basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩) := hchain
        _ = α ^ (i + 1) *
              basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ := by
            rw [Lean.Grind.Semiring.pow_succ]
            grind

/-- Telescoped Gram--Schmidt norm bound from an arbitrary row `j` through
`d` adjacent reduced-basis steps. -/
theorem teleBoundAdd (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hδη : η * η < δ)
    (j d : Nat) (hi : j + d < n) :
    basisNormSq (GramSchmidt.Int.basis b)
        ⟨j, Nat.lt_of_le_of_lt (Nat.le_add_right j d) hi⟩ ≤
      (1 / (δ - η * η)) ^ d *
        basisNormSq (GramSchmidt.Int.basis b) ⟨j + d, hi⟩ := by
  let α : Rat := 1 / (δ - η * η)
  have hα_nonneg : 0 ≤ α := by
    have hpos : 0 < δ - η * η := by grind
    have hα_pos : 0 < α := by
      dsimp [α]
      rw [Rat.div_def]
      simpa using (Rat.inv_pos.mpr hpos)
    grind
  induction d with
  | zero =>
      simp only [Nat.add_zero, Lean.Grind.Semiring.pow_zero]
      grind
  | succ d ih =>
      have hiprev : j + d < n := by omega
      have hchain := ih hiprev
      have hstep := stepAlpha b hred hδη (j + d) (by omega : j + d + 1 < n)
      have hmul := Rat.mul_le_mul_of_nonneg_left hstep
        (ratPow_nonneg α hα_nonneg d)
      calc
        basisNormSq (GramSchmidt.Int.basis b)
            ⟨j, Nat.lt_of_le_of_lt (Nat.le_add_right j (d + 1)) hi⟩
            ≤ α ^ d * basisNormSq (GramSchmidt.Int.basis b)
                ⟨j + d, hiprev⟩ := by simpa [α] using hchain
        _ ≤ α ^ d * (α * basisNormSq (GramSchmidt.Int.basis b)
                ⟨j + d + 1, by omega⟩) := by
              simpa [α] using hmul
        _ = α ^ (d + 1) * basisNormSq (GramSchmidt.Int.basis b)
                ⟨j + (d + 1), hi⟩ := by
              have hfin :
                  (⟨j + d + 1, by omega⟩ : Fin n) = ⟨j + (d + 1), hi⟩ :=
                Fin.ext rfl
              rw [hfin]
              rw [Lean.Grind.Semiring.pow_succ]
              grind

/-- First Gram-Schmidt basis vector identity: the 0-th Gram-Schmidt vector
coincides with the 0-th input row, so their squared norms agree. -/
theorem basisNormSq_zero (b : Matrix Int n m) (hn : 0 < n) :
    basisNormSq (GramSchmidt.Int.basis b) ⟨0, hn⟩ =
      (((b.row ⟨0, hn⟩).normSq : Int) : Rat) := by
  unfold basisNormSq
  rw [GramSchmidt.Int.basis_zero b hn]
  exact GramSchmidt.Int.normSq_map_intCast (b.row ⟨0, hn⟩)

/-- `ratPow_le_pow_of_one_le` states that for `1 ≤ α` the power `α ^ i` is
monotone in the exponent, so a larger index gives a larger geometric step
factor. -/
private theorem ratPow_le_pow_of_one_le {α : Rat} (hα : 1 ≤ α) :
    ∀ {i j : Nat}, i ≤ j → α ^ i ≤ α ^ j := by
  intro i j hij
  induction j with
  | zero =>
      have hi : i = 0 := Nat.le_zero.mp hij
      subst hi
      exact Rat.le_refl
  | succ k ih =>
      by_cases hi : i ≤ k
      · have hih := ih hi
        have hα_nn : (0 : Rat) ≤ α := by grind
        have hpow_k : 0 ≤ α ^ k := ratPow_nonneg α hα_nn k
        have hstep : α ^ k ≤ α ^ (k + 1) := by
          rw [Lean.Grind.Semiring.pow_succ]
          have h1 : α ^ k * 1 ≤ α ^ k * α :=
            Rat.mul_le_mul_of_nonneg_left hα hpow_k
          simpa using h1
        exact Rat.le_trans hih hstep
      · have hi' : i = k + 1 :=
          Nat.le_antisymm hij (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi))
        subst hi'
        exact Rat.le_refl

/-- A fold of terms individually bounded by `C` is bounded by the list length
times `C`, with an arbitrary running accumulator. -/
private theorem foldl_le_acc_add_length_mul {α : Type} (l : List α)
    (f : α → Rat) (C acc : Rat) (hf : ∀ x ∈ l, f x ≤ C) :
    l.foldl (fun acc x => acc + f x) acc ≤ acc + (l.length : Rat) * C := by
  induction l generalizing acc with
  | nil => simp; grind
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      have htail := ih (acc := acc + f x) (fun y hy => hf y (by simp [hy]))
      have hx := hf x (by simp)
      calc
        xs.foldl (fun acc x => acc + f x) (acc + f x)
            ≤ acc + f x + (xs.length : Rat) * C := htail
        _ ≤ acc + C + (xs.length : Rat) * C := by grind
        _ = acc + ((xs.length + 1 : Nat) : Rat) * C := by
          push_cast
          grind

/-- Every row up to index `i` in an LLL-reduced integer basis is controlled by
the `i`-th Gram--Schmidt norm.  The extra factor `n` accounts for the at most
`n` Gram--Schmidt components of the row; the geometric factor is the usual
telescoped Lovasz bound. -/
theorem rowNormSq_le_basisNormSq (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hηsq : η * η ≤ 1)
    (hδη : η * η < δ) (hδ' : δ ≤ 1)
    (j i : Fin n) (hji : j.val ≤ i.val) :
    (((b.row j).normSq : Int) : Rat) ≤
      (n : Rat) * (1 / (δ - η * η)) ^ (n - 1) *
        basisNormSq (GramSchmidt.Int.basis b) i := by
  let α : Rat := 1 / (δ - η * η)
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  have hpos : 0 < δ - η * η := by grind
  have hαpos : 0 < α := by
    dsimp [α]
    rw [Rat.div_def]
    simpa using (Rat.inv_pos.mpr hpos)
  have hαnn : 0 ≤ α := by grind
  have hden_le_one : δ - η * η ≤ 1 := by
    have hsqnn : 0 ≤ η * η := ratMulSelfNonneg η
    grind
  have hden_ne : δ - η * η ≠ 0 := by grind
  have hα_one : 1 ≤ α := by
    have hunit : α * (δ - η * η) = 1 := by
      dsimp [α]
      rw [Rat.div_def, show (1 : Rat) * (δ - η * η)⁻¹ =
        (δ - η * η)⁻¹ by grind, Rat.inv_mul_cancel _ hden_ne]
    have hmul := Rat.mul_le_mul_of_nonneg_left hden_le_one hαnn
    rw [hunit] at hmul
    simpa using hmul
  have horth : ∀ k l : Fin n, k ≠ l →
      (basis.row k).dotProduct (basis.row l) = 0 := by
    intro k l hkl
    exact GramSchmidt.Int.basis_orthogonal b k.val l.val k.isLt l.isLt
      (fun h => hkl (Fin.ext h))
  have hreconstruct := GramSchmidt.Int.row_reconstruction b j
  have hnorm := congrArg Vector.normSq hreconstruct
  rw [GramSchmidt.Int.normSq_map_intCast,
    GramSchmidt.normSq_vecMul_of_orthogonal basis (coeffs.row j) horth,
    Fin.foldl_eq_finRange_foldl] at hnorm
  rw [hnorm]
  have hfold := foldl_le_acc_add_length_mul (List.finRange n)
    (fun k : Fin n =>
      (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq)
    (α ^ (n - 1) * basisNormSq basis i) 0 (by
      intro k _hk
      by_cases hkj : k.val ≤ j.val
      · have hki : k.val ≤ i.val := Nat.le_trans hkj hji
        have hcoeff : (coeffs.row j)[k] * (coeffs.row j)[k] ≤ 1 := by
          rcases Nat.lt_or_eq_of_le hkj with hlt | heq
          · have hsize := hred.1 j.val k.val j.isLt hlt
            exact Rat.le_trans hsize hηsq
          · have hfin : k = j := Fin.ext heq
            rw [hfin]
            have hdiag : (coeffs.row j)[j] = 1 := by
              simpa [coeffs, GramSchmidt.entry] using
                GramSchmidt.Int.coeffs_diag b j.val j.isLt
            rw [hdiag]
            grind
        have hbasisnn : 0 ≤ basisNormSq basis k := basisNormSq_nonneg basis k
        have hfirst :
            (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq ≤
              basisNormSq basis k := by
          have hmul := Rat.mul_le_mul_of_nonneg_right hcoeff hbasisnn
          simpa [basisNormSq, basis] using hmul
        have htele := teleBoundAdd b hred hδη k.val (i.val - k.val) (by omega)
        have hadd : k.val + (i.val - k.val) = i.val := Nat.add_sub_of_le hki
        have hkfin :
            (⟨k.val, Nat.lt_of_le_of_lt (Nat.le_add_right k.val (i.val - k.val))
              (by omega)⟩ : Fin n) = k := Fin.ext rfl
        have hifin : (⟨k.val + (i.val - k.val), by omega⟩ : Fin n) = i :=
          Fin.ext hadd
        rw [hkfin, hifin] at htele
        have hpow : α ^ (i.val - k.val) ≤ α ^ (n - 1) :=
          ratPow_le_pow_of_one_le hα_one (by omega)
        have hibasisnn : 0 ≤ basisNormSq basis i := basisNormSq_nonneg basis i
        have hpowmul := Rat.mul_le_mul_of_nonneg_right hpow hibasisnn
        exact Rat.le_trans hfirst (Rat.le_trans (by simpa [α, basis] using htele)
          (by simpa [α, basis] using hpowmul))
      · have hjk : j.val < k.val := Nat.lt_of_not_ge hkj
        have hzero : (coeffs.row j)[k] = 0 := by
          simpa [coeffs, GramSchmidt.entry] using
            GramSchmidt.Int.coeffs_upper b j.val k.val j.isLt k.isLt hjk
        rw [hzero]
        have hnonneg : 0 ≤ α ^ (n - 1) * basisNormSq basis i :=
          Rat.mul_nonneg (ratPow_nonneg α hαnn (n - 1))
            (basisNormSq_nonneg basis i)
        grind)
  have hfold' :
      (List.finRange n).foldl
        (fun acc k => acc +
          (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq) 0
        ≤ (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := by
    calc
      _ ≤ 0 + (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := by
        simpa using hfold
      _ = (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := by grind
  calc
    (List.finRange n).foldl
        (fun acc k => acc +
          (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq) 0
        ≤ (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := hfold'
    _ = (n : Rat) * (1 / (δ - η * η)) ^ (n - 1) *
          basisNormSq (GramSchmidt.Int.basis b) i := by
          dsimp [α, basis]
          grind

end Internal.LLLCore

/-- LLL short-vector inequality, parameterized by the size-reduction bound
`η`. For a `(δ, η)`-LLL-reduced basis with `1/2 ≤ η`, `η² < δ ≤ 1`, the
squared norm of the first row is at most `(1 / (δ - η²)) ^ (n - 1)` times the
squared norm of any nonzero lattice vector. The proof combines the telescoping
Gram-Schmidt inequality with the lower bound on the smallest Gram-Schmidt
vector contained in the lattice. -/
theorem short_vector_bound_of_size_bound (b : Matrix Int n m) {δ η : Rat}
    (hli : Matrix.independent b) (hred : isLLLReduced b δ η)
    (hη : (1 / 2 : Rat) ≤ η) (hδη : η * η < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    {v : Vector Int m} (hv : Matrix.memLattice b v) (hv' : v ≠ 0) :
    (((b.row ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).normSq : Int) : Rat) ≤
      (1 / (δ - η * η)) ^ (n - 1) *
        ((v.normSq : Int) : Rat) := by
  have h0n : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  obtain ⟨i, hi_norm⟩ :=
    GramSchmidt.Int.normSq_latticeVec_ge_min_basis_normSq b hli v hv hv'
  have htele := LLLCore.teleBound b hred hδη i.val i.isLt
  have e1 : (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩ : Fin n) = ⟨0, h0n⟩ :=
    Fin.ext rfl
  have e2 : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
  rw [e1, e2, LLLCore.basisNormSq_zero b h0n] at htele
  have hα_pos : 0 < δ - η * η := by grind
  have hα_inv_pos : 0 < (1 / (δ - η * η) : Rat) := by
    rw [Rat.div_def]
    simpa using (Rat.inv_pos.mpr hα_pos)
  have hα_nn : (0 : Rat) ≤ 1 / (δ - η * η) := by grind
  -- `η ≥ 1/2` implies `η² ≥ 1/4`, so `δ - η² ≤ δ - 1/4 ≤ 3/4 ≤ 1` and
  -- `1 / (δ - η²) ≥ 1`.
  have hηη_lb : (1 / 4 : Rat) ≤ η * η := by
    have h2 : (0 : Rat) ≤ 1 / 2 := by grind
    have hηnn : (0 : Rat) ≤ η := Rat.le_trans h2 hη
    have hsq1 : (1 / 2 : Rat) * (1 / 2) ≤ (1 / 2 : Rat) * η :=
      Rat.mul_le_mul_of_nonneg_left hη h2
    have hsq2 : (1 / 2 : Rat) * η ≤ η * η :=
      Rat.mul_le_mul_of_nonneg_right hη hηnn
    have hsq : (1 / 2 : Rat) * (1 / 2) ≤ η * η := Rat.le_trans hsq1 hsq2
    grind
  have hα_one : (1 : Rat) ≤ 1 / (δ - η * η) := by
    have h_le : δ - η * η ≤ 1 := by grind
    have hne : δ - η * η ≠ 0 := by grind
    have hα_eq : (1 / (δ - η * η)) * (δ - η * η) = 1 := by
      rw [Rat.div_def, show (1 : Rat) * (δ - η * η)⁻¹ = (δ - η * η)⁻¹ from by grind]
      exact Rat.inv_mul_cancel _ hne
    have hstep : (1 / (δ - η * η)) * (δ - η * η) ≤ (1 / (δ - η * η)) * 1 :=
      Rat.mul_le_mul_of_nonneg_left h_le hα_nn
    rw [hα_eq] at hstep
    simpa using hstep
  have hi_le : i.val ≤ n - 1 := by omega
  have hpow_mono : (1 / (δ - η * η)) ^ i.val ≤ (1 / (δ - η * η)) ^ (n - 1) :=
    LLLCore.ratPow_le_pow_of_one_le hα_one hi_le
  have hbasis_nn : 0 ≤ LLLCore.basisNormSq (GramSchmidt.Int.basis b) i :=
    LLLCore.basisNormSq_nonneg _ i
  have hαpow_nn : 0 ≤ (1 / (δ - η * η)) ^ (n - 1) :=
    LLLCore.ratPow_nonneg _ hα_nn (n - 1)
  calc
    (((b.row ⟨0, h0n⟩).normSq : Int) : Rat)
        ≤ (1 / (δ - η * η)) ^ i.val *
            LLLCore.basisNormSq (GramSchmidt.Int.basis b) i := htele
    _ ≤ (1 / (δ - η * η)) ^ (n - 1) *
            LLLCore.basisNormSq (GramSchmidt.Int.basis b) i :=
        Rat.mul_le_mul_of_nonneg_right hpow_mono hbasis_nn
    _ ≤ (1 / (δ - η * η)) ^ (n - 1) * ((v.normSq : Int) : Rat) :=
        Rat.mul_le_mul_of_nonneg_left hi_norm hαpow_nn

namespace Internal

/-- Monotonicity of the size-reduction bound: a `(δ, η₁)`-LLL-reduced basis
is also `(δ, η₂)`-LLL-reduced for any `η₂ ≥ η₁ ≥ 0`. The Lovász side is
unchanged; the size-reduced side relaxes since `|μ| ≤ η₁ ≤ η₂` (in squared
form, `μ² ≤ η₁² ≤ η₂²`). -/
theorem isLLLReduced.mono_η (b : Matrix Int n m) {δ η₁ η₂ : Rat}
    (hη₁ : 0 ≤ η₁) (hle : η₁ ≤ η₂) (hred : isLLLReduced b δ η₁) :
    isLLLReduced b δ η₂ := by
  rcases hred with ⟨hsize, hlov⟩
  refine ⟨?_, hlov⟩
  intro i j hi hji
  have hη₂ : 0 ≤ η₂ := Rat.le_trans hη₁ hle
  have hsq1 : η₁ * η₁ ≤ η₁ * η₂ := Rat.mul_le_mul_of_nonneg_left hle hη₁
  have hsq2 : η₁ * η₂ ≤ η₂ * η₂ := Rat.mul_le_mul_of_nonneg_right hle hη₂
  exact Rat.le_trans (hsize i j hi hji) (Rat.le_trans hsq1 hsq2)

end Internal

end Hex
