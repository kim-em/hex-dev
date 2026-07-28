/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.BlockDeterminant
import all HexResultant.BlockDeterminant
import all HexPoly.Euclid.MulRing

public section

/-!
The Brown--Traub generalized Sylvester transformation.

After exchanging the input blocks, equation (18) replaces each `F` column by
the corresponding `H = F + B * G` column.  For target offset `d`, coefficient
`B[k]` multiplies source column `deg B + d - k`.  Indexing the elementary
column additions by `k` exposes the usual coefficient convolution directly.
-/

namespace Hex

universe u

namespace SubresultantMinor

/-- The value of one destination column after adding the first `count`
multiplier terms. -/
@[expose]
def productCol {R : Type u} [Zero R] [DecidableEq R] [Add R] [Mul R] {n : Nat}
    (M : Square R n) (dst : Fin n) (db offset : Nat)
    (hsrc : db + offset < dst.val) (b : DensePoly R) (i : Fin n) :
    (count : Nat) → count ≤ db + 1 → R
  | 0, _ => M i dst
  | count + 1, h =>
      productCol M dst db offset hsrc b i count (by omega) +
        b.coeff count * M i ⟨db + offset - count, by
          have := dst.isLt
          omega⟩

/-- Add the first `count` multiplier terms to one destination column. -/
@[expose]
def addProduct {R : Type u} [Zero R] [DecidableEq R] [Add R] [Mul R] {n : Nat}
    (M : Square R n) (dst : Fin n) (db offset : Nat)
    (hsrc : db + offset < dst.val) (b : DensePoly R) :
    (count : Nat) → count ≤ db + 1 → Square R n
  | 0, _ => M
  | count + 1, h =>
      let src : Fin n := ⟨db + offset - count, by
        have := dst.isLt
        omega⟩
      addCol (addProduct M dst db offset hsrc b count (by omega)) src dst
        (b.coeff count)

/-- Entrywise action of the multiplier-coefficient additions for one
destination. -/
theorem addProduct_apply {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    {n : Nat}
    (M : Square R n) (dst : Fin n) (db offset : Nat)
    (hsrc : db + offset < dst.val) (b : DensePoly R)
    (count : Nat) (h : count ≤ db + 1) (i j : Fin n) :
    addProduct M dst db offset hsrc b count h i j =
      if j = dst then productCol M dst db offset hsrc b i count h else M i j := by
  induction count generalizing j with
  | zero =>
      by_cases hj : j = dst
      · subst j
        simp [addProduct, productCol]
      · simp [addProduct, hj]
  | succ count ih =>
      let src : Fin n := ⟨db + offset - count, by
        have := dst.isLt
        omega⟩
      have hsrcDst : src ≠ dst := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [src] at hval
        omega
      by_cases hj : j = dst
      · subst j
        simp only [addProduct, addCol_apply, if_true, productCol]
        rw [ih, if_pos rfl, ih, if_neg hsrcDst]
      · simp only [addProduct, addCol_apply, if_neg hj]
        rw [ih, if_neg hj]

/-- One multiplier-column update preserves the local determinant. -/
theorem det_addProduct {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    {n : Nat}
    (M : Square R n) (dst : Fin n) (db offset : Nat)
    (hsrc : db + offset < dst.val) (b : DensePoly R)
    (count : Nat) (h : count ≤ db + 1) :
    det (addProduct M dst db offset hsrc b count h) = det M := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [addProduct, det_addCol, ih]
      intro heq
      have hval := congrArg Fin.val heq
      simp at hval
      omega

/-- A multiplier-column value depends only on its destination and selected
source entries. -/
private theorem productCol_congr {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    {n : Nat}
    (M N : Square R n) (dst : Fin n) (db offset : Nat)
    (hsrc : db + offset < dst.val) (b : DensePoly R) (i : Fin n)
    (count : Nat) (h : count ≤ db + 1)
    (hdst : M i dst = N i dst)
    (hsources : ∀ k, k < count →
      M i ⟨db + offset - k, by
        have := dst.isLt
        omega⟩ =
      N i ⟨db + offset - k, by
        have := dst.isLt
        omega⟩) :
    productCol M dst db offset hsrc b i count h =
      productCol N dst db offset hsrc b i count h := by
  induction count with
  | zero => exact hdst
  | succ count ih =>
      simp only [productCol]
      rw [ih (by omega) (fun k hk => hsources k (by omega)),
        hsources count (by omega)]

/-- Apply the Brown multiplier update to `right` consecutive columns starting
at `split`. Sources stay strictly to the left of `split`, so no destination is
ever read as a source. -/
@[expose]
def productCols {R : Type u} [Zero R] [DecidableEq R] [Add R] [Mul R] {n : Nat}
    (M : Square R n) (split db : Nat) (b : DensePoly R) :
    (right : Nat) → db + right ≤ split → split + right ≤ n → Square R n
  | 0, _, _ => M
  | right + 1, hs, ht =>
      let dst : Fin n := ⟨split + right, by omega⟩
      productCols
        (addProduct M dst db right (by
          simp [dst]
          omega) b (db + 1) (Nat.le_refl _))
        split db b right (by omega) (by omega)

/-- Entrywise action of the complete Brown multiplier-column update. -/
theorem productCols_apply {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    {n : Nat}
    (M : Square R n) (split db : Nat) (b : DensePoly R)
    (right : Nat) (hs : db + right ≤ split) (ht : split + right ≤ n)
    (i j : Fin n) :
    productCols M split db b right hs ht i j =
      if hj : split ≤ j.val ∧ j.val < split + right then
        productCol M j db (j.val - split) (by omega) b i (db + 1)
          (Nat.le_refl _)
      else M i j := by
  induction right generalizing M with
  | zero =>
      have hj : ¬(split ≤ j.val ∧ j.val < split) := by omega
      simp [productCols, hj]
  | succ right ih =>
      let dst : Fin n := ⟨split + right, by omega⟩
      let M' := addProduct M dst db right (by
        simp [dst]
        omega) b (db + 1) (Nat.le_refl _)
      rw [productCols, ih]
      by_cases hold : split ≤ j.val ∧ j.val < split + right
      · have hnew : split ≤ j.val ∧ j.val < split + (right + 1) := by
          omega
        rw [dif_pos hold, dif_pos hnew]
        apply productCol_congr M' M j db (j.val - split) (by omega) b i
          (db + 1) (Nat.le_refl _)
        · dsimp only [M']
          rw [addProduct_apply]
          rw [if_neg (by
            intro heq
            have hval := congrArg Fin.val heq
            simp [dst] at hval
            omega)]
        · intro k hk
          dsimp only [M']
          rw [addProduct_apply]
          rw [if_neg (by
            intro heq
            have hval := congrArg Fin.val heq
            simp [dst] at hval
            omega)]
      · by_cases hlast : j.val = split + right
        · have hnew : split ≤ j.val ∧ j.val < split + (right + 1) := by
            omega
          rw [dif_neg hold, dif_pos hnew]
          have hjdst : j = dst := Fin.ext hlast
          subst j
          rw [addProduct_apply, if_pos rfl]
          congr 3
          simp [dst]
        · have hnew : ¬(split ≤ j.val ∧ j.val < split + (right + 1)) := by
            omega
          rw [dif_neg hold, dif_neg hnew]
          rw [addProduct_apply]
          rw [if_neg (by
            intro heq
            have hval := congrArg Fin.val heq
            simp at hval
            omega)]

/-- The complete Brown multiplier-column update preserves the determinant. -/
theorem det_productCols {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    {n : Nat}
    (M : Square R n) (split db : Nat) (b : DensePoly R)
    (right : Nat) (hs : db + right ≤ split) (ht : split + right ≤ n) :
    det (productCols M split db b right hs ht) = det M := by
  induction right generalizing M with
  | zero => rfl
  | succ right ih =>
      rw [productCols, ih, det_addProduct]

end SubresultantMinor

namespace DensePoly
namespace Subresultant

/-- The first `count` terms of the coefficient convolution of `b` and `g` at
an integer index. Negative indices of `g` contribute zero. -/
@[expose]
def coeffFold {R : Type u} [Zero R] [DecidableEq R] [Add R] [Mul R]
    (b g : DensePoly R) (t : Int) (count : Nat) : R :=
  (List.range count).foldl
    (fun acc k => acc + b.coeff k * coeffInt g (t - (k : Int))) 0

/-- Extending the convolution fold appends the next coefficient product. -/
theorem coeffFold_succ {R : Type u} [Zero R] [DecidableEq R] [Add R] [Mul R]
    (b g : DensePoly R) (t : Int) (count : Nat) :
    coeffFold b g t (count + 1) =
      coeffFold b g t count +
        b.coeff count * coeffInt g (t - (count : Int)) := by
  simp [coeffFold, List.range_succ, List.foldl_append]

/-- Extending the convolution past the stored size of the left factor only
adds zero coefficients. -/
theorem coeffFold_of_size_le {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (b g : DensePoly R) (t : Int) (count : Nat) (h : b.size ≤ count) :
    coeffFold b g t count = coeffFold b g t b.size := by
  induction count with
  | zero =>
      have hb : b.size = 0 := by omega
      rw [hb]
  | succ count ih =>
      by_cases hle : b.size ≤ count
      · rw [coeffFold_succ, ih hle,
          coeff_eq_zero_of_size_le b hle,
          show (Zero.zero : R) = 0 from rfl,
          Lean.Grind.Semiring.zero_mul,
          Lean.Grind.Semiring.add_zero]
      · have hb : b.size = count + 1 := by omega
        rw [hb]

/-- The Brown destination-column recursion is the original entry plus its
coefficient convolution. -/
private theorem productCol_eq_add_coeffFold {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}
    (M : SubresultantMinor.Square R n) (dst : Fin n) (db offset : Nat)
    (hsrc : db + offset < dst.val) (b f g : DensePoly R) (i : Fin n)
    (t : Int) (count : Nat) (h : count ≤ db + 1)
    (hdst : M i dst = coeffInt f t)
    (hsources : ∀ k, k < count →
      M i ⟨db + offset - k, by
        have := dst.isLt
        omega⟩ = coeffInt g (t - (k : Int))) :
    SubresultantMinor.productCol M dst db offset hsrc b i count h =
      coeffInt f t + coeffFold b g t count := by
  induction count with
  | zero =>
      simp [SubresultantMinor.productCol, coeffFold, hdst]
      grind
  | succ count ih =>
      rw [SubresultantMinor.productCol,
        ih (by omega) (fun k hk => hsources k (by omega)),
        hsources count (by omega), coeffFold_succ]
      grind

/-- Reading at `t - k`, for nonnegative `t`, is the usual truncated natural
coefficient lookup. -/
private theorem coeffInt_sub_nat {R : Type u} [Zero R] [DecidableEq R]
    (p : DensePoly R) (t : Int) (ht : 0 ≤ t) (k : Nat) :
    coeffInt p (t - (k : Int)) =
      if k ≤ t.toNat then p.coeff (t.toNat - k) else 0 := by
  have htCast : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  by_cases hk : k ≤ t.toNat
  · rw [if_pos hk]
    have hkInt : (k : Int) ≤ t := by
      rw [← htCast]
      exact Int.ofNat_le.mpr hk
    unfold coeffInt
    rw [if_neg (by
      have hk0 := Int.natCast_nonneg k
      omega)]
    congr 1
    apply Int.natCast_inj.mp
    rw [Int.toNat_sub_of_le hkInt, Int.ofNat_sub hk, htCast]
  · rw [if_neg hk]
    have hkInt : t < (k : Int) := by
      rw [← htCast]
      exact Int.ofNat_lt.mpr (by omega)
    unfold coeffInt
    rw [if_pos (by omega)]

/-- The full integer-indexed coefficient fold is the corresponding product
coefficient. -/
theorem coeffFold_eq_mul {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    (b g : DensePoly R) (t : Int) :
    coeffFold b g t b.size = coeffInt (b * g) t := by
  by_cases ht : t < 0
  · have hterm (k : Nat) : coeffInt g (t - (k : Int)) = 0 := by
      have hk0 := Int.natCast_nonneg k
      unfold coeffInt
      rw [if_pos (by omega)]
    have hfold (xs : List Nat) (init : R) :
        xs.foldl
          (fun acc k => acc + b.coeff k * coeffInt g (t - (k : Int))) init =
            init := by
      induction xs generalizing init with
      | nil => rfl
      | cons k ks ih =>
          rw [List.foldl_cons, hterm]
          have hstep : init + b.coeff k * (0 : R) = init := by grind
          rw [hstep]
          exact ih init
    unfold coeffFold
    rw [hfold]
    unfold coeffInt
    rw [if_pos ht]
  · have ht0 : 0 ≤ t := by omega
    have hstep (acc : R) (k : Nat) :
        acc + b.coeff k * coeffInt g (t - (k : Int)) =
          if k ≤ t.toNat ∧ t.toNat - k < g.size then
            acc + b.coeff k * g.coeff (t.toNat - k)
          else acc := by
      rw [coeffInt_sub_nat g t ht0 k]
      by_cases hk : k ≤ t.toNat
      · rw [if_pos hk]
        by_cases hgk : t.toNat - k < g.size
        · rw [if_pos ⟨hk, hgk⟩]
        · rw [if_neg (by omega)]
          rw [coeff_eq_zero_of_size_le g (by omega)]
          rw [show (Zero.zero : R) = 0 from rfl,
            Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
      · rw [if_neg hk, if_neg (by omega)]
        rw [Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
    have hfold (xs : List Nat) (init : R) :
        xs.foldl
          (fun acc k => acc + b.coeff k * coeffInt g (t - (k : Int))) init =
        xs.foldl
          (fun acc k =>
            if k ≤ t.toNat ∧ t.toNat - k < g.size then
              acc + b.coeff k * g.coeff (t.toNat - k)
            else acc) init := by
      induction xs generalizing init with
      | nil => rfl
      | cons k ks ih =>
          rw [List.foldl_cons, List.foldl_cons, hstep]
          exact ih _
    unfold coeffFold
    rw [hfold]
    unfold coeffInt
    rw [if_neg ht]
    rw [coeff_mul, mulCoeffSum_eq_singleFold]
    rfl

/-- Brown's polynomial update is coefficientwise the original coefficient plus
the multiplier convolution. -/
theorem coeffInt_add_mul {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (f b g : DensePoly R) (t : Int) :
    coeffInt (f + b * g) t = coeffInt f t + coeffFold b g t b.size := by
  rw [coeffInt_add, coeffFold_eq_mul]

/-- One destination column of the swapped generalized Sylvester matrix becomes
the corresponding `H = F + B * G` column after the Brown update. -/
private theorem productCol_addMul {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db J l : Nat) (f g b h : DensePoly R)
    (hJ : J < dg) (hdeg : df = db + dg) (hb : b.size ≤ db + 1)
    (hh : h = f + b * g) (d : Nat) (hd : d < dg - J)
    (i dst : Fin ((dg - J) + (df - J)))
    (hdstVal : dst.val = df - J + d) :
    SubresultantMinor.productCol
      (coeffMatrixAt dg df J l g f) dst db d (by
        omega) b i (db + 1) (Nat.le_refl _) =
      coeffMatrixAt dg df J l g h i dst := by
  have hsrc : db + d < dst.val := by
    omega
  by_cases hi : i.val = (dg - J) + (df - J) - 1
  · let t := Int.ofNat l - Int.ofNat (dg - J - 1) + Int.ofNat d
    have hdst : coeffMatrixAt dg df J l g f i dst = coeffInt f t := by
      simp [coeffMatrixAt, t, hi, hdstVal]
      omega
    have hsources : ∀ k, k < db + 1 →
        coeffMatrixAt dg df J l g f i
          ⟨db + d - k, by
            have := dst.isLt
            omega⟩ = coeffInt g (t - (k : Int)) := by
      intro k hk
      unfold coeffMatrixAt
      simp only
      rw [if_pos (by omega), if_pos (by omega)]
      congr 1
      simp only [t, Int.ofNat_eq_natCast]
      rw [Int.ofNat_sub (by omega : k ≤ db + d)]
      omega
    have hcol := productCol_eq_add_coeffFold
      (coeffMatrixAt dg df J l g f) dst db d hsrc b f g i t
      (db + 1) (Nat.le_refl _) hdst hsources
    rw [hcol]
    rw [coeffFold_of_size_le b g t (db + 1) hb,
      ← coeffInt_add_mul f b g t, ← hh]
    simp [coeffMatrixAt, t, hi, hdstVal]
    omega
  · let t := Int.ofNat df - Int.ofNat i.val + Int.ofNat d
    have hdst : coeffMatrixAt dg df J l g f i dst = coeffInt f t := by
      simp [coeffMatrixAt, t, hi, hdstVal]
      omega
    have hsources : ∀ k, k < db + 1 →
        coeffMatrixAt dg df J l g f i
          ⟨db + d - k, by
            have := dst.isLt
            omega⟩ = coeffInt g (t - (k : Int)) := by
      intro k hk
      unfold coeffMatrixAt
      simp only
      rw [if_pos (by omega), if_neg (by omega)]
      congr 1
      simp only [t, Int.ofNat_eq_natCast]
      rw [Int.ofNat_sub (by omega : k ≤ db + d)]
      omega
    have hcol := productCol_eq_add_coeffFold
      (coeffMatrixAt dg df J l g f) dst db d hsrc b f g i t
      (db + 1) (Nat.le_refl _) hdst hsources
    rw [hcol]
    rw [coeffFold_of_size_le b g t (db + 1) hb,
      ← coeffInt_add_mul f b g t, ← hh]
    simp [coeffMatrixAt, t, hi, hdstVal]
    omega

/-- Brown's unit upper-triangular column transformation turns the swapped
generalized Sylvester matrix for `G, F` into the coefficient matrix with blocks
`G, H`, where `H = F + B * G`. -/
theorem productCols_addMul {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db J l : Nat) (f g b h : DensePoly R)
    (hJ : J < dg) (hdeg : df = db + dg) (hb : b.size ≤ db + 1)
    (hh : h = f + b * g) :
    SubresultantMinor.productCols
      (coeffMatrixAt dg df J l g f) (df - J) db b (dg - J)
        (by omega) (by omega) =
      coeffMatrixAt dg df J l g h := by
  funext i j
  rw [SubresultantMinor.productCols_apply]
  by_cases hj : df - J ≤ j.val ∧ j.val < df - J + (dg - J)
  · rw [dif_pos hj]
    let d := j.val - (df - J)
    have hd : d < dg - J := by
      simp [d]
      omega
    exact productCol_addMul df dg db J l f g b h hJ hdeg hb hh
      d hd i j (by simp [d]; omega)
  · rw [dif_neg hj]
    have hjleft : j.val < df - J := by
      have := j.isLt
      omega
    simp [coeffMatrixAt, hjleft]

/-- The Brown column transformation preserves the determinant of the swapped
generalized Sylvester matrix. -/
theorem det_addMul {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db J l : Nat) (f g b h : DensePoly R)
    (hJ : J < dg) (hdeg : df = db + dg) (hb : b.size ≤ db + 1)
    (hh : h = f + b * g) :
    SubresultantMinor.det (coeffMatrixAt dg df J l g h) =
      SubresultantMinor.det (coeffMatrixAt dg df J l g f) := by
  rw [← productCols_addMul df dg db J l f g b h hJ hdeg hb hh]
  exact SubresultantMinor.det_productCols
    (coeffMatrixAt dg df J l g f) (df - J) db b (dg - J)
      (by omega) (by omega)

/-- The column-operation form of Brown--Traub equation (18): after swapping the
input blocks, a unit upper-triangular transformation replaces `F` by
`H = F + B * G` and leaves only the usual block-swap sign. -/
theorem coeffMinorAt_addMul {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db J l : Nat) (f g b h : DensePoly R)
    (hJ : J < dg) (hdeg : df = db + dg) (hb : b.size ≤ db + 1)
    (hh : h = f + b * g) :
    coeffMinorAt df dg J l f g =
      SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) *
        coeffMinorAt dg df J l g h := by
  rw [coeffMinorAt_swap]
  unfold coeffMinorAt
  rw [det_addMul df dg db J l f g b h hJ hdeg hb hh]

end Subresultant
end DensePoly
end Hex
