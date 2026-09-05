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
        simp only [addProduct, addCol_apply, ite_true, productCol]
        rw [ih, ite_eq_left rfl, ih, ite_eq_right hsrcDst]
      · simp only [addProduct, addCol_apply, ite_eq_right hj]
        rw [ih, ite_eq_right hj]

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
        rw [dite_eq_left hold, dite_eq_left hnew]
        apply productCol_congr M' M j db (j.val - split) (by omega) b i
          (db + 1) (Nat.le_refl _)
        · dsimp only [M']
          rw [addProduct_apply]
          rw [ite_eq_right (by
            intro heq
            have hval := congrArg Fin.val heq
            simp [dst] at hval
            omega)]
        · intro k hk
          dsimp only [M']
          rw [addProduct_apply]
          rw [ite_eq_right (by
            intro heq
            have hval := congrArg Fin.val heq
            simp [dst] at hval
            omega)]
      · by_cases hlast : j.val = split + right
        · have hnew : split ≤ j.val ∧ j.val < split + (right + 1) := by
            omega
          rw [dite_eq_right hold, dite_eq_left hnew]
          have hjdst : j = dst := Fin.ext hlast
          subst j
          rw [addProduct_apply, ite_eq_left rfl]
          congr 3
          simp [dst]
        · have hnew : ¬(split ≤ j.val ∧ j.val < split + (right + 1)) := by
            omega
          rw [dite_eq_right hold, dite_eq_right hnew]
          rw [addProduct_apply]
          rw [ite_eq_right (by
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
  · rw [ite_eq_left hk]
    have hkInt : (k : Int) ≤ t := by
      rw [← htCast]
      exact Int.ofNat_le.mpr hk
    unfold coeffInt
    rw [ite_eq_right (by
      have hk0 := Int.natCast_nonneg k
      omega)]
    congr 1
    apply Int.natCast_inj.mp
    rw [Int.toNat_sub_of_le hkInt, Int.ofNat_sub hk, htCast]
  · rw [ite_eq_right hk]
    have hkInt : t < (k : Int) := by
      rw [← htCast]
      exact Int.ofNat_lt.mpr (by omega)
    unfold coeffInt
    rw [ite_eq_left (by omega)]

/-- The full integer-indexed coefficient fold is the corresponding product
coefficient. -/
theorem coeffFold_eq_mul {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    (b g : DensePoly R) (t : Int) :
    coeffFold b g t b.size = coeffInt (b * g) t := by
  by_cases ht : t < 0
  · have hterm (k : Nat) : coeffInt g (t - (k : Int)) = 0 := by
      have hk0 := Int.natCast_nonneg k
      unfold coeffInt
      rw [ite_eq_left (by omega)]
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
    rw [ite_eq_left ht]
  · have ht0 : 0 ≤ t := by omega
    have hstep (acc : R) (k : Nat) :
        acc + b.coeff k * coeffInt g (t - (k : Int)) =
          if k ≤ t.toNat ∧ t.toNat - k < g.size then
            acc + b.coeff k * g.coeff (t.toNat - k)
          else acc := by
      rw [coeffInt_sub_nat g t ht0 k]
      by_cases hk : k ≤ t.toNat
      · rw [ite_eq_left hk]
        by_cases hgk : t.toNat - k < g.size
        · rw [ite_eq_left ⟨hk, hgk⟩]
        · rw [ite_eq_right (by omega)]
          rw [coeff_eq_zero_of_size_le g (by omega)]
          rw [show (Zero.zero : R) = 0 from rfl,
            Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
      · rw [ite_eq_right hk, ite_eq_right (by omega)]
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
    rw [ite_eq_right ht]
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
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
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
      rw [ite_eq_left (by omega), ite_eq_right (by omega)]
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
  · rw [dite_eq_left hj]
    let d := j.val - (df - J)
    have hd : d < dg - J := by
      simp [d]
      omega
    exact productCol_addMul df dg db J l f g b h hJ hdeg hb hh
      d hd i j (by simp [d]; omega)
  · rw [dite_eq_right hj]
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

/-- Raising the retained formal degree of the right input by one contributes
one leading coefficient of the left input, provided the right polynomial has
no coefficient at the new degree. This is used in the opposite direction to
collapse an artificially retained formal degree. -/
theorem coeffMinorAt_succRight {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dg dh J l : Nat) (g h : DensePoly R)
    (hpos : 0 < (dg - J) + (dh - J)) (hJh : J ≤ dh)
    (hg : g.size = dg + 1) (hh : h.size ≤ dh + 1) :
    coeffMinorAt dg (dh + 1) J l g h =
      g.leadingCoeff * coeffMinorAt dg dh J l g h := by
  let n := (dg - J) + (dh - J)
  have hnpos : 0 < n := by
    simpa [n] using hpos
  have hdim : ((dg - J) + (dh + 1 - J)) = n + 1 := by
    simp [n]
    omega
  let row : Fin (n + 1) := ⟨0, by omega⟩
  let M : SubresultantMinor.Square R (n + 1) :=
    SubresultantMinor.castSquare hdim
      (coeffMatrixAt dg (dh + 1) J l g h)
  have hleftPos : 0 < dh + 1 - J := by omega
  have hnotLast : 0 ≠ (dg - J) + (dh + 1 - J) - 1 := by omega
  have hfirst : M row row = g.leadingCoeff := by
    have hcoeff : g.coeff dg = g.leadingCoeff := by
      rw [leadingCoeff_eq_coeff_last g (by omega), hg]
      congr
    simpa [M, row, SubresultantMinor.castSquare, coeffMatrixAt,
      Fin.cast, hleftPos, hnotLast, n]
      using hcoeff
  have hzero (j : Fin (n + 1)) (hj : 0 < j.val) : M row j = 0 := by
    by_cases hleft : j.val < dh + 1 - J
    · have hbound : g.size ≤ dg + j.val := by
        rw [hg]
        omega
      simp only [M, row, SubresultantMinor.castSquare, coeffMatrixAt,
        Fin.cast]
      rw [ite_eq_left hleft, ite_eq_right hnotLast]
      rw [show Int.ofNat dg - Int.ofNat 0 + Int.ofNat j.val =
          ((dg + j.val : Nat) : Int) by
        simp [Int.ofNat_eq_natCast, Int.natCast_add]]
      rw [coeffInt_natCast]
      exact coeff_eq_zero_of_size_le g hbound
    · let jj := j.val - (dh + 1 - J)
      have hbound : h.size ≤ dh + 1 + jj := by
        simp [jj]
        omega
      simp only [M, row, SubresultantMinor.castSquare, coeffMatrixAt,
        Fin.cast]
      rw [ite_eq_right hleft, ite_eq_right hnotLast]
      rw [show Int.ofNat (dh + 1) - Int.ofNat 0 + Int.ofNat jj =
          ((dh + 1 + jj : Nat) : Int) by
        simp [Int.ofNat_eq_natCast, Int.natCast_add]]
      rw [coeffInt_natCast]
      exact coeff_eq_zero_of_size_le h hbound
  have hdelete : SubresultantMinor.deleteFirst M row =
      coeffMatrixAt dg dh J l g h := by
    funext i j
    change coeffMatrixAt dg (dh + 1) J l g h
        ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ =
      coeffMatrixAt dg dh J l g h i j
    simp only [coeffMatrixAt]
    by_cases hleft : j.val < dh - J
    · rw [ite_eq_left (by omega), ite_eq_left hleft]
      by_cases hlast : i.val = n - 1
      · rw [ite_eq_left (by omega), ite_eq_left hlast]
        congr 1
        simp [n]
        omega
      · rw [ite_eq_right (by omega), ite_eq_right hlast]
        congr 1
        simp [Int.ofNat_eq_natCast, Int.natCast_add] <;> omega
    · rw [ite_eq_right (by omega), ite_eq_right hleft]
      by_cases hlast : i.val = n - 1
      · rw [ite_eq_left (by omega), ite_eq_left hlast]
        congr 1
        simp [Int.ofNat_eq_natCast] <;> omega
      · rw [ite_eq_right (by omega), ite_eq_right hlast]
        congr 1
        simp [Int.ofNat_eq_natCast, Int.natCast_add] <;> omega
  unfold coeffMinorAt
  rw [← SubresultantMinor.det_castSquare hdim]
  change SubresultantMinor.det M = _
  rw [SubresultantMinor.det_firstRow M hzero, hfirst, hdelete]

/-- Raising the retained formal degree of the right input repeatedly
contributes the corresponding power of the left leading coefficient. Reading
the equality right-to-left collapses all retained degrees at once. -/
theorem coeffMinorAt_raiseRight {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dg dh J l extra : Nat) (g h : DensePoly R)
    (hpos : 0 < (dg - J) + (dh - J)) (hJh : J ≤ dh)
    (hg : g.size = dg + 1) (hh : h.size ≤ dh + 1) :
    coeffMinorAt dg (dh + extra) J l g h =
      g.leadingCoeff ^ extra * coeffMinorAt dg dh J l g h := by
  induction extra with
  | zero =>
      rw [Nat.add_zero, Lean.Grind.Semiring.pow_zero]
      grind
  | succ extra ih =>
      rw [Nat.add_succ,
        coeffMinorAt_succRight dg (dh + extra) J l g h (by omega)
          (by omega) hg (by omega),
        ih, Lean.Grind.Semiring.pow_succ]
      grind

/-- At the right input's formal degree, the left polynomial block is empty. -/
private theorem coeffMinorAt_rightDegree_ignore {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dg dh l : Nat) (h g : DensePoly R) :
    coeffMinorAt dh dg dh l h g =
      coeffMinorAt dh dg dh l h 0 := by
  unfold coeffMinorAt
  apply congrArg SubresultantMinor.det
  funext i j
  have hj : j.val < dg - dh := by
    have := j.isLt
    omega
  simp [coeffMatrixAt, hj]

/-- The first nonempty edge minor is the selected coefficient of the right
input. -/
private theorem coeffMinorAt_unitRight {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dh l : Nat) (h : DensePoly R) :
    coeffMinorAt dh (dh + 1) dh l h 0 = h.coeff l := by
  unfold coeffMinorAt
  have hdim : (dh - dh) + (dh + 1 - dh) = 1 := by omega
  rw [← SubresultantMinor.det_castSquare hdim]
  let M : SubresultantMinor.Square R 1 :=
    SubresultantMinor.castSquare hdim
      (coeffMatrixAt dh (dh + 1) dh l h 0)
  change SubresultantMinor.det M = _
  rw [SubresultantMinor.det_firstRow M (by
    intro j hj
    omega)]
  have hentry : M ⟨0, by omega⟩ ⟨0, by omega⟩ = h.coeff l := by
    simp [M, coeffMatrixAt, Fin.cast]
  rw [hentry, SubresultantMinor.det_zero]
  grind

/-- When the right formal degree is one below the left and the subresultant
index equals it, the one-entry coefficient minor selects the right input. -/
theorem coeffMinorAt_leftSucc {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dh l : Nat) (g h : DensePoly R) :
    coeffMinorAt (dh + 1) dh dh l g h = h.coeff l := by
  rw [coeffMinorAt_swap]
  simp only [Nat.sub_self, Nat.mul_zero, SubresultantMinor.sign]
  rw [ite_eq_left (by decide), Lean.Grind.Semiring.one_mul,
    coeffMinorAt_rightDegree_ignore, coeffMinorAt_unitRight]

/-- The subresultant immediately below the divisor degree is the signed
pseudo-remainder. This includes defective remainders: no exact degree is
assumed for the remainder. -/
theorem poly_prem {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [Div R] [ExactDivLaws R]
    (f g : DensePoly R) (hgsize : 2 ≤ g.size) (hgf : g.size ≤ f.size) :
    poly (g.size - 2) f g =
      scale
        (SubresultantMinor.sign (R := R) (f.size - g.size + 1))
        (pseudoDivMod f g).2 := by
  let df := f.size - 1
  let dg := g.size - 1
  let db := f.size - g.size
  let J := g.size - 2
  let a := g.leadingCoeff ^ (db + 1)
  let q := (pseudoDivMod f g).1
  let r := (pseudoDivMod f g).2
  let b := scale (0 - 1) q
  have hg : g ≠ 0 := by
    intro hzero
    subst g
    simp at hgsize
  have hglc : g.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size g (by omega)
  have h1 : (1 : R) ≠ 0 := one_ne_zero_of_nonzero hglc
  have hneg : (0 - 1 : R) ≠ 0 := negOne_ne_zero_of_one h1
  have ha : a ≠ 0 := pow_ne_zero h1 hglc (db + 1)
  have hqsize : q.size ≤ db + 1 := by
    simpa only [q, db] using pseudoDivMod_quotient_size_le f g
  have hbsize : b.size ≤ db + 1 := by
    rw [size_scale hneg]
    exact hqsize
  have hrsize : r.size ≤ J + 1 := by
    have hrlt : r.size < g.size := by
      simpa only [r] using pseudoDivMod_remainder_lt f g hg
    dsimp only [J]
    omega
  have hrec : scale a f = q * g + r := by
    simpa only [a, db, q, r] using pseudoDivMod_reconstruct f g hg hgf
  have hbneg : b = -q := by
    apply ext_coeff
    intro i
    simp only [b, coeff_scale_semiring, coeff_neg_ring]
    grind
  have hr : r = scale a f + b * g := by
    rw [hbneg]
    grind
  have hdf : df = db + dg := by
    dsimp only [df, db, dg]
    omega
  have hfg : g.size = dg + 1 := by
    dsimp only [dg]
    omega
  have hff : formalDegree f = df := by
    simp [formalDegree, df]
  have hgg : formalDegree g = dg := by
    simp [formalDegree, dg]
  apply ext_coeff
  intro l
  rw [coeff_scale_semiring]
  simp only [coeff_poly]
  by_cases hl : l < J + 1
  · rw [ite_eq_left hl]
    unfold coeffMinor
    rw [hff, hgg]
    have hscale := coeffMinorAt_scale_left df dg J l a f g
    have hadd := coeffMinorAt_addMul df dg db J l (scale a f) g b r
      (by dsimp only [dg, J]; omega) hdf hbsize hr
    have hraise := coeffMinorAt_raiseRight dg J J l (df - J) g r
      (by dsimp only [dg, J]; omega) (Nat.le_refl _) hfg hrsize
    rw [show J + (df - J) = df by dsimp only [df, J]; omega] at hraise
    have hedge : coeffMinorAt dg J J l g r = r.coeff l := by
      rw [show dg = J + 1 by dsimp only [dg, J]; omega]
      exact coeffMinorAt_leftSucc J l g r
    rw [hadd, hraise, hedge] at hscale
    have hdfJ : df - J = db + 1 := by
      dsimp only [df, J, db]
      omega
    have hdgJ : dg - J = 1 := by
      dsimp only [dg, J]
      omega
    have hpow : g.leadingCoeff ^ (df - J) = a := by
      rw [hdfJ]
    have hunit : a ^ (dg - J) = a := by
      rw [hdgJ, Lean.Grind.Semiring.pow_one]
    have hsign :
        SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) =
          SubresultantMinor.sign (db + 1) := by
      rw [hdfJ, hdgJ, Nat.mul_one]
    rw [hpow, hunit, hsign] at hscale
    apply ExactDivLaws.mul_right_cancel ha
    grind
  · rw [ite_eq_right hl]
    have hrzero : r.coeff l = 0 :=
      coeff_eq_zero_of_size_le r (by omega)
    rw [hrzero, Lean.Grind.Semiring.mul_zero]
    rfl

/-- The subresultant at the right input's degree is that input multiplied by
the expected power of its leading coefficient. -/
theorem coeffMinorAt_rightDegree {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dg dh l : Nat) (g h : DensePoly R)
    (hdh : dh < dg) (hh : h.size = dh + 1) :
    coeffMinorAt dg dh dh l g h =
      h.leadingCoeff ^ (dg - dh - 1) * h.coeff l := by
  rw [coeffMinorAt_swap]
  simp only [Nat.sub_self, Nat.mul_zero, SubresultantMinor.sign]
  rw [ite_eq_left (by decide)]
  rw [Lean.Grind.Semiring.one_mul,
    coeffMinorAt_rightDegree_ignore dg dh l h g]
  have hsum : dh + 1 + (dg - (dh + 1)) = dg := by omega
  have hraise := coeffMinorAt_raiseRight dh (dh + 1) dh l
    (dg - (dh + 1)) h (0 : DensePoly R) (by omega) (by omega) hh (by simp)
  rw [hsum] at hraise
  rw [hraise, coeffMinorAt_unitRight]
  congr 2

/-- Brown--Traub equation (12): if `H = F + B * G`, then the generalized
Sylvester coefficient minor for `F, G` is the `G, H` minor at any formal degree
bounding `H`, times the block-swap sign and one `lc(G)` for every collapsed
formal degree. -/
theorem coeffMinorAt_brownTraub {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db dh J l : Nat) (f g b h : DensePoly R)
    (hJh : J ≤ dh) (hdh : dh < dg)
    (hdeg : df = db + dg) (hg : g.size = dg + 1)
    (hb : b.size ≤ db + 1) (hhsize : h.size ≤ dh + 1)
    (hh : h = f + b * g) :
    coeffMinorAt df dg J l f g =
      SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) *
        (g.leadingCoeff ^ (df - dh) * coeffMinorAt dg dh J l g h) := by
  have hJg : J < dg := by omega
  have hdhf : dh ≤ df := by omega
  rw [coeffMinorAt_addMul df dg db J l f g b h hJg hdeg hb hh]
  rw [← show dh + (df - dh) = df by omega]
  rw [coeffMinorAt_raiseRight dg dh J l (df - dh) g h (by omega) hJh hg
    hhsize]
  simp

/-- The generalized subresultant at the right input's degree is a scalar
multiple of that input. -/
theorem poly_rightDegree {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (dg dh : Nat) (g h : DensePoly R)
    (hdh : dh < dg) (hg : g.size = dg + 1) (hh : h.size = dh + 1) :
    poly dh g h = scale (h.leadingCoeff ^ (dg - dh - 1)) h := by
  have hfg : formalDegree g = dg := by simp [formalDegree, hg]
  have hfh : formalDegree h = dh := by simp [formalDegree, hh]
  apply ext_coeff
  intro l
  rw [coeff_scale_semiring]
  simp only [coeff_poly]
  by_cases hl : l < dh + 1
  · rw [ite_eq_left hl]
    unfold coeffMinor
    rw [hfg, hfh]
    exact coeffMinorAt_rightDegree dg dh l g h hdh hh
  · rw [ite_eq_right hl, coeff_eq_zero_of_size_le h (by omega)]
    change (0 : R) = h.leadingCoeff ^ (dg - dh - 1) * (0 : R)
    rw [Lean.Grind.Semiring.mul_zero]

/-- Polynomial form of the Brown--Traub transformation at or below the degree
of `H`. -/
theorem poly_brownTraub {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db dh J : Nat) (f g b h : DensePoly R)
    (hJh : J ≤ dh) (hdh : dh < dg) (hdeg : df = db + dg)
    (hf : f.size = df + 1) (hg : g.size = dg + 1)
    (hb : b.size ≤ db + 1) (hhsize : h.size = dh + 1)
    (hh : h = f + b * g) :
    poly J f g =
      scale
        (SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) *
          g.leadingCoeff ^ (df - dh))
        (poly J g h) := by
  have hff : formalDegree f = df := by simp [formalDegree, hf]
  have hfg : formalDegree g = dg := by simp [formalDegree, hg]
  have hfh : formalDegree h = dh := by simp [formalDegree, hhsize]
  apply ext_coeff
  intro l
  rw [coeff_scale_semiring]
  simp only [coeff_poly]
  by_cases hl : l < J + 1
  · rw [ite_eq_left hl, ite_eq_left hl]
    unfold coeffMinor
    rw [hff, hfg, hfh]
    rw [coeffMinorAt_brownTraub df dg db dh J l f g b h hJh hdh hdeg
      hg hb (by omega) hh]
    grind
  · rw [ite_eq_right hl, ite_eq_right hl]
    change (0 : R) =
      (SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) *
        g.leadingCoeff ^ (df - dh)) * (0 : R)
    rw [Lean.Grind.Semiring.mul_zero]

/-- Transport a generalized subresultant family across one scaled
pseudo-remainder step. The identity stays cross-multiplied, so every scalar
remains in the base ring even across defective degree drops. -/
theorem poly_descent {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [Div R] [ExactDivLaws R]
    (f g h : DensePoly R) {c : R} (hc : c ≠ 0)
    (hg : g ≠ 0) (hh : h ≠ 0) (hgf : g.size ≤ f.size)
    (hp : (pseudoDivMod f g).2 = scale c h)
    (J : Nat) (hJ : J < h.size) :
    scale
        (g.leadingCoeff ^
          ((f.size - g.size + 1) * (g.size - 1 - J)))
        (poly J f g) =
      scale
        (SubresultantMinor.sign (R := R)
            ((f.size - 1 - J) * (g.size - 1 - J)) *
          g.leadingCoeff ^ (f.size - h.size) *
          c ^ (g.size - 1 - J))
        (poly J g h) := by
  let df := f.size - 1
  let dg := g.size - 1
  let db := f.size - g.size
  let dh := h.size - 1
  let a := g.leadingCoeff ^ (db + 1)
  let q := (pseudoDivMod f g).1
  let b := scale (0 - 1) q
  have hgpos : 0 < g.size := Nat.pos_of_ne_zero fun hzero =>
    hg ((size_eq_zero_iff g).mp hzero)
  have hhpos : 0 < h.size := Nat.pos_of_ne_zero fun hzero =>
    hh ((size_eq_zero_iff h).mp hzero)
  have hglc : g.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size g hgpos
  have h1 : (1 : R) ≠ 0 := one_ne_zero_of_nonzero hglc
  have hneg : (0 - 1 : R) ≠ 0 := negOne_ne_zero_of_one h1
  have ha : a ≠ 0 := pow_ne_zero h1 hglc (db + 1)
  have hbsize : b.size ≤ db + 1 := by
    rw [size_scale hneg]
    simpa only [q, db] using pseudoDivMod_quotient_size_le f g
  have hrec := pseudoDivMod_reconstruct f g hg hgf
  have hbneg : b = -q := by
    apply ext_coeff
    intro i
    simp only [b, coeff_scale_semiring, coeff_neg_ring]
    grind
  have hrem : scale c h = scale a f + b * g := by
    rw [hbneg, ← hp]
    simpa only [a, db, q] using (show
      (pseudoDivMod f g).2 =
        scale (g.leadingCoeff ^ (f.size - g.size + 1)) f +
          -(pseudoDivMod f g).1 * g by
      grind)
  have hdf : df = db + dg := by
    dsimp only [df, db, dg]
    omega
  have hdhg : dh < dg := by
    have hremSize : (pseudoDivMod f g).2.size < g.size :=
      pseudoDivMod_remainder_lt f g hg
    rw [hp, size_scale hc] at hremSize
    dsimp only [dh, dg]
    omega
  have hJh : J ≤ dh := by
    dsimp only [dh]
    omega
  have hfsize : (scale a f).size = df + 1 := by
    rw [size_scale ha]
    dsimp only [df]
    omega
  have hgsize : g.size = dg + 1 := by
    dsimp only [dg]
    omega
  have hhsize : (scale c h).size = dh + 1 := by
    rw [size_scale hc]
    dsimp only [dh]
    omega
  have hBT := poly_brownTraub df dg db dh J (scale a f) g b (scale c h)
    hJh hdhg hdf hfsize hgsize hbsize hhsize hrem
  have hleft := poly_scale_left ha J f g
  have hright := poly_scale_right hc J g h
  have hfgdeg : formalDegree g = dg := by simp [formalDegree, dg]
  rw [hleft, hright, scale_scale] at hBT
  rw [hfgdeg] at hBT
  have haPow : a ^ (dg - J) =
      g.leadingCoeff ^ ((db + 1) * (dg - J)) := by
    exact (pow_mul g.leadingCoeff (db + 1) (dg - J)).symm
  rw [haPow] at hBT
  have hdiff : df - dh = f.size - h.size := by
    dsimp only [df, dh]
    omega
  rw [hdiff] at hBT
  simpa only [df, dg, db, dh, Nat.add_comm] using hBT

/-- Endpoint form of Brown--Traub equation (12), including both leading
coefficient powers. -/
theorem poly_brownTraub_rightDegree {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (df dg db dh : Nat) (f g b h : DensePoly R)
    (hdh : dh < dg) (hdeg : df = db + dg)
    (hf : f.size = df + 1) (hg : g.size = dg + 1)
    (hb : b.size ≤ db + 1) (hhsize : h.size = dh + 1)
    (hh : h = f + b * g) :
    poly dh f g =
      scale
        (SubresultantMinor.sign (R := R) ((df - dh) * (dg - dh)) *
          g.leadingCoeff ^ (df - dh) * h.leadingCoeff ^ (dg - dh - 1)) h := by
  rw [poly_brownTraub df dg db dh dh f g b h (Nat.le_refl _) hdh hdeg hf hg
    hb hhsize hh]
  rw [poly_rightDegree dg dh g h hdh hg hhsize, scale_scale]

/-- The endpoint factorization makes its scalar quotient coefficientwise
exact in every lawful exact-division domain. -/
theorem divScalar_brownTraub {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [Div R] [ExactDivLaws R]
    (df dg db dh : Nat) (f g b h : DensePoly R)
    (hdh : dh < dg) (hdeg : df = db + dg)
    (hf : f.size = df + 1) (hg : g.size = dg + 1)
    (hb : b.size ≤ db + 1) (hhsize : h.size = dh + 1)
    (hh : h = f + b * g)
    (h1 : (1 : R) ≠ 0) :
    divScalar (poly dh f g)
        (SubresultantMinor.sign (R := R) ((df - dh) * (dg - dh)) *
          g.leadingCoeff ^ (df - dh) * h.leadingCoeff ^ (dg - dh - 1)) = h := by
  have hsign :
      SubresultantMinor.sign (R := R) ((df - dh) * (dg - dh)) ≠ 0 :=
    SubresultantMinor.sign_ne_zero h1 _
  have hglc : g.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size g (by omega)
  have hhlc : h.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size h (by omega)
  have hc : SubresultantMinor.sign (R := R) ((df - dh) * (dg - dh)) *
      g.leadingCoeff ^ (df - dh) * h.leadingCoeff ^ (dg - dh - 1) ≠ 0 :=
    ExactDivLaws.mul_ne_zero
      (ExactDivLaws.mul_ne_zero hsign (pow_ne_zero h1 hglc _))
      (pow_ne_zero h1 hhlc _)
  rw [poly_brownTraub_rightDegree df dg db dh f g b h hdh hdeg hf hg hb
    hhsize hh]
  exact divScalar_scale h hc

/-- A positive-size all-zero right block makes the zeroth coefficient minor
vanish. -/
private theorem coeffMinorAt_zero_right {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R]
    (d : Nat) (hd : 0 < d) (g : DensePoly R) :
    coeffMinorAt d 0 0 0 g 0 = 0 := by
  unfold coeffMinorAt
  let M := coeffMatrixAt d 0 0 0 g (0 : DensePoly R)
  change SubresultantMinor.det M = 0
  let dst : Fin d := ⟨0, hd⟩
  have hcol (i : Fin d) : M i dst = 0 := by
    simp [M, dst, coeffMatrixAt, coeffInt]
  have hset :
      SubresultantMinor.setCol M dst (fun _ => 0) = M := by
    funext i j
    by_cases hj : j = dst
    · subst j
      simp [SubresultantMinor.setCol, hcol]
    · simp [SubresultantMinor.setCol, hj]
  rw [← hset]
  exact SubresultantMinor.det_setCol_zero M dst

/-- If an ordered pseudo-division terminates at a nonconstant divisor, the
zeroth generalized subresultant vanishes. -/
theorem coeffMinor_zero_of_prem_zero {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [Div R] [ExactDivLaws R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size)
    (hgBig : 2 ≤ g.size) (hp : (pseudoDivMod f g).2 = 0) :
    coeffMinor 0 0 f g = 0 := by
  let df := f.size - 1
  let dg := g.size - 1
  let db := f.size - g.size
  let a := g.leadingCoeff ^ (db + 1)
  let q := (pseudoDivMod f g).1
  let b := scale (0 - 1) q
  have hgpos : 0 < g.size := by omega
  have hglc : g.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size g hgpos
  have h1 : (1 : R) ≠ 0 := one_ne_zero_of_nonzero hglc
  have ha : a ≠ 0 := pow_ne_zero h1 hglc (db + 1)
  have hbsize : b.size ≤ db + 1 := by
    have hneg : (0 - 1 : R) ≠ 0 := negOne_ne_zero_of_one h1
    rw [size_scale hneg]
    simpa only [q, db] using pseudoDivMod_quotient_size_le f g
  have hbneg : b = -q := by
    apply ext_coeff
    intro i
    simp only [b, coeff_scale_semiring, coeff_neg_ring]
    grind
  have hzero : (0 : DensePoly R) = scale a f + b * g := by
    rw [hbneg]
    have hrec := pseudoDivMod_reconstruct f g hg hgf
    rw [hp] at hrec
    simpa only [a, db, q] using (show
      (0 : DensePoly R) =
        scale (g.leadingCoeff ^ (f.size - g.size + 1)) f +
          -(pseudoDivMod f g).1 * g by grind)
  have hdf : df = db + dg := by
    dsimp only [df, db, dg]
    omega
  have hfg : g.size = dg + 1 := by
    dsimp only [dg]
    omega
  have hdg : 0 < dg := by
    dsimp only [dg]
    omega
  have hbt := coeffMinorAt_brownTraub df dg db 0 0 0
    (scale a f) g b (0 : DensePoly R) (Nat.le_refl 0) hdg hdf hfg
    hbsize (by simp) hzero
  have hright : coeffMinorAt dg 0 0 0 g 0 = 0 :=
    coeffMinorAt_zero_right dg hdg g
  rw [hright, Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.mul_zero] at hbt
  have hscale := coeffMinorAt_scale_left df dg 0 0 a f g
  rw [hbt] at hscale
  have hapow : a ^ (dg - 0) ≠ 0 := pow_ne_zero h1 ha (dg - 0)
  have hminor : coeffMinorAt df dg 0 0 f g = 0 := by
    apply ExactDivLaws.mul_right_cancel hapow
    grind
  unfold coeffMinor
  have hff : formalDegree f = df := by
    simp [formalDegree, df]
  have hgg : formalDegree g = dg := by
    simp [formalDegree, dg]
  rw [hff, hgg]
  exact hminor

end Subresultant
end DensePoly
end Hex
