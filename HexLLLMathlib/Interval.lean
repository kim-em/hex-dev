/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Basic
public import HexGramSchmidtMathlib.Int

public section

/-!
Soundness of the fixed-precision interval reducedness checker.

`Hex.lllReducedInterval` runs an enclosure Gram-Schmidt pass over the exact
integer Gram matrix of a candidate basis and accepts only when every
independence, size-reduction, and Lovász inequality is decided with the
enclosure strictly on the correct side. This module proves that acceptance
entails the exact rational predicates: `Hex.isLLLReduced b δ η` together
with `Hex.Matrix.independent b`.

The proof has three layers:

* per-operation containment lemmas for the dyadic interval kernel
  (`Hex.Ival`): each operation's result encloses the exact rational value
  whenever its inputs do;
* the exact Gram-Schmidt recurrence over the Gram matrix
  (`gram_recurrence`): `⟨b_i, b_j⟩ = ⟨b_i, b*_j⟩ + Σ_{k<j} μ[j][k]·⟨b_i, b*_k⟩`,
  derived from `basis_decomposition` and `basis_orthogonal`, which is the
  recurrence the executable pass evaluates in interval arithmetic;
* a structural induction over the executable pass (`pass_spec`) showing
  every `μ[i][j]` and `‖b*_i‖²` enclosure contains its exact rational
  value, then reading the three accepted clauses back through the
  enclosures. Independence follows from strict positivity of every
  `‖b*_i‖²` enclosure via the unconditional Gram-determinant product
  identity `gramDet_eq_prod_normSq_uncond`.
-/

namespace HexLLLMathlib

open Hex Hex.Internal

/-! ### Rounding helpers -/

private theorem intCast_fdiv_le (p : Int) {S : Int} (hS : 0 < S) :
    ((Int.fdiv p S : Int) : Rat) ≤ (p : Rat) / (S : Rat) := by
  have hadd : S * Int.fdiv p S + Int.fmod p S = p := Int.mul_fdiv_add_fmod p S
  have hmod : (0 : Rat) ≤ (Int.fmod p S : Rat) := by
    exact_mod_cast Int.fmod_nonneg_of_pos p hS
  have hSQ : (0 : Rat) < (S : Rat) := by exact_mod_cast hS
  rw [le_div_iff₀ hSQ]
  have hp : ((S : Rat)) * ((Int.fdiv p S : Int) : Rat) + ((Int.fmod p S : Int) : Rat)
      = (p : Rat) := by exact_mod_cast congrArg (Int.cast : Int → Rat) hadd
  nlinarith [hp, hmod]

private theorem div_le_intCast_cdiv (p : Int) {S : Int} (hS : 0 < S) :
    (p : Rat) / (S : Rat) ≤ ((Ival.cdiv p S : Int) : Rat) := by
  have h := intCast_fdiv_le (-p) hS
  have h2 := neg_le_neg h
  calc (p : Rat) / (S : Rat) = -(((-p : Int) : Rat) / (S : Rat)) := by
        push_cast
        ring
    _ ≤ -((Int.fdiv (-p) S : Int) : Rat) := h2
    _ = ((Ival.cdiv p S : Int) : Rat) := by
        unfold Ival.cdiv
        push_cast
        ring

private theorem div_le_div_of_le_num {a b c : Rat} (hc : 0 < c) (h : a ≤ b) :
    a / c ≤ b / c := by
  have hinv : (0 : Rat) ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right h hinv

private theorem div_le_div_of_le_den {a b c : Rat} (ha : 0 ≤ a) (hb : 0 < b)
    (h : b ≤ c) : a / c ≤ a / b := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div a b]
  exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hb h) ha

private theorem div_le_div_of_nonpos_den {a b c : Rat} (ha : a ≤ 0) (hb : 0 < b)
    (h : b ≤ c) : a / b ≤ a / c := by
  rw [div_eq_mul_one_div a b, div_eq_mul_one_div a c]
  exact mul_le_mul_of_nonpos_left (one_div_le_one_div_of_le hb h) ha

/-! ### Containment lemmas for the interval kernel -/

private theorem mem_ofInt (S z : Int) : (Ival.ofInt S z).mem S (z : Rat) := by
  unfold Ival.ofInt Ival.mem
  constructor <;> simp [Int.cast_mul]

private theorem mem_add {S : Int} {I J : Ival} {x y : Rat}
    (hx : I.mem S x) (hy : J.mem S y) : (I.add J).mem S (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  unfold Ival.add Ival.mem
  push_cast
  constructor <;> [nlinarith; nlinarith]

private theorem mem_sub {S : Int} {I J : Ival} {x y : Rat}
    (hx : I.mem S x) (hy : J.mem S y) : (I.sub J).mem S (x - y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  unfold Ival.sub Ival.mem
  push_cast
  constructor <;> [nlinarith; nlinarith]

private theorem mul_le_max4 {x y A B C D : Rat}
    (hA : A ≤ x) (hB : x ≤ B) (hC : C ≤ y) (hD : y ≤ D) :
    x * y ≤ max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
  rcases le_total 0 y with hy | hy
  · have hxy : x * y ≤ B * y := mul_le_mul_of_nonneg_right hB hy
    rcases le_total 0 B with hB0 | hB0
    · have hBy : B * y ≤ B * D := mul_le_mul_of_nonneg_left hD hB0
      exact le_trans (le_trans hxy hBy) (le_max_of_le_right (le_max_right _ _))
    · have hBy : B * y ≤ B * C := mul_le_mul_of_nonpos_left hC hB0
      exact le_trans (le_trans hxy hBy) (le_max_of_le_right (le_max_left _ _))
  · have hxy : x * y ≤ A * y := mul_le_mul_of_nonpos_right hA hy
    rcases le_total 0 A with hA0 | hA0
    · have hAy : A * y ≤ A * D := mul_le_mul_of_nonneg_left hD hA0
      exact le_trans (le_trans hxy hAy) (le_max_of_le_left (le_max_right _ _))
    · have hAy : A * y ≤ A * C := mul_le_mul_of_nonpos_left hC hA0
      exact le_trans (le_trans hxy hAy) (le_max_of_le_left (le_max_left _ _))

private theorem min4_le_mul {x y A B C D : Rat}
    (hA : A ≤ x) (hB : x ≤ B) (hC : C ≤ y) (hD : y ≤ D) :
    min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * y := by
  have h := mul_le_max4 (x := -x) (y := y) (A := -B) (B := -A) (C := C) (D := D)
    (by linarith) (by linarith) hC hD
  rw [neg_mul] at h
  have hmax :
      max (max (-B * C) (-B * D)) (max (-A * C) (-A * D)) =
        -(min (min (B * C) (B * D)) (min (A * C) (A * D))) := by
    simp [max_neg_neg]
  rw [hmax] at h
  have := neg_le_neg h
  rw [neg_neg] at this
  calc min (min (A * C) (A * D)) (min (B * C) (B * D))
      = min (min (B * C) (B * D)) (min (A * C) (A * D)) := min_comm _ _
    _ ≤ x * y := by linarith

private theorem mem_mul {S : Int} (hS : 0 < S) {I J : Ival} {x y : Rat}
    (hx : I.mem S x) (hy : J.mem S y) : (I.mul S J).mem S (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  have hSQ : (0 : Rat) < (S : Rat) := by exact_mod_cast hS
  have hmax := mul_le_max4 h1 h2 h3 h4
  have hmin := min4_le_mul h1 h2 h3 h4
  unfold Ival.mul Ival.mem
  constructor
  · refine le_trans (intCast_fdiv_le _ hS) ?_
    rw [div_le_iff₀ hSQ]
    push_cast
    nlinarith [hmin]
  · refine le_trans ?_ (div_le_intCast_cdiv _ hS)
    rw [le_div_iff₀ hSQ]
    push_cast
    nlinarith [hmax]

private theorem mem_divPos {S : Int} (hS : 0 < S) {I J : Ival} {x y : Rat}
    (hx : I.mem S x) (hy : J.mem S y) (hpos : 0 < J.lo) :
    (I.divPos S J).mem S (x / y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  have hSQ : (0 : Rat) < (S : Rat) := by exact_mod_cast hS
  have hC : (0 : Rat) < (J.lo : Rat) := by exact_mod_cast hpos
  have hyS : (0 : Rat) < y * S := lt_of_lt_of_le hC h3
  have hy0 : 0 < y := by nlinarith
  have hDQ : (0 : Rat) < (J.hi : Rat) := lt_of_lt_of_le hC (le_trans h3 h4)
  have hD : 0 < J.hi := by exact_mod_cast hDQ
  have hquot : (x / y) * S = (x * S * S) / (y * S) := by
    field_simp
  have hcast_lo : ((I.lo * S : Int) : Rat) = (I.lo : Rat) * (S : Rat) := by push_cast; ring
  have hcast_hi : ((I.hi * S : Int) : Rat) = (I.hi : Rat) * (S : Rat) := by push_cast; ring
  unfold Ival.divPos Ival.mem
  constructor
  · -- lower endpoint
    have hnum : (I.lo : Rat) * S ≤ x * S * S :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hSQ)
    have hstep : ((I.lo * S : Int) : Rat) / (y * S) ≤ (x / y) * S := by
      rw [hquot, hcast_lo]
      exact div_le_div_of_le_num hyS hnum
    rcases le_total 0 ((I.lo * S : Int) : Rat) with hA0 | hA0
    · -- nonneg numerator: divide by the largest denominator J.hi
      have hfd : ((Int.fdiv (I.lo * S) J.hi : Int) : Rat) ≤
          ((I.lo * S : Int) : Rat) / (J.hi : Rat) := intCast_fdiv_le _ hD
      have hmono : ((I.lo * S : Int) : Rat) / (J.hi : Rat) ≤
          ((I.lo * S : Int) : Rat) / (y * S) := by
        rcases le_total (y * S) (J.hi : Rat) with hyJ | hyJ
        · exact div_le_div_of_le_den hA0 hyS hyJ
        · exact le_of_eq_of_le (by rw [le_antisymm h4 hyJ]) le_rfl
      have hchain := le_trans (le_trans hfd hmono) hstep
      refine le_trans ?_ hchain
      have : (min ((Int.fdiv (I.lo * S) J.lo)) ((Int.fdiv (I.lo * S) J.hi)) : Int) ≤
          Int.fdiv (I.lo * S) J.hi := min_le_right _ _
      exact_mod_cast this
    · -- nonpos numerator: divide by the smallest denominator J.lo
      have hfd : ((Int.fdiv (I.lo * S) J.lo : Int) : Rat) ≤
          ((I.lo * S : Int) : Rat) / (J.lo : Rat) := intCast_fdiv_le _ hpos
      have hmono : ((I.lo * S : Int) : Rat) / (J.lo : Rat) ≤
          ((I.lo * S : Int) : Rat) / (y * S) :=
        div_le_div_of_nonpos_den hA0 hC h3
      have hchain := le_trans (le_trans hfd hmono) hstep
      refine le_trans ?_ hchain
      have : (min ((Int.fdiv (I.lo * S) J.lo)) ((Int.fdiv (I.lo * S) J.hi)) : Int) ≤
          Int.fdiv (I.lo * S) J.lo := min_le_left _ _
      exact_mod_cast this
  · -- upper endpoint
    have hnum : x * S * S ≤ (I.hi : Rat) * S :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hSQ)
    have hstep : (x / y) * S ≤ ((I.hi * S : Int) : Rat) / (y * S) := by
      rw [hquot, hcast_hi]
      exact div_le_div_of_le_num hyS hnum
    rcases le_total 0 ((I.hi * S : Int) : Rat) with hB0 | hB0
    · -- nonneg numerator: bound by division through the smallest denominator
      have hcd : ((I.hi * S : Int) : Rat) / (J.lo : Rat) ≤
          ((Ival.cdiv (I.hi * S) J.lo : Int) : Rat) := div_le_intCast_cdiv _ hpos
      have hmono : ((I.hi * S : Int) : Rat) / (y * S) ≤
          ((I.hi * S : Int) : Rat) / (J.lo : Rat) :=
        div_le_div_of_le_den hB0 hC h3
      have hchain := le_trans (le_trans hstep hmono) hcd
      refine le_trans hchain ?_
      have : (Ival.cdiv (I.hi * S) J.lo : Int) ≤
          max (Ival.cdiv (I.hi * S) J.lo) (Ival.cdiv (I.hi * S) J.hi) := le_max_left _ _
      exact_mod_cast this
    · -- nonpos numerator: bound by division through the largest denominator
      have hcd : ((I.hi * S : Int) : Rat) / (J.hi : Rat) ≤
          ((Ival.cdiv (I.hi * S) J.hi : Int) : Rat) := div_le_intCast_cdiv _ hD
      have hmono : ((I.hi * S : Int) : Rat) / (y * S) ≤
          ((I.hi * S : Int) : Rat) / (J.hi : Rat) := by
        rcases le_total (y * S) (J.hi : Rat) with hyJ | hyJ
        · exact div_le_div_of_nonpos_den hB0 hyS hyJ
        · exact le_of_le_of_eq le_rfl (by rw [le_antisymm h4 hyJ])
      have hchain := le_trans (le_trans hstep hmono) hcd
      refine le_trans hchain ?_
      have : (Ival.cdiv (I.hi * S) J.hi : Int) ≤
          max (Ival.cdiv (I.hi * S) J.lo) (Ival.cdiv (I.hi * S) J.hi) := le_max_right _ _
      exact_mod_cast this

private theorem mem_ofRat {S : Int} (_hS : 0 < S) (q : Rat) :
    (Ival.ofRat S q).mem S q := by
  have hden : (0 : Int) < (q.den : Int) := by exact_mod_cast q.den_pos
  have hdenQ : (0 : Rat) < (q.den : Rat) := by exact_mod_cast q.den_pos
  have hq : q * (q.den : Rat) = (q.num : Rat) := by
    have h := Rat.num_div_den q
    field_simp at h
    linarith
  have hqS : ((q.num * S : Int) : Rat) / (q.den : Rat) = q * S := by
    rw [div_eq_iff (ne_of_gt hdenQ)]
    push_cast
    linear_combination (-(S : Rat)) * hq
  unfold Ival.ofRat Ival.mem
  constructor
  · exact le_of_le_of_eq (intCast_fdiv_le _ hden) hqS
  · exact le_of_eq_of_le hqS.symm (div_le_intCast_cdiv _ hden)

/-! ### Exact Gram-Schmidt recurrence over the Gram matrix -/

private theorem foldl_finRange_eq_sum {R : Type*} [AddCommMonoid R] {k : Nat}
    (f : Fin k → R) :
    (List.finRange k).foldl (fun acc i => acc + f i) 0 = ∑ i, f i := by
  rw [← List.foldl_map, ← List.sum_eq_foldl,
    ← List.sum_toFinset f (List.nodup_finRange k), List.toFinset_finRange]

private theorem dot_eq_sum {m' : Nat} (u v : Vector Rat m') :
    u.dotProduct v = ∑ k : Fin m', u[k] * v[k] := by
  unfold Vector.dotProduct
  exact foldl_finRange_eq_sum _

/-- The rational cast of a basis row of the integer input. -/
private noncomputable def castRow (b : Hex.Matrix Int n m) (i : Fin n) : Vector Rat m :=
  Vector.map (fun x : Int => (x : Rat)) (b.row i)

/-- Exact Gram-Schmidt coefficient `μ[i][j]`. -/
private noncomputable def muExact (b : Hex.Matrix Int n m) (i j : Fin n) : Rat :=
  GramSchmidt.entry (GramSchmidt.Int.coeffs b) i j

/-- Exact dot product `⟨b_i, b*_j⟩` of an input row against a
Gram-Schmidt basis row. -/
private noncomputable def gsDot (b : Hex.Matrix Int n m) (i j : Fin n) : Rat :=
  (castRow b i).dotProduct ((GramSchmidt.Int.basis b).row j)

/-- Exact squared Gram-Schmidt norm `‖b*_j‖²`. -/
private noncomputable def nrm (b : Hex.Matrix Int n m) (j : Fin n) : Rat :=
  Hex.Internal.LLLCore.basisNormSq (GramSchmidt.Int.basis b) j

private theorem nrm_eq_dot (b : Hex.Matrix Int n m) (j : Fin n) :
    nrm b j = ((GramSchmidt.Int.basis b).row j).dotProduct
      ((GramSchmidt.Int.basis b).row j) := by
  unfold nrm Hex.Internal.LLLCore.basisNormSq
  rfl

/-- Cast of an integer Gram entry as a rational dot product of cast rows. -/
private theorem gram_cast (b : Hex.Matrix Int n m) (i j : Fin n) :
    (((b.row i).dotProduct (b.row j) : Int) : Rat) =
      (castRow b i).dotProduct (castRow b j) := by
  rw [dot_eq_sum]
  rw [show (b.row i).dotProduct (b.row j) =
      ∑ k : Fin m, (b.row i)[k] * (b.row j)[k] from foldl_finRange_eq_sum _]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold castRow
  simp [Vector.getElem_map]

private theorem getElem_foldl_add_smul {m' : Nat} (xs : List (Fin m'))
    (w : Fin m' → Rat) (rows : Fin m' → Vector Rat m) (z : Vector Rat m)
    (l : Fin m) :
    (xs.foldl (fun acc k => acc + w k • rows k) z)[l] =
      z[l] + (xs.map (fun k => w k * (rows k)[l])).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      have : (z + w x • rows x)[l] = z[l] + w x * (rows x)[l] := by
        simp only [Fin.getElem_fin, Vector.getElem_add, Vector.getElem_smul]
        rfl
      rw [this]
      ring

private theorem getElem_prefixCombination
    (C : Hex.Matrix Rat n n) (B : Hex.Matrix Rat n m) (i : Nat) (hi : i < n)
    (l : Fin m) :
    (GramSchmidt.prefixCombination C B i hi)[l] =
      ∑ k : Fin i,
        GramSchmidt.entry C ⟨i, hi⟩ ⟨k.val, Nat.lt_trans k.isLt hi⟩ *
          (B.row ⟨k.val, Nat.lt_trans k.isLt hi⟩)[l] := by
  unfold GramSchmidt.prefixCombination
  rw [getElem_foldl_add_smul]
  have hz : (0 : Vector Rat m)[l] = 0 := by
    simp
  rw [hz, zero_add]
  rw [← foldl_finRange_eq_sum
    (fun k : Fin i =>
      GramSchmidt.entry C ⟨i, hi⟩ ⟨k.val, Nat.lt_trans k.isLt hi⟩ *
        (B.row ⟨k.val, Nat.lt_trans k.isLt hi⟩)[l])]
  rw [← List.foldl_map, ← List.sum_eq_foldl]

private theorem dot_add_right {m' : Nat} (u v w : Vector Rat m') :
    u.dotProduct (v + w) = u.dotProduct v + u.dotProduct w := by
  rw [dot_eq_sum, dot_eq_sum, dot_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.getElem_fin, Vector.getElem_add]
  ring

private theorem dot_comm {m' : Nat} (u v : Vector Rat m') :
    u.dotProduct v = v.dotProduct u := by
  rw [dot_eq_sum, dot_eq_sum]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem dot_prefixCombination (u : Vector Rat m)
    (C : Hex.Matrix Rat n n) (B : Hex.Matrix Rat n m) (i : Nat) (hi : i < n) :
    u.dotProduct (GramSchmidt.prefixCombination C B i hi) =
      ∑ k : Fin i,
        GramSchmidt.entry C ⟨i, hi⟩ ⟨k.val, Nat.lt_trans k.isLt hi⟩ *
          u.dotProduct (B.row ⟨k.val, Nat.lt_trans k.isLt hi⟩) := by
  rw [dot_eq_sum]
  have : ∀ l : Fin m,
      u[l] * (GramSchmidt.prefixCombination C B i hi)[l] =
        ∑ k : Fin i,
          GramSchmidt.entry C ⟨i, hi⟩ ⟨k.val, Nat.lt_trans k.isLt hi⟩ *
            ((B.row ⟨k.val, Nat.lt_trans k.isLt hi⟩)[l] * u[l]) := by
    intro l
    rw [getElem_prefixCombination, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dot_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Decomposition of a dot product against a cast input row through the
Gram-Schmidt basis: `⟨u, b_j⟩ = ⟨u, b*_j⟩ + Σ_{k<j} μ[j][k]·⟨u, b*_k⟩`. -/
private theorem dot_castRow_decompose (b : Hex.Matrix Int n m)
    (u : Vector Rat m) (j : Fin n) :
    u.dotProduct (castRow b j) =
      u.dotProduct ((GramSchmidt.Int.basis b).row j) +
        ∑ k : Fin j.val,
          muExact b j ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ *
            u.dotProduct
              ((GramSchmidt.Int.basis b).row ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩) := by
  have hdecomp := GramSchmidt.Int.basis_decomposition b j.val j.isLt
  have hrow : castRow b j = Vector.map (fun x : Int => (x : Rat)) (b.row ⟨j.val, j.isLt⟩) := by
    unfold castRow
    congr 1
  rw [hrow, hdecomp, dot_add_right, dot_prefixCombination]
  rfl

/-- The exact recurrence the interval pass evaluates: a Gram entry equals
the `⟨b_i, b*_j⟩` dot product plus the `μ[j][·]`-weighted prefix of the
`⟨b_i, b*_·⟩` dot products. -/
private theorem gram_recurrence (b : Hex.Matrix Int n m) (i j : Fin n) :
    (((b.row i).dotProduct (b.row j) : Int) : Rat) =
      gsDot b i j +
        ∑ k : Fin j.val,
          muExact b j ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ *
            gsDot b i ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ := by
  rw [gram_cast, dot_castRow_decompose]
  rfl

/-- `⟨b_i, b*_j⟩ = μ[i][j]·‖b*_j‖²` strictly below the diagonal. -/
private theorem gsDot_eq_mu_mul_nrm (b : Hex.Matrix Int n m) {i j : Fin n}
    (hji : j.val < i.val) :
    gsDot b i j = muExact b i j * nrm b j := by
  unfold gsDot
  rw [dot_comm, dot_castRow_decompose]
  have horth : ((GramSchmidt.Int.basis b).row j).dotProduct
      ((GramSchmidt.Int.basis b).row i) = 0 := by
    rw [dot_comm]
    exact GramSchmidt.Int.basis_orthogonal b i.val j.val i.isLt j.isLt
      (Nat.ne_of_gt hji)
  rw [horth, zero_add, Finset.sum_eq_single (⟨j.val, hji⟩ : Fin i.val)]
  · rw [dot_comm, nrm_eq_dot]
  · intro k _ hk
    have hkj : k.val ≠ j.val := fun h => hk (Fin.ext h)
    have horth' : ((GramSchmidt.Int.basis b).row j).dotProduct
        ((GramSchmidt.Int.basis b).row ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) = 0 := by
      rw [dot_comm]
      exact GramSchmidt.Int.basis_orthogonal b k.val j.val
        (Nat.lt_trans k.isLt i.isLt) j.isLt hkj
    rw [horth', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `⟨b_i, b*_i⟩ = ‖b*_i‖²` on the diagonal. -/
private theorem gsDot_self (b : Hex.Matrix Int n m) (i : Fin n) :
    gsDot b i i = nrm b i := by
  unfold gsDot
  rw [dot_comm, dot_castRow_decompose]
  have hsum : (∑ k : Fin i.val,
      muExact b i ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ *
        ((GramSchmidt.Int.basis b).row i).dotProduct
          ((GramSchmidt.Int.basis b).row ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have horth : ((GramSchmidt.Int.basis b).row i).dotProduct
        ((GramSchmidt.Int.basis b).row ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) = 0 :=
      GramSchmidt.Int.basis_orthogonal b i.val k.val i.isLt
        (Nat.lt_trans k.isLt i.isLt) (Nat.ne_of_gt k.isLt)
    rw [horth, mul_zero]
  rw [hsum, add_zero, dot_comm, nrm_eq_dot]

/-! ### Containment induction over the executable pass -/

private theorem getElem!_push_lt {α : Type*} [Inhabited α] (a : Array α) (x : α)
    {j : Nat} (hj : j < a.size) : (a.push x)[j]! = a[j]! := by
  have h1 : j < (a.push x).size := by
    rw [Array.size_push]
    omega
  rw [getElem!_pos (a.push x) j h1, getElem!_pos a j hj]
  exact Array.getElem_push_lt hj

private theorem getElem!_push_eq {α : Type*} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  have h1 : a.size < (a.push x).size := by
    rw [Array.size_push]
    omega
  rw [getElem!_pos (a.push x) a.size h1]
  exact Array.getElem_push_eq ..

private theorem getElem!_push_size_eq {α : Type*} [Inhabited α] (a : Array α)
    (x : α) {j : Nat} (hj : j = a.size) : (a.push x)[j]! = x := by
  subst hj
  exact getElem!_push_eq a x

/-- Containment for the sign-cased product bounds: the pair
`Ival.prodBounds a b` brackets the exact product `(x·S)·(y·S)` whenever the
inputs bracket `x·S` and `y·S`. -/
private theorem prodBounds_le {S : Int} {a b : Ival} {x y : Rat}
    (ha : a.mem S x) (hb : b.mem S y) :
    (((Ival.prodBounds a b).1 : Int) : Rat) ≤ (x * S) * (y * S) ∧
      (x * S) * (y * S) ≤ (((Ival.prodBounds a b).2 : Int) : Rat) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  unfold Ival.prodBounds
  by_cases hA : 0 ≤ a.lo
  · have hA' : (0 : Rat) ≤ (a.lo : Rat) := by exact_mod_cast hA
    have hx : (0 : Rat) ≤ x * S := le_trans hA' ha1
    by_cases hB : 0 ≤ b.lo
    · have hB' : (0 : Rat) ≤ (b.lo : Rat) := by exact_mod_cast hB
      have hy : (0 : Rat) ≤ y * S := le_trans hB' hb1
      rw [if_pos hA, if_pos hB]
      constructor <;> (push_cast; nlinarith)
    · rw [if_pos hA, if_neg hB]
      have hB' : (b.lo : Rat) < 0 := by exact_mod_cast not_le.mp hB
      by_cases hB2 : b.hi ≤ 0
      · have hB2' : (b.hi : Rat) ≤ 0 := by exact_mod_cast hB2
        have hy : y * S ≤ 0 := le_trans hb2 hB2'
        rw [if_pos hB2]
        constructor <;> (push_cast; nlinarith)
      · have hB2' : (0 : Rat) < (b.hi : Rat) := by exact_mod_cast not_le.mp hB2
        rw [if_neg hB2]
        constructor <;> (push_cast; nlinarith)
  · have hA' : (a.lo : Rat) < 0 := by exact_mod_cast not_le.mp hA
    rw [if_neg hA]
    by_cases hA2 : a.hi ≤ 0
    · have hA2' : (a.hi : Rat) ≤ 0 := by exact_mod_cast hA2
      have hx : x * S ≤ 0 := le_trans ha2 hA2'
      rw [if_pos hA2]
      by_cases hB : 0 ≤ b.lo
      · have hB' : (0 : Rat) ≤ (b.lo : Rat) := by exact_mod_cast hB
        have hy : (0 : Rat) ≤ y * S := le_trans hB' hb1
        rw [if_pos hB]
        constructor <;> (push_cast; nlinarith)
      · rw [if_neg hB]
        have hB' : (b.lo : Rat) < 0 := by exact_mod_cast not_le.mp hB
        by_cases hB2 : b.hi ≤ 0
        · have hB2' : (b.hi : Rat) ≤ 0 := by exact_mod_cast hB2
          have hy : y * S ≤ 0 := le_trans hb2 hB2'
          rw [if_pos hB2]
          constructor <;> (push_cast; nlinarith)
        · have hB2' : (0 : Rat) < (b.hi : Rat) := by exact_mod_cast not_le.mp hB2
          rw [if_neg hB2]
          constructor <;> (push_cast; nlinarith)
    · have hA2' : (0 : Rat) < (a.hi : Rat) := by exact_mod_cast not_le.mp hA2
      rw [if_neg hA2]
      by_cases hB : 0 ≤ b.lo
      · have hB' : (0 : Rat) ≤ (b.lo : Rat) := by exact_mod_cast hB
        have hy : (0 : Rat) ≤ y * S := le_trans hB' hb1
        rw [if_pos hB]
        constructor <;> (push_cast; nlinarith)
      · rw [if_neg hB]
        have hB' : (b.lo : Rat) < 0 := by exact_mod_cast not_le.mp hB
        by_cases hB2 : b.hi ≤ 0
        · have hB2' : (b.hi : Rat) ≤ 0 := by exact_mod_cast hB2
          have hy : y * S ≤ 0 := le_trans hb2 hB2'
          rw [if_pos hB2]
          constructor <;> (push_cast; nlinarith)
        · have hB2' : (0 : Rat) < (b.hi : Rat) := by exact_mod_cast not_le.mp hB2
          rw [if_neg hB2]
          -- both straddle zero: bound through the side picked by the sign
          -- of `x·S`
          constructor
          · show ((min (a.lo * b.hi) (a.hi * b.lo) : Int) : Rat) ≤ _
            have hcast : ((min (a.lo * b.hi) (a.hi * b.lo) : Int) : Rat) =
                min ((a.lo : Rat) * (b.hi : Rat)) ((a.hi : Rat) * (b.lo : Rat)) := by
              rcases le_total (a.lo * b.hi) (a.hi * b.lo) with h | h
              · rw [min_eq_left h]
                rw [min_eq_left (by exact_mod_cast h)]
                push_cast
                ring
              · rw [min_eq_right h]
                rw [min_eq_right (by exact_mod_cast h)]
                push_cast
                ring
            rw [hcast]
            rcases le_total 0 (x * (S : Rat)) with hx | hx
            · exact le_trans (min_le_right _ _) (by nlinarith)
            · exact le_trans (min_le_left _ _) (by nlinarith)
          · show _ ≤ ((max (a.lo * b.lo) (a.hi * b.hi) : Int) : Rat)
            have hcast : ((max (a.lo * b.lo) (a.hi * b.hi) : Int) : Rat) =
                max ((a.lo : Rat) * (b.lo : Rat)) ((a.hi : Rat) * (b.hi : Rat)) := by
              rcases le_total (a.lo * b.lo) (a.hi * b.hi) with h | h
              · rw [max_eq_right h]
                rw [max_eq_right (by exact_mod_cast h)]
                push_cast
                ring
              · rw [max_eq_left h]
                rw [max_eq_left (by exact_mod_cast h)]
                push_cast
                ring
            rw [hcast]
            rcases le_total 0 (x * (S : Rat)) with hx | hx
            · exact le_trans (by nlinarith :
                (x * S) * (y * S) ≤ (a.hi : Rat) * (b.hi : Rat)) (le_max_right _ _)
            · exact le_trans (by nlinarith :
                (x * S) * (y * S) ≤ (a.lo : Rat) * (b.lo : Rat)) (le_max_left _ _)

/-- The body of `IntervalGS.dotStep`'s exact scale-`S²` accumulation. -/
private def dotAccStep (muA rA : Array Ival) (acc : Int × Int) (k : Nat) :
    Int × Int :=
  let p := Ival.prodBounds muA[k]! rA[k]!
  (acc.1 - p.2, acc.2 - p.1)

/-- The scale-`S²` accumulator of `dotStep` encloses
`(g − Σ_{k<t} x_k·y_k)·S²` exactly (no rounding inside the fold). -/
private theorem dotAcc_bounds {S : Int}
    (muA rA : Array Ival) (g : Int) (t : Nat) (xs ys : Fin t → Rat)
    (hmu : ∀ k : Fin t, (muA[k.val]!).mem S (xs k))
    (hr : ∀ k : Fin t, (rA[k.val]!).mem S (ys k)) :
    let acc := (List.range t).foldl (dotAccStep muA rA) (g * S * S, g * S * S)
    ((acc.1 : Rat) ≤ ((g : Rat) - ∑ k, xs k * ys k) * S * S ∧
      ((g : Rat) - ∑ k, xs k * ys k) * S * S ≤ (acc.2 : Rat)) := by
  induction t with
  | zero =>
      refine ⟨?_, ?_⟩ <;> simp
  | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun k => xs k.castSucc) (fun k => ys k.castSucc)
        (fun k => hmu k.castSucc) (fun k => hr k.castSucc)
      obtain ⟨hp1, hp2⟩ := prodBounds_le (hmu (Fin.last t)) (hr (Fin.last t))
      rw [show (List.range (t + 1)).foldl (dotAccStep muA rA) (g * S * S, g * S * S) =
          dotAccStep muA rA
            ((List.range t).foldl (dotAccStep muA rA) (g * S * S, g * S * S)) t from by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]]
      rw [Fin.sum_univ_castSucc]
      unfold dotAccStep
      set acc := (List.range t).foldl (dotAccStep muA rA) (g * S * S, g * S * S)
      have hterm : (xs (Fin.last t) * S) * (ys (Fin.last t) * S) =
          xs (Fin.last t) * ys (Fin.last t) * S * S := by ring
      rw [hterm] at hp1 hp2
      constructor
      · push_cast
        have heq : ((g : Rat) - (∑ k : Fin t, xs k.castSucc * ys k.castSucc +
            xs (Fin.last t) * ys (Fin.last t))) * S * S =
            ((g : Rat) - ∑ k : Fin t, xs k.castSucc * ys k.castSucc) * S * S -
              xs (Fin.last t) * ys (Fin.last t) * S * S := by ring
        rw [heq]
        exact sub_le_sub ih1 hp2
      · push_cast
        have heq : ((g : Rat) - (∑ k : Fin t, xs k.castSucc * ys k.castSucc +
            xs (Fin.last t) * ys (Fin.last t))) * S * S =
            ((g : Rat) - ∑ k : Fin t, xs k.castSucc * ys k.castSucc) * S * S -
              xs (Fin.last t) * ys (Fin.last t) * S * S := by ring
        rw [heq]
        exact sub_le_sub ih2 hp1

private theorem dotStep_mem {S : Int} (hS : 0 < S)
    (muA rA : Array Ival) (g : Int) (t : Nat) (xs ys : Fin t → Rat)
    (hmu : ∀ k : Fin t, (muA[k.val]!).mem S (xs k))
    (hr : ∀ k : Fin t, (rA[k.val]!).mem S (ys k)) :
    (IntervalGS.dotStep S muA rA g t).mem S ((g : Rat) - ∑ k, xs k * ys k) := by
  have hSQ : (0 : Rat) < (S : Rat) := by exact_mod_cast hS
  obtain ⟨h1, h2⟩ := dotAcc_bounds muA rA g t xs ys hmu hr
  have hfold : IntervalGS.dotStep S muA rA g t =
      ⟨Int.fdiv ((List.range t).foldl (dotAccStep muA rA) (g * S * S, g * S * S)).1 S,
        Ival.cdiv ((List.range t).foldl (dotAccStep muA rA) (g * S * S, g * S * S)).2 S⟩ := by
    unfold IntervalGS.dotStep dotAccStep
    rfl
  rw [hfold]
  set acc := (List.range t).foldl (dotAccStep muA rA) (g * S * S, g * S * S)
  set V : Rat := (g : Rat) - ∑ k, xs k * ys k
  constructor
  · -- fdiv acc.1 S ≤ V·S
    have hd : ((acc.1 : Rat)) / (S : Rat) ≤ V * S := by
      rw [div_le_iff₀ hSQ]
      calc (acc.1 : Rat) ≤ V * S * S := h1
        _ = V * S * S := rfl
    exact le_trans (intCast_fdiv_le _ hS) hd
  · -- V·S ≤ cdiv acc.2 S
    have hd : V * S ≤ ((acc.2 : Rat)) / (S : Rat) := by
      rw [le_div_iff₀ hSQ]
      exact h2
    exact le_trans hd (div_le_intCast_cdiv _ hS)

/-- Invariant carried by the pass across the first `t` rows: sizes are `t`,
every `‖b*_j‖²` enclosure is strictly positive and contains the exact
value, and every `μ[j][k]` enclosure contains the exact coefficient. -/
private def Inv (b : Hex.Matrix Int n m) (S : Int) (t : Nat) (ht : t ≤ n)
    (mus : Array (Array Ival)) (bstars : Array Ival) : Prop :=
  mus.size = t ∧ bstars.size = t ∧
    ∀ j (hj : j < t),
      0 < (bstars[j]!).lo ∧
        (bstars[j]!).mem S (nrm b ⟨j, Nat.lt_of_lt_of_le hj ht⟩) ∧
        ∀ k (hk : k < j),
          ((mus[j]!)[k]!).mem S
            (muExact b ⟨j, Nat.lt_of_lt_of_le hj ht⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_of_lt_of_le hj ht)⟩)

private theorem pos_of_mem_pos_lo {S : Int} (hS : 0 < S) {I : Ival} {x : Rat}
    (hmem : I.mem S x) (hlo : 0 < I.lo) : 0 < x := by
  obtain ⟨h1, _⟩ := hmem
  have hSQ : (0 : Rat) < (S : Rat) := by exact_mod_cast hS
  have hloQ : (0 : Rat) < (I.lo : Rat) := by exact_mod_cast hlo
  nlinarith

/-- The accumulated `r` and `μ` rows of the inner fold enclose the exact
`⟨b_i, b*_·⟩` dot products and Gram-Schmidt coefficients of row `i`. -/
private theorem rowFold_spec (b : Hex.Matrix Int n m) {S : Int} (hS : 0 < S)
    (gRow : Array Int) (mus : Array (Array Ival)) (bstars : Array Ival)
    (i : Fin n) (hinv : Inv b S i.val (Nat.le_of_lt i.isLt) mus bstars)
    (hgRow : ∀ j (hj : j ≤ i.val),
      gRow[j]! = (b.row i).dotProduct
        (b.row ⟨j, Nat.lt_of_le_of_lt hj i.isLt⟩))
    (t : Nat) (ht : t ≤ i.val) :
    ((List.range t).foldl (IntervalGS.rowStep S gRow mus bstars) (#[], #[])).1.size = t ∧
      ((List.range t).foldl (IntervalGS.rowStep S gRow mus bstars) (#[], #[])).2.size = t ∧
      ∀ j (hj : j < t),
        ((((List.range t).foldl (IntervalGS.rowStep S gRow mus bstars)
              (#[], #[])).1)[j]!).mem S
            (gsDot b i ⟨j, Nat.lt_trans (Nat.lt_of_lt_of_le hj ht) i.isLt⟩) ∧
          ((((List.range t).foldl (IntervalGS.rowStep S gRow mus bstars)
              (#[], #[])).2)[j]!).mem S
            (muExact b i ⟨j, Nat.lt_trans (Nat.lt_of_lt_of_le hj ht) i.isLt⟩) := by
  induction t with
  | zero =>
      exact ⟨rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ t ih =>
      have ht' : t ≤ i.val := Nat.le_of_succ_le ht
      obtain ⟨hsz1, hsz2, hprev⟩ := ih ht'
      have hfold : (List.range (t + 1)).foldl (IntervalGS.rowStep S gRow mus bstars)
            (#[], #[]) =
          IntervalGS.rowStep S gRow mus bstars
            ((List.range t).foldl (IntervalGS.rowStep S gRow mus bstars) (#[], #[])) t := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set acc := (List.range t).foldl (IntervalGS.rowStep S gRow mus bstars) (#[], #[])
        with hacc
      have htlt : t < i.val := Nat.lt_of_succ_le ht
      have htn : t < n := Nat.lt_trans htlt i.isLt
      obtain ⟨hszm, hszb, hrows⟩ := hinv
      obtain ⟨hblo, hbmem, hmmem⟩ := hrows t htlt
      -- the fresh r entry encloses ⟨b_i, b*_t⟩
      have hrec := gram_recurrence b i ⟨t, htn⟩
      have hrmem : (IntervalGS.dotStep S mus[t]! acc.1 gRow[t]! t).mem S
          (gsDot b i ⟨t, htn⟩) := by
        have hds := dotStep_mem hS mus[t]! acc.1 gRow[t]! t
          (fun k : Fin t => muExact b ⟨t, htn⟩ ⟨k.val, Nat.lt_trans k.isLt htn⟩)
          (fun k : Fin t => gsDot b i ⟨k.val, Nat.lt_trans k.isLt htn⟩)
          (fun k => hmmem k.val k.isLt)
          (fun k => (hprev k.val k.isLt).1)
        have heq : (gRow[t]! : Rat) -
            (∑ k : Fin t, muExact b ⟨t, htn⟩ ⟨k.val, Nat.lt_trans k.isLt htn⟩ *
              gsDot b i ⟨k.val, Nat.lt_trans k.isLt htn⟩) = gsDot b i ⟨t, htn⟩ := by
          rw [hgRow t (Nat.le_of_lt htlt), hrec]
          ring
        rw [← heq]
        exact hds
      -- the fresh μ entry encloses μ[i][t]
      have hnrm_pos : 0 < nrm b ⟨t, htn⟩ := pos_of_mem_pos_lo hS hbmem hblo
      have hmumem : (Ival.divPos S (IntervalGS.dotStep S mus[t]! acc.1 gRow[t]! t)
          (bstars[t]!)).mem S (muExact b i ⟨t, htn⟩) := by
        have hdv := mem_divPos hS hrmem hbmem hblo
        have heq : gsDot b i ⟨t, htn⟩ / nrm b ⟨t, htn⟩ = muExact b i ⟨t, htn⟩ := by
          rw [gsDot_eq_mu_mul_nrm b htlt]
          exact mul_div_cancel_right₀ _ (ne_of_gt hnrm_pos)
        rw [← heq]
        exact hdv
      rw [hfold]
      unfold IntervalGS.rowStep
      dsimp only
      refine ⟨by simp [Array.size_push, hsz1], by simp [Array.size_push, hsz2], ?_⟩
      intro j hj
      rcases Nat.lt_or_ge j t with hjt | hjt
      · have hj1 : j < acc.1.size := by omega
        have hj2 : j < acc.2.size := by omega
        rw [getElem!_push_lt _ _ hj1, getElem!_push_lt _ _ hj2]
        exact hprev j hjt
      · have hjeq : j = t := by omega
        subst hjeq
        constructor
        · rw [getElem!_push_size_eq _ _ (by omega : j = acc.1.size)]
          exact hrmem
        · rw [getElem!_push_size_eq _ _ (by omega : j = acc.2.size)]
          exact hmumem

/-- The `μ` row and `‖b*_i‖²` enclosure produced by `IntervalGS.row` contain
the exact values, given the invariant for all earlier rows. -/
private theorem row_spec (b : Hex.Matrix Int n m) {S : Int} (hS : 0 < S)
    (gRow : Array Int) (mus : Array (Array Ival)) (bstars : Array Ival)
    (i : Fin n) (hinv : Inv b S i.val (Nat.le_of_lt i.isLt) mus bstars)
    (hgRow : ∀ j (hj : j ≤ i.val),
      gRow[j]! = (b.row i).dotProduct
        (b.row ⟨j, Nat.lt_of_le_of_lt hj i.isLt⟩)) :
    (IntervalGS.row S gRow mus bstars i.val).1.size = i.val ∧
      (∀ j (hj : j < i.val),
        (((IntervalGS.row S gRow mus bstars i.val).1)[j]!).mem S
          (muExact b i ⟨j, Nat.lt_trans hj i.isLt⟩)) ∧
      ((IntervalGS.row S gRow mus bstars i.val).2).mem S (nrm b i) := by
  obtain ⟨hsz1, hsz2, hentries⟩ :=
    rowFold_spec b hS gRow mus bstars i hinv hgRow i.val (Nat.le_refl i.val)
  set acc := (List.range i.val).foldl (IntervalGS.rowStep S gRow mus bstars) (#[], #[])
    with hacc
  have hrow : IntervalGS.row S gRow mus bstars i.val =
      (acc.2, IntervalGS.dotStep S acc.2 acc.1 gRow[i.val]! i.val) := by
    unfold IntervalGS.row
    rfl
  rw [hrow]
  refine ⟨hsz2, fun j hj => (hentries j hj).2, ?_⟩
  have hds := dotStep_mem hS acc.2 acc.1 gRow[i.val]! i.val
    (fun k : Fin i.val => muExact b i ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩)
    (fun k : Fin i.val => gsDot b i ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩)
    (fun k => (hentries k.val k.isLt).2)
    (fun k => (hentries k.val k.isLt).1)
  have hrec := gram_recurrence b i i
  have heq : (gRow[i.val]! : Rat) -
      (∑ k : Fin i.val, muExact b i ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ *
        gsDot b i ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) = nrm b i := by
    rw [hgRow i.val (Nat.le_refl i.val)]
    rw [show (⟨i.val, Nat.lt_of_le_of_lt (Nat.le_refl i.val) i.isLt⟩ : Fin n) = i from
      Fin.ext rfl]
    rw [hrec, ← gsDot_self b i]
    ring
  rw [← heq]
  exact hds

/-- Acceptance invariant of the full pass. -/
private theorem pass_spec (b : Hex.Matrix Int n m) {S : Int} (hS : 0 < S)
    (g : Array (Array Int))
    (hg : ∀ i (hi : i < n) j (hj : j ≤ i),
      (g[i]!)[j]! = (b.row ⟨i, hi⟩).dotProduct
        (b.row ⟨j, Nat.lt_of_le_of_lt hj hi⟩)) :
    ∀ t (ht : t ≤ n) (res : Array (Array Ival) × Array Ival),
      (List.range t).foldlM (IntervalGS.passStep S g) (#[], #[]) = some res →
      Inv b S t ht res.1 res.2 := by
  intro t
  induction t with
  | zero =>
      intro ht res hres
      simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq]
        at hres
      rw [← hres]
      exact ⟨rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ t ih =>
      intro ht res hres
      rw [List.range_succ, List.foldlM_append] at hres
      obtain ⟨s, hs, hstep⟩ := Option.bind_eq_some_iff.mp hres
      simp only [List.foldlM_cons, List.foldlM_nil] at hstep
      obtain ⟨s', hs', hpure⟩ := Option.bind_eq_some_iff.mp hstep
      have hres' : IntervalGS.passStep S g s t = some res := by
        cases hpure
        exact hs'
      have hinv_t := ih (Nat.le_of_succ_le ht) s hs
      have htn : t < n := Nat.lt_of_succ_le ht
      let iF : Fin n := ⟨t, htn⟩
      have hgRow : ∀ j (hj : j ≤ iF.val),
          (g[t]!)[j]! = (b.row iF).dotProduct
            (b.row ⟨j, Nat.lt_of_le_of_lt hj iF.isLt⟩) := fun j hj => hg t htn j hj
      obtain ⟨hrsz, hrmu, hrb⟩ := row_spec b hS g[t]! s.1 s.2 iF hinv_t hgRow
      -- unfold the step and the positivity test
      unfold IntervalGS.passStep at hres'
      set rowRes := IntervalGS.row S g[t]! s.1 s.2 t with hrowRes
      obtain ⟨hsz1, hsz2, hinvrows⟩ := hinv_t
      by_cases hpos : 0 < rowRes.2.lo
      · rw [if_pos hpos] at hres'
        have hres'' : res = (s.1.push rowRes.1, s.2.push rowRes.2) :=
          (Option.some.injEq _ _ ▸ hres').symm
        subst hres''
        dsimp only
        refine ⟨by simp [Array.size_push, hsz1], by simp [Array.size_push, hsz2], ?_⟩
        intro j hj
        rcases Nat.lt_or_ge j t with hjt | hjt
        · have hj1 : j < s.1.size := by omega
          have hj2 : j < s.2.size := by omega
          rw [getElem!_push_lt _ _ hj1, getElem!_push_lt _ _ hj2]
          exact hinvrows j hjt
        · have hjeq : j = t := by omega
          subst hjeq
          rw [getElem!_push_size_eq _ _ (by omega : j = s.2.size),
            getElem!_push_size_eq _ _ (by omega : j = s.1.size)]
          exact ⟨hpos, hrb, fun k hk => hrmu k hk⟩
      · rw [if_neg hpos] at hres'
        cases hres'

/-! ### Glue: the Gram array fed to the pass -/

private theorem g_entries (b : Hex.Matrix Int n m) (i : Nat) (hi : i < n)
    (j : Nat) (hj : j < n) :
    ((((Matrix.gramMatrix b).toArray.map Vector.toArray))[i]!)[j]! =
      (b.row ⟨i, hi⟩).dotProduct (b.row ⟨j, hj⟩) := by
  have hi1 : i < ((Matrix.gramMatrix b).toArray.map Vector.toArray).size := by
    rw [Array.size_map, Vector.size_toArray]
    exact hi
  have hi2 : i < (Matrix.gramMatrix b).toArray.size := by
    rw [Vector.size_toArray]
    exact hi
  rw [getElem!_pos ((Matrix.gramMatrix b).toArray.map Vector.toArray) i hi1,
    Array.getElem_map]
  have hj1 : j < ((Matrix.gramMatrix b).toArray[i]'hi2).toArray.size := by
    rw [Vector.size_toArray]
    exact hj
  rw [getElem!_pos (((Matrix.gramMatrix b).toArray[i]'hi2).toArray) j hj1]
  simp only [Vector.getElem_toArray]
  simpa using Hex.Matrix.getElem_gramMatrix b ⟨i, hi⟩ ⟨j, hj⟩

/-! ### Positivity of the Gram-determinant product -/

private theorem normProduct_pos (b : Hex.Matrix Int n m)
    (hpos : ∀ j : Fin n, 0 < nrm b j) :
    ∀ t (ht : t ≤ n), 0 < GramSchmidt.Int.gramSchmidtNormProduct b t ht := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp [GramSchmidt.Int.gramSchmidtNormProduct]
  | succ t ih =>
      intro ht
      rw [GramSchmidt.Int.gramSchmidtNormProduct_succ b t ht]
      exact mul_pos (ih (Nat.le_of_succ_le ht)) (hpos ⟨t, Nat.lt_of_succ_le ht⟩)

private theorem independent_of_nrm_pos (b : Hex.Matrix Int n m)
    (hpos : ∀ j : Fin n, 0 < nrm b j) :
    Hex.Matrix.independent b := by
  unfold Hex.Matrix.independent GramSchmidt.Int.independent
  intro k
  have h := GramSchmidt.Int.gramDet_eq_prod_normSq_uncond b (k.val + 1)
    (Nat.succ_le_of_lt k.isLt)
  have hp := normProduct_pos b hpos (k.val + 1) (Nat.succ_le_of_lt k.isLt)
  rw [← h] at hp
  exact_mod_cast hp

/-! ### Soundness of the interval reducedness checker -/

/-- Acceptance by the fixed-precision interval checker entails the exact
rational reducedness predicate and independence. This is the trusted
statement consumed by `lllReducedCheck_sound` / `certCheck_sound`; the
exact-integer fallback path is covered by `lllReducedInt_sound`. -/
theorem lllReducedInterval_sound (b : Hex.Matrix Int n m) (δ η : Rat) :
    Hex.lllReducedInterval b δ η = true →
      Hex.isLLLReduced b δ η ∧ Hex.Matrix.independent b := by
  intro h
  have hS : (0 : Int) < (2 : Int) ^ Hex.Internal.intervalPrec := pow_pos (by norm_num) _
  have hSQ : (0 : Rat) < (((2 : Int) ^ Hex.Internal.intervalPrec : Int) : Rat) := by
    exact_mod_cast hS
  simp only [Hex.lllReducedInterval] at h
  set S : Int := (2 : Int) ^ Hex.Internal.intervalPrec with hSdef
  set g : Array (Array Int) := (Matrix.gramMatrix b).toArray.map Vector.toArray
    with hgdef
  rcases hpass : IntervalGS.pass S g n with _ | ⟨mus, bstars⟩
  · rw [hpass] at h
    cases h
  rw [hpass] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hsizeOK, hlovOK⟩ := h
  have hg : ∀ i (hi : i < n) j (hj : j ≤ i),
      (g[i]!)[j]! = (b.row ⟨i, hi⟩).dotProduct
        (b.row ⟨j, Nat.lt_of_le_of_lt hj hi⟩) :=
    fun i hi j hj => g_entries b i hi j (Nat.lt_of_le_of_lt hj hi)
  have hinv : Inv b S n (Nat.le_refl n) mus bstars :=
    pass_spec b hS g hg n (Nat.le_refl n) (mus, bstars) hpass
  obtain ⟨hszm, hszb, hrows⟩ := hinv
  have hnrm_pos : ∀ j : Fin n, 0 < nrm b j := by
    intro j
    obtain ⟨hblo, hbmem, _⟩ := hrows j.val j.isLt
    exact pos_of_mem_pos_lo hS hbmem hblo
  -- unpack the two Bool clauses
  unfold IntervalGS.sizeOK at hsizeOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    at hsizeOK
  unfold IntervalGS.lovaszOK at hlovOK
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hlovOK
  refine ⟨⟨?_, ?_⟩, independent_of_nrm_pos b hnrm_pos⟩
  · -- size-reduced clause
    intro i j hi hji
    obtain ⟨hhiB, hloB⟩ := hsizeOK i hi j hji
    obtain ⟨_, _, hmus⟩ := hrows i hi
    have hmem := hmus j hji
    obtain ⟨hmlo, hmhi⟩ := hmem
    have hden : (0 : Rat) < (η.den : Rat) := by exact_mod_cast η.den_pos
    set μv : Rat := muExact b ⟨i, hi⟩ ⟨j, Nat.lt_trans hji hi⟩ with hμv
    have hhiQ : ((((mus[i]!)[j]!).hi : Rat)) * (η.den : Rat) ≤
        (η.num : Rat) * ((S : Int) : Rat) := by exact_mod_cast hhiB
    have hloQ : -((η.num : Rat) * ((S : Int) : Rat)) ≤
        ((((mus[i]!)[j]!).lo : Rat)) * (η.den : Rat) := by exact_mod_cast hloB
    have hηden : η * (η.den : Rat) = (η.num : Rat) := by
      have h := Rat.num_div_den η
      field_simp at h
      linarith
    have hub : μv ≤ η := by
      have h1 : μv * (η.den : Rat) * ((S : Int) : Rat) ≤
          (η.num : Rat) * ((S : Int) : Rat) := by nlinarith
      have h2 : μv * (η.den : Rat) ≤ (η.num : Rat) :=
        le_of_mul_le_mul_right h1 hSQ
      have h3 : μv * (η.den : Rat) ≤ η * (η.den : Rat) := by
        rw [hηden]
        exact h2
      exact le_of_mul_le_mul_right h3 hden
    have hlb : -η ≤ μv := by
      have h1 : -(η.num : Rat) * ((S : Int) : Rat) ≤
          μv * (η.den : Rat) * ((S : Int) : Rat) := by nlinarith
      have h2 : -(η.num : Rat) ≤ μv * (η.den : Rat) :=
        le_of_mul_le_mul_right h1 hSQ
      have h3 : (-η) * (η.den : Rat) ≤ μv * (η.den : Rat) := by
        rw [neg_mul, hηden]
        exact h2
      exact le_of_mul_le_mul_right h3 hden
    show μv * μv ≤ η * η
    nlinarith
  · -- Lovász clause
    intro i hi
    have hi' : i < n - 1 := by omega
    have hcmp := hlovOK i hi'
    have hi1n : i + 1 < n := hi
    have hin : i < n := Nat.lt_trans (Nat.lt_succ_self i) hi
    obtain ⟨hblo_i, hbmem_i, _⟩ := hrows i hin
    obtain ⟨hblo_i1, hbmem_i1, hmus_i1⟩ := hrows (i + 1) hi1n
    have hμmem := hmus_i1 i (Nat.lt_succ_self i)
    have hδmem := mem_ofRat hS δ
    have hlhs := mem_mul hS hδmem hbmem_i
    have hrhs := mem_add hbmem_i1 (mem_mul hS (mem_mul hS hμmem hμmem) hbmem_i)
    obtain ⟨_, hlhs_hi⟩ := hlhs
    obtain ⟨hrhs_lo, _⟩ := hrhs
    have hQ : (((Ival.mul S (Ival.ofRat S δ) (bstars[i]!)).hi : Int) : Rat) ≤
        (((((bstars[i + 1]!).add (Ival.mul S (Ival.mul S ((mus[i+1]!)[i]!)
          ((mus[i+1]!)[i]!)) (bstars[i]!)))).lo : Int) : Rat) := by
      exact_mod_cast hcmp
    have hchain := le_trans hlhs_hi (le_trans hQ hrhs_lo)
    show δ * Hex.Internal.LLLCore.basisNormSq (GramSchmidt.Int.basis b)
          ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ ≤
        Hex.Internal.LLLCore.basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ +
          ((GramSchmidt.Int.coeffs b)[(⟨i + 1, hi⟩ : Fin n)][(⟨i,
            Nat.lt_trans (Nat.lt_succ_self i) hi⟩ : Fin n)]) *
          ((GramSchmidt.Int.coeffs b)[(⟨i + 1, hi⟩ : Fin n)][(⟨i,
            Nat.lt_trans (Nat.lt_succ_self i) hi⟩ : Fin n)]) *
          Hex.Internal.LLLCore.basisNormSq (GramSchmidt.Int.basis b)
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    have := (mul_le_mul_iff_of_pos_right hSQ).mp hchain
    exact this

end HexLLLMathlib
