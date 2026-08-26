/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Exact

public section

/-!
# Semantics of lazy and canonical arithmetic

Each checked lazy operation has a soundness theorem and a bounded-search
completeness theorem. These imply the corresponding theorem for the total
fallback wrapper, and exactification transfers it to canonical algebraic
numbers.
-/

namespace Hex

noncomputable section

section

/-- Proof-local Mathlib `CommRing` view of `ZPoly`, assembled from the
executable library's verified `Lean.Grind.CommRing` instance. -/
@[implicit_reducible] local instance : CommRing ZPoly :=
  let s := (inferInstance : Lean.Grind.CommRing ZPoly)
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one,
        Lean.Grind.Semiring.natCast_succ] }

/-- Proof-local domain structure on `ZPoly`, transported from
`Polynomial Int`. -/
local instance : IsDomain ZPoly :=
  MulEquiv.isDomain (Polynomial Int)
    (HexPolyMathlib.equiv (R := Int)).toMulEquiv

private noncomputable def evalZPoly (t : ℂ) : ZPoly →+* ℂ :=
  (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
    (HexPolyMathlib.equiv (R := Int)).toRingHom

private theorem ZPoly.map_liftOuter (p : ZPoly) (t : ℂ) :
    (HexPolyMathlib.toPolynomial p.liftOuter).map (evalZPoly t) =
      HexRootsMathlib.toPolyℂ p := by
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    ZPoly.coeff_liftOuter, HexRootsMathlib.coeff_toPolyℂ]
  change Polynomial.eval₂ (Int.castRingHom ℂ) t
      (HexPolyMathlib.toPolynomial (DensePoly.C (p.coeff n))) =
    (p.coeff n : ℂ)
  rw [HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
  rfl

/-- Specialization of the coefficient variable commutes with the constant
bivariate lift. -/
theorem ZPoly.map_liftOuterAt (p : ZPoly) (t : ℂ) :
    (HexPolyMathlib.toPolynomial p.liftOuter).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom) =
      HexRootsMathlib.toPolyℂ p :=
  map_liftOuter p t

/-- Specializing the coefficient variable of the constant bivariate lift
recovers the original complex polynomial. -/
theorem ZPoly.eval_liftOuter (p : ZPoly) (t y : ℂ) :
    ((HexPolyMathlib.toPolynomial p.liftOuter).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y =
      (HexRootsMathlib.toPolyℂ p).eval y := by
  have hmap := map_liftOuterAt p t
  exact congrArg (fun q : Polynomial ℂ => q.eval y) hmap

/-- The constant bivariate lift preserves the degree of the source integer
polynomial. -/
theorem ZPoly.natDegree_liftOuter (p : ZPoly) :
    (HexPolyMathlib.toPolynomial p.liftOuter).natDegree =
      p.degree?.getD 0 := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases hp : p.size = 0
  · have hlift : p.liftOuter.size = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold ZPoly.liftOuter
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp [hp])
    rw [(DensePoly.degree?_eq_none_iff p.liftOuter).2 hlift,
      (DensePoly.degree?_eq_none_iff p).2 hp]
  · have hppos : 0 < p.size := Nat.pos_of_ne_zero hp
    have hliftLe : p.liftOuter.size ≤ p.size := by
      unfold ZPoly.liftOuter
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    have hcoeff : p.liftOuter.coeff (p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun q : ZPoly => q.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size p hppos hconst
    have hliftGe : p.size ≤ p.liftOuter.size := by
      by_contra h
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    have hsize : p.liftOuter.size = p.size := Nat.le_antisymm hliftLe hliftGe
    rw [DensePoly.degree?_eq_some_of_pos_size p hppos,
      DensePoly.degree?_eq_some_of_pos_size p.liftOuter (by omega),
      Option.getD_some, Option.getD_some, hsize]

private theorem ZPoly.coeff_mulSubstitute (q : ZPoly) (j : Nat) :
    q.mulSubstitute.coeff j =
      if j ≤ q.degree?.getD 0 then
        DensePoly.monomial (q.degree?.getD 0 - j)
          (q.coeff (q.degree?.getD 0 - j))
      else 0 := by
  unfold ZPoly.mulSubstitute
  change (DensePoly.ofList ((List.range (q.degree?.getD 0 + 1)).map fun j =>
      DensePoly.monomial (q.degree?.getD 0 - j)
        (q.coeff (q.degree?.getD 0 - j)))).coeff j = _
  rw [DensePoly.coeff_ofList,
    HexPolyMathlib.list_getD_map_range_zero]
  split <;> rename_i h
  · rw [if_pos (by omega)]
  · rw [if_neg (by omega)]
    rfl

private theorem evalZPoly_X (t : ℂ) : evalZPoly t ZPoly.X = t := by
  simp [evalZPoly, ZPoly.X, HexPolyMathlib.equiv_apply,
    HexPolyMathlib.toPolynomial_monomial,
    Polynomial.monomial_one_one_eq_X]

private theorem evalZPoly_monomial (t : ℂ) (n : Nat) (c : Int) :
    evalZPoly t (DensePoly.monomial n c) = (c : ℂ) * t ^ n := by
  simp [evalZPoly, HexPolyMathlib.equiv_apply,
    HexPolyMathlib.toPolynomial_monomial]

private theorem ZPoly.map_mulSubstitute (q : ZPoly) (t : ℂ) :
    (HexPolyMathlib.toPolynomial q.mulSubstitute).map (evalZPoly t) =
      ∑ j ∈ Finset.range (q.degree?.getD 0 + 1),
        Polynomial.monomial j
          ((q.coeff (q.degree?.getD 0 - j) : ℂ) *
            t ^ (q.degree?.getD 0 - j)) := by
  ext j
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    ZPoly.coeff_mulSubstitute]
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  by_cases hj : j ≤ q.degree?.getD 0
  · rw [if_pos hj, evalZPoly_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      exact Polynomial.coeff_monomial_of_ne
        ((q.coeff (q.degree?.getD 0 - b) : ℂ) *
          t ^ (q.degree?.getD 0 - b)) hbj.symm
    · simp [hj]
  · rw [if_neg hj, map_zero]
    symm
    exact Finset.sum_eq_zero
      (s := Finset.range (q.degree?.getD 0 + 1)) fun b hb =>
      Polynomial.coeff_monomial_of_ne
        ((q.coeff (q.degree?.getD 0 - b) : ℂ) *
          t ^ (q.degree?.getD 0 - b)) (by
        have hbLe : b ≤ q.degree?.getD 0 := by simpa using hb
        omega)

private theorem ZPoly.eval_map_mulSubstitute (q : ZPoly) (t y : ℂ)
    (hy : y ≠ 0) :
    ((HexPolyMathlib.toPolynomial q.mulSubstitute).map
      (evalZPoly t)).eval y =
      y ^ q.degree?.getD 0 *
        (HexRootsMathlib.toPolyℂ q).eval (t / y) := by
  rw [ZPoly.map_mulSubstitute, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_monomial]
  rw [Polynomial.eval_eq_sum_range,
    HexRootsMathlib.natDegree_toPolyℂ, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ q.degree?.getD 0 := by simpa using hj
  rw [HexRootsMathlib.coeff_toPolyℂ, div_pow]
  field_simp
  have hidx : q.degree?.getD 0 + 1 - 1 - j =
      q.degree?.getD 0 - j := by omega
  rw [hidx]
  have hpow : y ^ j * y ^ (q.degree?.getD 0 - j) =
      y ^ q.degree?.getD 0 := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_assoc, hpow]
  ring

private theorem ZPoly.natDegree_map_mulSubstitute (q : ZPoly) (hq : q ≠ 0)
    (t : ℂ) (ht : t ≠ 0) :
    ((HexPolyMathlib.toPolynomial q.mulSubstitute).map
      (evalZPoly t)).natDegree =
      (HexPolyMathlib.toPolynomial q.mulSubstitute).natDegree := by
  let g := q.mulSubstitute
  have hqpos : 0 < q.size := by
    by_contra h
    exact hq ((DensePoly.size_eq_zero_iff q).mp (by omega))
  have hn : q.degree?.getD 0 = q.size - 1 := by
    rw [DensePoly.degree?_eq_some_of_pos_size q hqpos, Option.getD_some]
  have hqtop : q.coeff (q.degree?.getD 0) ≠ (Zero.zero : Int) := by
    simpa [hn] using DensePoly.coeff_last_ne_zero_of_pos_size q hqpos
  have hgcoeff0 : g.coeff 0 =
      DensePoly.monomial (q.degree?.getD 0)
        (q.coeff (q.degree?.getD 0)) := by
    dsimp only [g]
    rw [ZPoly.coeff_mulSubstitute, if_pos (Nat.zero_le _), Nat.sub_zero]
  have hgcoeff0ne : g.coeff 0 ≠ 0 := by
    rw [hgcoeff0]
    exact DensePoly.monomial_ne_zero_of_ne_zero hqtop
  have hgpos : 0 < g.size := by
    by_contra h
    exact hgcoeff0ne (DensePoly.coeff_eq_zero_of_size_le g (by omega))
  have hgsize : g.size ≤ q.degree?.getD 0 + 1 := by
    dsimp only [g]
    unfold ZPoly.mulSubstitute
    exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
  have hdle : g.size - 1 ≤ q.degree?.getD 0 := by omega
  have hgLast : g.coeff (g.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size g hgpos
  have hcoeff : q.coeff (q.degree?.getD 0 - (g.size - 1)) ≠ 0 := by
    intro hzero
    apply hgLast
    dsimp only [g]
    rw [ZPoly.coeff_mulSubstitute, if_pos hdle, hzero]
    simp
  apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
  rw [HexPolyMathlib.leadingCoeff_toPolynomial,
    DensePoly.leadingCoeff_eq_coeff_last g hgpos]
  dsimp only [g]
  rw [ZPoly.coeff_mulSubstitute, if_pos hdle, evalZPoly_monomial]
  have htPow :
      t ^ (q.degree?.getD 0 - (g.size - 1)) ≠ 0 :=
    _root_.pow_ne_zero _ ht
  exact mul_ne_zero (by exact_mod_cast hcoeff) htPow

private theorem ZPoly.removeX_eq_ofList_dropWhile (p : ZPoly) :
    p.removeX = DensePoly.ofList (p.toList.dropWhile (· == 0)) := by
  unfold ZPoly.removeX DensePoly.toList DensePoly.ofList
  apply congrArg DensePoly.ofCoeffs
  have h := congrArg Array.reverse
    (List.popWhile_toArray (fun x : Int => x == 0)
      p.toArray.toList.reverse)
  have hreverse : p.toArray.toList.reverse.toArray = p.toArray.reverse := by
    rw [← List.reverse_toArray, Array.toArray_toList]
  rw [hreverse] at h
  simpa only [List.reverse_toArray, List.reverse_reverse,
    Array.toArray_toList, Array.reverse_reverse] using h

private theorem toPolynomial_ofList_zero_cons (l : List Int) :
    HexPolyMathlib.toPolynomial (DensePoly.ofList (0 :: l)) =
      Polynomial.X * HexPolyMathlib.toPolynomial (DensePoly.ofList l) := by
  ext n
  cases n with
  | zero =>
      simp [HexPolyMathlib.coeff_toPolynomial]
  | succ n =>
      simp [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_X_mul]

private theorem toPolynomial_ofList_eq_X_pow_dropWhile (l : List Int) :
    ∃ k : Nat,
      HexPolyMathlib.toPolynomial (DensePoly.ofList l) =
        Polynomial.X ^ k * HexPolyMathlib.toPolynomial
          (DensePoly.ofList (l.dropWhile (· == 0))) := by
  induction l with
  | nil =>
      exact ⟨0, by simp⟩
  | cons a l ih =>
      by_cases ha : a = 0
      · subst a
        obtain ⟨k, hk⟩ := ih
        refine ⟨k + 1, ?_⟩
        rw [toPolynomial_ofList_zero_cons, hk]
        simp only [List.dropWhile_cons, beq_self_eq_true, if_true]
        rw [pow_succ]
        ring
      · refine ⟨0, ?_⟩
        simp [ha]

private theorem ZPoly.toPolynomial_eq_X_pow_mul_removeX (p : ZPoly) :
    ∃ k : Nat,
      HexPolyMathlib.toPolynomial p = Polynomial.X ^ k *
        HexPolyMathlib.toPolynomial p.removeX := by
  obtain ⟨k, hk⟩ := toPolynomial_ofList_eq_X_pow_dropWhile p.toList
  refine ⟨k, ?_⟩
  simpa [ZPoly.removeX_eq_ofList_dropWhile] using hk

/-- Removing the maximal power of `X` preserves nonzeroness. -/
theorem ZPoly.removeX_ne_zero {p : ZPoly} (hp : p ≠ 0) :
    p.removeX ≠ 0 := by
  intro hremove
  obtain ⟨k, hk⟩ := ZPoly.toPolynomial_eq_X_pow_mul_removeX p
  rw [hremove, HexPolyMathlib.toPolynomial_zero, mul_zero] at hk
  apply hp
  exact HexPolyMathlib.equiv.injective (by simpa using hk)

/-- Removing the maximal power of `X` preserves every nonzero complex root. -/
theorem ZPoly.removeX_isRoot {p : ZPoly} {z : ℂ}
    (hz : z ≠ 0) (hroot : (HexRootsMathlib.toPolyℂ p).IsRoot z) :
    (HexRootsMathlib.toPolyℂ p.removeX).IsRoot z := by
  obtain ⟨k, hk⟩ := ZPoly.toPolynomial_eq_X_pow_mul_removeX p
  have hmap := congrArg
    (Polynomial.map (Int.castRingHom ℂ)) hk
  have hfactor :
      HexRootsMathlib.toPolyℂ p = Polynomial.X ^ k *
        HexRootsMathlib.toPolyℂ p.removeX := by
    simpa using hmap
  change (HexRootsMathlib.toPolyℂ p.removeX).eval z = 0
  change (HexRootsMathlib.toPolyℂ p).eval z = 0 at hroot
  rw [hfactor, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left
    (_root_.pow_ne_zero _ hz)

private theorem ZPoly.coeff_reciprocal (p : ZPoly) (j : Nat) :
    p.reciprocal.coeff j =
      if j < p.size then p.coeff (p.size - 1 - j) else 0 := by
  unfold ZPoly.reciprocal
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?]
  by_cases hj : j < p.size
  · rw [if_pos hj, Array.getElem?_reverse (by simpa using hj)]
    rw [← Array.getD_eq_getD_getElem?, DensePoly.toArray_getD]
    rw [DensePoly.toArray_size]
  · rw [if_neg hj, Array.getElem?_eq_none (by simpa using
      (Nat.le_of_not_gt hj))]
    rfl

private theorem ZPoly.toPolynomial_reciprocal (p : ZPoly) (hp : p ≠ 0) :
    HexPolyMathlib.toPolynomial p.reciprocal =
      (HexPolyMathlib.toPolynomial p).reverse := by
  have hpos : 0 < p.size := by
    by_contra h
    exact hp ((DensePoly.size_eq_zero_iff p).mp (by omega))
  have hdegree : (HexPolyMathlib.toPolynomial p).natDegree = p.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial,
      DensePoly.degree?_eq_some_of_pos_size p hpos, Option.getD_some]
  ext j
  rw [HexPolyMathlib.coeff_toPolynomial, ZPoly.coeff_reciprocal,
    Polynomial.coeff_reverse, hdegree, HexPolyMathlib.coeff_toPolynomial]
  by_cases hj : j < p.size
  · rw [if_pos hj, Polynomial.revAt_le (by omega)]
  · rw [if_neg hj, Polynomial.revAt_eq_self_of_lt (by omega)]
    exact (DensePoly.coeff_eq_zero_of_size_le p
      (Nat.le_of_not_gt hj)).symm

private theorem ZPoly.toPolyℂ_reciprocal (p : ZPoly) (hp : p ≠ 0) :
    HexRootsMathlib.toPolyℂ p.reciprocal =
      (HexRootsMathlib.toPolyℂ p).reverse := by
  have hdegree :
      ((HexPolyMathlib.toPolynomial p).map
        (Int.castRingHom ℂ)).natDegree =
        (HexPolyMathlib.toPolynomial p).natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int (Int.castRingHom ℂ))
      (HexPolyMathlib.toPolynomial p)
  change (HexPolyMathlib.toPolynomial p.reciprocal).map
      (Int.castRingHom ℂ) =
    ((HexPolyMathlib.toPolynomial p).map
      (Int.castRingHom ℂ)).reverse
  rw [ZPoly.toPolynomial_reciprocal p hp]
  ext j
  rw [Polynomial.coeff_map, Polynomial.coeff_reverse,
    Polynomial.coeff_reverse, hdegree, Polynomial.coeff_map]

private theorem ZPoly.reciprocal_ne_zero {p : ZPoly} (hp : p ≠ 0) :
    p.reciprocal ≠ 0 := by
  have hpos : 0 < p.size := by
    by_contra h
    exact hp ((DensePoly.size_eq_zero_iff p).mp (by omega))
  have hlast := DensePoly.coeff_last_ne_zero_of_pos_size p hpos
  intro hzero
  have hcoeff := congrArg (fun q : ZPoly => q.coeff 0) hzero
  rw [ZPoly.coeff_reciprocal, if_pos hpos, Nat.sub_zero] at hcoeff
  simp at hcoeff
  exact hlast hcoeff

private theorem ZPoly.reciprocal_isRoot {p : ZPoly} {z : ℂ}
    (hp : p ≠ 0) (hz : z ≠ 0)
    (hroot : (HexRootsMathlib.toPolyℂ p).IsRoot z) :
    (HexRootsMathlib.toPolyℂ p.reciprocal).IsRoot z⁻¹ := by
  rw [ZPoly.toPolyℂ_reciprocal p hp]
  letI : Invertible z := invertibleOfNonzero hz
  change ((HexRootsMathlib.toPolyℂ p).reverse).eval z⁻¹ = 0
  change (HexRootsMathlib.toPolyℂ p).eval z = 0 at hroot
  have hreverse :=
    (Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id ℂ) z
      (HexRootsMathlib.toPolyℂ p)).mpr (by simpa using hroot)
  simpa [invOf_eq_inv] using hreverse

/-- A nonzero complex root of a nonzero integer polynomial is bounded away
from zero by the reciprocal Cauchy bound of its coefficient height. -/
theorem ZPoly.root_norm_lower {p : ZPoly} {z : ℂ}
    (hp : p ≠ 0) (hz : z ≠ 0)
    (hroot : (HexRootsMathlib.toPolyℂ p).IsRoot z) :
    (((p.coeffAbsMax + 1 : Nat) : ℝ))⁻¹ < ‖z‖ := by
  let P := HexRootsMathlib.toPolyℂ p
  let R := P.reverse
  have hPne : P ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero p fun hsize =>
      hp ((DensePoly.size_eq_zero_iff p).mp hsize)
  have hRne : R ≠ 0 := by
    simpa [R] using hPne
  have hRroot : R.IsRoot z⁻¹ := by
    simpa [R, ZPoly.toPolyℂ_reciprocal p hp] using
      ZPoly.reciprocal_isRoot hp hz hroot
  have hsup :
      (Finset.range R.natDegree).sup (fun i => ‖R.coeff i‖₊) ≤
        (p.coeffAbsMax : NNReal) := by
    apply Finset.sup_le
    intro i hi
    rw [show R.coeff i = P.coeff (Polynomial.revAt P.natDegree i) by
      simp [R, Polynomial.coeff_reverse]]
    rw [show P.coeff (Polynomial.revAt P.natDegree i) =
        (p.coeff (Polynomial.revAt P.natDegree i) : ℂ) by
      simp [P]]
    rw [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs]
    exact_mod_cast HexRootsMathlib.coeff_natAbs_le_coeffAbsMax p
      (Polynomial.revAt P.natDegree i)
  have htrail : P.trailingCoeff ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hPne
  have htrailCoeff : p.coeff P.natTrailingDegree ≠ 0 := by
    intro hzero
    apply htrail
    rw [Polynomial.trailingCoeff, show P.coeff P.natTrailingDegree =
        (p.coeff P.natTrailingDegree : ℂ) by simp [P], hzero]
    simp
  have hlead : (1 : NNReal) ≤ ‖R.leadingCoeff‖₊ := by
    rw [show R.leadingCoeff = P.trailingCoeff by
      simp [R, Polynomial.reverse_leadingCoeff],
      Polynomial.trailingCoeff,
      show P.coeff P.natTrailingDegree =
        (p.coeff P.natTrailingDegree : ℂ) by simp [P],
      Complex.nnnorm_intCast, ← NNReal.natCast_natAbs]
    exact_mod_cast (show 1 ≤ (p.coeff P.natTrailingDegree).natAbs by
      have := Int.natAbs_pos.mpr htrailCoeff
      omega)
  have hcauchyNN :
      Polynomial.cauchyBound R ≤ (p.coeffAbsMax : NNReal) + 1 := by
    rw [Polynomial.cauchyBound]
    calc
      (Finset.range R.natDegree).sup (fun i => ‖R.coeff i‖₊) /
              ‖R.leadingCoeff‖₊ + 1 ≤
          (p.coeffAbsMax : NNReal) / 1 + 1 := by
        gcongr
      _ = (p.coeffAbsMax : NNReal) + 1 := by simp
  have hinvNN := hRroot.norm_lt_cauchyBound hRne
  have hinv : ‖z⁻¹‖ <
      ((p.coeffAbsMax + 1 : Nat) : ℝ) := by
    calc
      ‖z⁻¹‖ < (Polynomial.cauchyBound R : ℝ) := by
        exact_mod_cast hinvNN
      _ ≤ ((p.coeffAbsMax : NNReal) + 1 : NNReal) := by
        exact_mod_cast hcauchyNN
      _ = ((p.coeffAbsMax + 1 : Nat) : ℝ) := by norm_num
  rw [norm_inv] at hinv
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hdenom : 0 < ((p.coeffAbsMax + 1 : Nat) : ℝ) := by positivity
  have hprod :
      1 < ((p.coeffAbsMax + 1 : Nat) : ℝ) * ‖z‖ := by
    exact (mul_inv_lt_iff₀ hnorm).mp (by simpa using hinv)
  have hfinal := (mul_inv_lt_iff₀ hdenom).mpr (by
    simpa [mul_comm] using hprod)
  simpa only [one_mul] using hfinal

private theorem AlgebraicRoot.inv_norm_lower (a : AlgebraicRoot)
    (ha : a.toComplex ≠ 0) :
    (((a.p.coeffAbsMax + 1 : Nat) : ℝ))⁻¹ < ‖a.toComplex‖ :=
  ZPoly.root_norm_lower
    (HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep) ha
    (AlgebraicRoot.toComplex_isRoot a)

/-- A common complex root after specializing the coefficient variable is a
root of the executable bivariate resultant. -/
theorem resultant_isRoot
    (f g : DensePoly ZPoly) (t y : ℂ)
    (hpos : 1 < f.size ∨ 1 < g.size)
    (hf : ((HexPolyMathlib.toPolynomial f).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y = 0)
    (hg : ((HexPolyMathlib.toPolynomial g).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y = 0) :
    (HexRootsMathlib.toPolyℂ (DensePoly.resultant f g)).eval t = 0 := by
  let ε : ZPoly →+* ℂ :=
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom
  let F : Polynomial ℂ := (HexPolyMathlib.toPolynomial f).map ε
  let G : Polynomial ℂ := (HexPolyMathlib.toPolynomial g).map ε
  let m := f.degree?.getD 0
  let n := g.degree?.getD 0
  have hm : F.natDegree ≤ m := by
    calc
      F.natDegree ≤ (HexPolyMathlib.toPolynomial f).natDegree :=
        Polynomial.natDegree_map_le
      _ = m := by
        simp [m]
  have hn : G.natDegree ≤ n := by
    calc
      G.natDegree ≤ (HexPolyMathlib.toPolynomial g).natDegree :=
        Polynomial.natDegree_map_le
      _ = n := by
        simp [n]
  have hmn : 0 < m ∨ 0 < n := by
    rcases hpos with hfpos | hgpos
    · left
      dsimp only [m]
      rw [DensePoly.degree?_eq_some_of_pos_size f (by omega), Option.getD_some]
      omega
    · right
      dsimp only [n]
      rw [DensePoly.degree?_eq_some_of_pos_size g (by omega), Option.getD_some]
      omega
  have hresultant : Polynomial.resultant F G m n = 0 := by
    by_cases hboth : F = 0 ∧ G = 0
    · rcases hboth with ⟨hFzero, hGzero⟩
      rw [hFzero, hGzero, Polynomial.resultant_zero_zero]
      exact zero_pow (by omega)
    · have hne : F ≠ 0 ∨ G ≠ 0 := by
        by_cases hFzero : F = 0
        · right
          intro hGzero
          exact hboth ⟨hFzero, hGzero⟩
        · exact Or.inl hFzero
      have hdefault : Polynomial.resultant F G = 0 :=
        DensePoly.resultant_eq_zero_of_common_eval F G y
          (by simpa [F, ε] using hf) (by simpa [G, ε] using hg) hne
      have hmEq : m = F.natDegree + (m - F.natDegree) := by omega
      have hnEq : n = G.natDegree + (n - G.natDegree) := by omega
      rw [hmEq, Polynomial.resultant_add_left_deg F G F.natDegree n
        (m - F.natDegree) le_rfl]
      rw [hnEq, Polynomial.resultant_add_right_deg F G F.natDegree
        G.natDegree (n - G.natDegree) le_rfl]
      rw [hdefault]
      ring
  have hcorrespondence := congrArg ε
    (DensePoly.toPolynomial_resultant f g)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have heval (q : ZPoly) :
      ε q = (HexRootsMathlib.toPolyℂ q).eval t := by
    simp [ε, HexRootsMathlib.toPolyℂ, Polynomial.eval_map]
  rw [← heval]
  rw [hcorrespondence]
  exact hresultant

private theorem ZPoly.addEliminant_ne_zero (a b : AlgebraicRoot) :
    ZPoly.addEliminant a.p b.p ≠ 0 := by
  let P := HexRootsMathlib.toPolyℂ a.p
  let Q := HexRootsMathlib.toPolyℂ b.p
  have haPoly : a.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
  have hbPoly : b.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero b.rep
  have hPne : P ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero a.p fun hsize =>
      haPoly ((DensePoly.size_eq_zero_iff a.p).mp hsize)
  have hQne : Q ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero b.p fun hsize =>
      hbPoly ((DensePoly.size_eq_zero_iff b.p).mp hsize)
  let sums : Set ℂ :=
    (fun xy : ℂ × ℂ => xy.1 + xy.2) ''
      (P.rootSet ℂ ×ˢ Q.rootSet ℂ)
  have hsums : sums.Finite := by
    exact ((Polynomial.rootSet_finite P ℂ).prod
      (Polynomial.rootSet_finite Q ℂ)).image _
  obtain ⟨t, ht⟩ := hsums.exists_notMem
  let G := Q.comp (Polynomial.C t - Polynomial.X)
  have hcoprime : IsCoprime P G := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := ℂ) ℂ P G).2
    intro y
    by_contra hboth
    push Not at hboth
    apply ht
    refine ⟨(y, t - y), ⟨?_, ?_⟩, by simp⟩
    · exact (Polynomial.mem_rootSet_of_ne hPne).2 (by
        simpa [Polynomial.aeval_def] using hboth.1)
    · apply (Polynomial.mem_rootSet_of_ne hQne).2
      simpa [G, Polynomial.aeval_def, Polynomial.eval_comp] using hboth.2
  have hresultant : Polynomial.resultant P G ≠ 0 :=
    Polynomial.resultant_ne_zero P G hcoprime
  let y : DensePoly ZPoly := DensePoly.monomial 1 1
  let x : DensePoly ZPoly := DensePoly.C ZPoly.X
  let f : DensePoly ZPoly := a.p.liftOuter
  let g : DensePoly ZPoly := DensePoly.compose b.p.liftOuter (x - y)
  have hfmap :
      (HexPolyMathlib.toPolynomial f).map (evalZPoly t) = P := by
    simpa [f, P] using ZPoly.map_liftOuter a.p t
  have hgmap :
      (HexPolyMathlib.toPolynomial g).map (evalZPoly t) = G := by
    dsimp only [g, G, x, y]
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp,
      ZPoly.map_liftOuter]
    simp [Q, HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X, evalZPoly_X]
  have hfnat :
      (HexPolyMathlib.toPolynomial f).natDegree = P.natDegree := by
    calc
      (HexPolyMathlib.toPolynomial f).natDegree =
          a.p.degree?.getD 0 := by
        simpa [f] using ZPoly.natDegree_liftOuter a.p
      _ = P.natDegree := by
        simp [P]
  have hinnerNat :
      (HexPolyMathlib.toPolynomial (x - y)).natDegree = 1 := by
    dsimp only [x, y]
    rw [HexPolyMathlib.toPolynomial_sub,
      HexPolyMathlib.toPolynomial_C,
      HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X,
      show Polynomial.C ZPoly.X - Polynomial.X =
          -(Polynomial.X - Polynomial.C ZPoly.X) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hcomplexInnerNat :
      (Polynomial.C t - Polynomial.X).natDegree = 1 := by
    rw [show Polynomial.C t - Polynomial.X =
        -(Polynomial.X - Polynomial.C t) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hgnat :
      (HexPolyMathlib.toPolynomial g).natDegree = G.natDegree := by
    rw [show HexPolyMathlib.toPolynomial g =
        (HexPolyMathlib.toPolynomial b.p.liftOuter).comp
          (HexPolyMathlib.toPolynomial (x - y)) by
        simp [g]]
    rw [Polynomial.natDegree_comp, hinnerNat, mul_one,
      ZPoly.natDegree_liftOuter]
    rw [show G.natDegree = Q.natDegree *
        (Polynomial.C t - Polynomial.X).natDegree by
      exact Polynomial.natDegree_comp]
    rw [hcomplexInnerNat, mul_one]
    simp [Q]
  intro hzero
  have hcorrespondence := congrArg (evalZPoly t)
    (DensePoly.toPolynomial_resultant f g)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have hraw : DensePoly.resultant f g = 0 := by
    simpa [ZPoly.addEliminant, f, g, x, y] using hzero
  rw [hraw, map_zero, hfmap, hgmap] at hcorrespondence
  apply hresultant
  simpa [← hfnat, ← hgnat] using hcorrespondence.symm

private theorem ZPoly.mulEliminant_ne_zero (a b : AlgebraicRoot) :
    ZPoly.mulEliminant a.p b.p ≠ 0 := by
  let P := HexRootsMathlib.toPolyℂ a.p
  let Q := HexRootsMathlib.toPolyℂ b.p
  have haPoly : a.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
  have hbPoly : b.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero b.rep
  have hPne : P ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero a.p fun hsize =>
      haPoly ((DensePoly.size_eq_zero_iff a.p).mp hsize)
  have hQne : Q ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero b.p fun hsize =>
      hbPoly ((DensePoly.size_eq_zero_iff b.p).mp hsize)
  let products : Set ℂ :=
    (fun xy : ℂ × ℂ => xy.1 * xy.2) ''
      (P.rootSet ℂ ×ˢ Q.rootSet ℂ)
  have hproducts : products.Finite := by
    exact ((Polynomial.rootSet_finite P ℂ).prod
      (Polynomial.rootSet_finite Q ℂ)).image _
  have hforbidden : ({0} ∪ products : Set ℂ).Finite :=
    Set.Finite.union (Set.finite_singleton 0) hproducts
  obtain ⟨t, ht⟩ := hforbidden.exists_notMem
  have ht0 : t ≠ 0 := by
    intro hzero
    apply ht
    subst t
    exact Set.mem_union_left products (Set.mem_singleton 0)
  have htProducts : t ∉ products := by
    intro hmem
    exact ht (Set.mem_union_right {0} hmem)
  let G := (HexPolyMathlib.toPolynomial b.p.mulSubstitute).map
    (evalZPoly t)
  have hcoprime : IsCoprime P G := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := ℂ) ℂ P G).2
    intro y
    by_contra hboth
    push Not at hboth
    have hPy : P.eval y = 0 := by
      simpa [Polynomial.aeval_def] using hboth.1
    have hGy : G.eval y = 0 := by
      simpa [Polynomial.aeval_def] using hboth.2
    by_cases hy : y = 0
    · subst y
      have hcoeff :
          (b.p.coeff (b.p.degree?.getD 0) : ℂ) *
              t ^ b.p.degree?.getD 0 = 0 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero] at hGy
        simpa [G, Polynomial.coeff_map,
          HexPolyMathlib.coeff_toPolynomial,
          ZPoly.coeff_mulSubstitute, evalZPoly_monomial] using hGy
      have hbpos : 0 < b.p.size := by
        by_contra h
        exact hbPoly ((DensePoly.size_eq_zero_iff b.p).mp (by omega))
      have hbtop : b.p.coeff (b.p.degree?.getD 0) ≠ 0 := by
        rw [DensePoly.degree?_eq_some_of_pos_size b.p hbpos,
          Option.getD_some]
        exact DensePoly.coeff_last_ne_zero_of_pos_size b.p hbpos
      exact (mul_ne_zero (by exact_mod_cast hbtop)
        (_root_.pow_ne_zero _ ht0)) hcoeff
    · have hQeval : Q.eval (t / y) = 0 := by
        have hproduct :
            y ^ b.p.degree?.getD 0 * Q.eval (t / y) = 0 := by
          rw [← ZPoly.eval_map_mulSubstitute b.p t y hy]
          simpa [G] using hGy
        exact (mul_eq_zero.mp hproduct).resolve_left
          (_root_.pow_ne_zero _ hy)
      apply htProducts
      refine ⟨(y, t / y), ⟨?_, ?_⟩, ?_⟩
      · exact (Polynomial.mem_rootSet_of_ne hPne).2 hPy
      · exact (Polynomial.mem_rootSet_of_ne hQne).2 hQeval
      · field_simp
  have hresultant : Polynomial.resultant P G ≠ 0 :=
    Polynomial.resultant_ne_zero P G hcoprime
  let f : DensePoly ZPoly := a.p.liftOuter
  let g : DensePoly ZPoly := b.p.mulSubstitute
  have hfmap :
      (HexPolyMathlib.toPolynomial f).map (evalZPoly t) = P := by
    simpa [f, P] using ZPoly.map_liftOuter a.p t
  have hgmap :
      (HexPolyMathlib.toPolynomial g).map (evalZPoly t) = G := by
    rfl
  have hfnat :
      (HexPolyMathlib.toPolynomial f).natDegree = P.natDegree := by
    calc
      (HexPolyMathlib.toPolynomial f).natDegree =
          a.p.degree?.getD 0 := by
        simpa [f] using ZPoly.natDegree_liftOuter a.p
      _ = P.natDegree := by
        simp [P]
  have hgnat :
      (HexPolyMathlib.toPolynomial g).natDegree = G.natDegree := by
    simpa [g, G] using
      (ZPoly.natDegree_map_mulSubstitute b.p hbPoly t ht0).symm
  intro hzero
  have hcorrespondence := congrArg (evalZPoly t)
    (DensePoly.toPolynomial_resultant f g)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have hraw : DensePoly.resultant f g = 0 := by
    simpa [ZPoly.mulEliminant, f, g] using hzero
  rw [hraw, map_zero, hfmap, hgmap] at hcorrespondence
  apply hresultant
  simpa [← hfnat, ← hgnat] using hcorrespondence.symm

private theorem ZPoly.addEliminant_isRoot (a b : AlgebraicRoot) :
    (HexRootsMathlib.toPolyℂ (ZPoly.addEliminant a.p b.p)).IsRoot
      (a.toComplex + b.toComplex) := by
  unfold ZPoly.addEliminant
  apply resultant_isRoot
      (y := a.toComplex)
  · left
    have hsize : 1 < a.p.size := by
      have hpos : 0 < a.p.size := by
        by_contra h
        have hzero : a.p = 0 :=
          (DensePoly.size_eq_zero_iff a.p).mp (by omega)
        have hdegree := a.pos_degree
        rw [hzero] at hdegree
        simp at hdegree
      have hdegree := a.pos_degree
      rw [DensePoly.degree?_eq_some_of_pos_size a.p hpos,
        Option.getD_some] at hdegree
      omega
    have hcoeff :
        a.p.liftOuter.coeff (a.p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun p : ZPoly => p.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size a.p (by omega) hconst
    have hlt : a.p.size - 1 < a.p.liftOuter.size := by
      by_contra h
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    omega
  · change ((HexPolyMathlib.toPolynomial a.p.liftOuter).map
      (evalZPoly (a.toComplex + b.toComplex))).eval a.toComplex = 0
    rw [ZPoly.map_liftOuter]
    exact AlgebraicRoot.toComplex_isRoot a
  · change (((HexPolyMathlib.toPolynomial
      (DensePoly.compose b.p.liftOuter
        (DensePoly.C ZPoly.X - DensePoly.monomial 1 1))).map
          (evalZPoly (a.toComplex + b.toComplex))).eval a.toComplex) = 0
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp,
      ZPoly.map_liftOuter]
    simp [HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X, evalZPoly_X,
      Polynomial.eval_comp, AlgebraicRoot.toComplex_isRoot]

private theorem ZPoly.mulEliminant_isRoot (a b : AlgebraicRoot)
    (ha : a.toComplex ≠ 0) :
    (HexRootsMathlib.toPolyℂ (ZPoly.mulEliminant a.p b.p)).IsRoot
      (a.toComplex * b.toComplex) := by
  unfold ZPoly.mulEliminant
  apply resultant_isRoot
      (y := a.toComplex)
  · left
    have hsize : 1 < a.p.size := by
      have hpos : 0 < a.p.size := by
        by_contra h
        have hzero : a.p = 0 :=
          (DensePoly.size_eq_zero_iff a.p).mp (by omega)
        have hdegree := a.pos_degree
        rw [hzero] at hdegree
        simp at hdegree
      have hdegree := a.pos_degree
      rw [DensePoly.degree?_eq_some_of_pos_size a.p hpos,
        Option.getD_some] at hdegree
      omega
    have hcoeff :
        a.p.liftOuter.coeff (a.p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun p : ZPoly => p.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size a.p (by omega) hconst
    have hlt : a.p.size - 1 < a.p.liftOuter.size := by
      by_contra h
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    omega
  · change ((HexPolyMathlib.toPolynomial a.p.liftOuter).map
      (evalZPoly (a.toComplex * b.toComplex))).eval a.toComplex = 0
    rw [ZPoly.map_liftOuter]
    exact AlgebraicRoot.toComplex_isRoot a
  · change ((HexPolyMathlib.toPolynomial b.p.mulSubstitute).map
      (evalZPoly (a.toComplex * b.toComplex))).eval a.toComplex = 0
    rw [ZPoly.eval_map_mulSubstitute b.p _ _ ha]
    have hdiv : a.toComplex * b.toComplex / a.toComplex = b.toComplex := by
      field_simp
    rw [hdiv, AlgebraicRoot.toComplex_isRoot]
    simp

end


/-- A successful eliminant search selects the supplied semantic root whenever
the operation ball contains it. -/
theorem AlgebraicRoot.ofEliminant?_sound
    (raw : ZPoly) (ballAt : Int → Option DyadicComplexBall)
    {c : AlgebraicRoot} {z : ℂ}
    (h : AlgebraicRoot.ofEliminant? raw ballAt = some c)
    (hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot z)
    (hball : ∀ (ball : DyadicComplexBall),
      ballAt (separationDepth (ZPoly.squareFreeCore raw)) = some ball →
        z ∈ ball.set) :
    c.toComplex = z := by
  unfold AlgebraicRoot.ofEliminant? at h
  dsimp only at h
  split at h
  · rename_i hprim
    split at h
    · rename_i hpos
      split at h
      · rename_i hdegree
        split at h
        · rename_i hsimple
          obtain ⟨ball, hballAt, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨isolations, hisolate, h⟩ :=
            Option.bind_eq_some_iff.mp h
          obtain ⟨refined, hrefined, h⟩ :=
            Option.bind_eq_some_iff.mp h
          cases hselected : refined.toList.filter fun r =>
              r.1.square.meetsBall ball with
          | nil => simp [hselected] at h
          | cons matching rest =>
              cases rest with
              | cons second rest => simp [hselected] at h
              | nil =>
                  rw [hselected] at h
                  have hc := Option.some.inj h
                  subst c
                  let p := ZPoly.squareFreeCore raw
                  have hpne : p ≠ 0 := by
                    intro hp
                    have hdegree' := hdegree
                    change ZPoly.squareFreeCore raw = 0 at hp
                    rw [hp] at hdegree'
                    simp at hdegree'
                  have hrawne : raw ≠ 0 := by
                    intro hraw
                    apply hpne
                    subst raw
                    rfl
                  have hpRoot : (HexRootsMathlib.toPolyℂ p).IsRoot z := by
                    simpa [p] using
                      HexPolyZMathlib.isRoot_squareFreeCore hrawne hroot
                  obtain ⟨iso, hiso, hisoRoot⟩ :=
                    HexRootsMathlib.isolate_root_mem_of_pos p hsimple
                      (separationDepth p : Int) .nkThenPellet hdegree
                      hisolate hpRoot
                  obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
                  have hi : i < isolations.size := by simpa using hiList
                  obtain ⟨hmapSize, hmapGet⟩ :=
                    HexRootsMathlib.array_mapM_some_get hrefined
                  have hj : i < refined.size := by
                    simpa [← hmapSize] using hi
                  have hto := hmapGet i hi hj
                  have hrawIso : refined[i].1 = isolations[i] := by
                    rw [DyadicRootIsolation.toRefined?] at hto
                    split at hto
                    · exact (congrArg Subtype.val (Option.some.inj hto)).symm
                    · simp at hto
                  have harrIso : isolations[i] = iso := by
                    rw [← hidx]
                    exact (Array.getElem_toList hi).symm
                  have hrefinedRoot :
                      HexRootsMathlib.RefinedIsolation.root refined[i] = z := by
                    change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 = z
                    rw [hrawIso, harrIso]
                    exact hisoRoot
                  have hzCandidate :
                      z ∈ refined[i].1.square.toBall.set := by
                    rw [← hrefinedRoot]
                    exact DyadicComplexBall.mem_toBall
                      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc
                        refined[i])
                  have hzBall : z ∈ ball.set := by
                    exact hball ball (by simpa [p] using hballAt)
                  have hmeet :
                      refined[i].1.square.meetsBall ball = true := by
                    simpa [DyadicSquare.meetsBall] using
                      DyadicComplexBall.meets_of_mem hzCandidate hzBall
                  have hmem : refined[i] ∈
                      refined.toList.filter fun r =>
                        r.1.square.meetsBall ball := by
                    simp [hmeet]
                  rw [hselected] at hmem
                  have heq : refined[i] = matching := by simpa using hmem
                  change matching.root = z
                  rw [← heq]
                  exact hrefinedRoot
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A nonzero eliminant root enclosed by a sufficiently small operation ball
survives normalization, isolation, and the singleton selection filter. -/
theorem AlgebraicRoot.ofEliminant?_isSome
    (raw : ZPoly) (ballAt : Int → Option DyadicComplexBall)
    {z : ℂ} (hraw : raw ≠ 0)
    (hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot z)
    (ball : DyadicComplexBall)
    (hballAt : ballAt (separationDepth (ZPoly.squareFreeCore raw)) =
      some ball)
    (hzball : z ∈ ball.set)
    (hballRadius : ball.realRadius ≤
      (2 : ℝ) ^ (-(mahlerPrec (ZPoly.squareFreeCore raw) : ℤ))) :
    (AlgebraicRoot.ofEliminant? raw ballAt).isSome := by
  have hpne : ZPoly.squareFreeCore raw ≠ 0 :=
    ZPoly.squareFreeCore_ne_zero raw hraw
  have hpRoot :
      (HexRootsMathlib.toPolyℂ (ZPoly.squareFreeCore raw)).IsRoot z := by
    exact HexPolyZMathlib.isRoot_squareFreeCore hraw hroot
  have hprim : ZPoly.content (ZPoly.squareFreeCore raw) = 1 := by
    simpa [ZPoly.Primitive] using ZPoly.squareFreeCore_primitive raw hraw
  have hpos : 0 < (ZPoly.squareFreeCore raw).leadingCoeff :=
    ZPoly.leadingCoeff_squareFreeCore_pos raw hraw
  have hsimple : HasOnlySimpleRoots (ZPoly.squareFreeCore raw) := by
    simpa [HasOnlySimpleRoots] using
      ZPoly.squareFreeRat_squareFreeCore raw hraw
  have hdegree : 0 < (ZPoly.squareFreeCore raw).degree?.getD 0 := by
    by_contra hn
    have hsize : (ZPoly.squareFreeCore raw).size ≠ 0 := by
      intro hsize
      exact hpne ((DensePoly.size_eq_zero_iff _).mp hsize)
    exact HexRootsMathlib.not_isRoot_of_degree_not_pos
      (ZPoly.squareFreeCore raw) hsize hn z hpRoot
  unfold AlgebraicRoot.ofEliminant?
  dsimp only
  rw [dif_pos hprim, dif_pos hpos, dif_pos hdegree, dif_pos hsimple]
  rw [hballAt]
  have hisolateSome := HexRootsMathlib.isolate_isSome
    (ZPoly.squareFreeCore raw) hsimple hpne
    (separationDepth (ZPoly.squareFreeCore raw) : Int) .nkThenPellet
  cases hisolate : isolate (ZPoly.squareFreeCore raw) hsimple
      (separationDepth (ZPoly.squareFreeCore raw) : Int) with
  | none => simp [hisolate] at hisolateSome
  | some isolations =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hmapSome := HexRootsMathlib.array_mapM_isSome
        (xs := isolations) (f := DyadicRootIsolation.toRefined?)
        (fun iso hiso => by
          unfold DyadicRootIsolation.toRefined?
          rw [dif_pos (HexRootsMathlib.isolate_refined
            (ZPoly.squareFreeCore raw) hsimple
            (separationDepth (ZPoly.squareFreeCore raw) : Int)
            .nkThenPellet hisolate iso hiso)]
          rfl)
      cases hrefined : isolations.mapM DyadicRootIsolation.toRefined? with
      | none => simp [hrefined] at hmapSome
      | some refined =>
          simp only [Option.bind_some]
          obtain ⟨hmapSize, hmapGet⟩ :=
            HexRootsMathlib.array_mapM_some_get hrefined
          have hrefinedPairwise : refined.toList.Pairwise fun r s =>
              HexRootsMathlib.RefinedIsolation.root r ≠
                HexRootsMathlib.RefinedIsolation.root s := by
            rw [List.pairwise_iff_getElem]
            intro i j hi hj hij
            have hi' : i < isolations.size := by
              simpa [hmapSize] using hi
            have hj' : j < isolations.size := by
              simpa [hmapSize] using hj
            have htoI := hmapGet i hi' hi
            have htoJ := hmapGet j hj' hj
            have hrawI : refined[i].1 = isolations[i] := by
              rw [DyadicRootIsolation.toRefined?] at htoI
              split at htoI
              · exact (congrArg Subtype.val (Option.some.inj htoI)).symm
              · simp at htoI
            have hrawJ : refined[j].1 = isolations[j] := by
              rw [DyadicRootIsolation.toRefined?] at htoJ
              split at htoJ
              · exact (congrArg Subtype.val (Option.some.inj htoJ)).symm
              · simp at htoJ
            intro hroots
            apply HexRootsMathlib.isolate_roots_ne
              (ZPoly.squareFreeCore raw) hsimple
              (separationDepth (ZPoly.squareFreeCore raw) : Int)
              .nkThenPellet hisolate
              hi' hj' (Nat.ne_of_lt hij)
            change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 =
              HexRootsMathlib.DyadicRootIsolation.root refined[j].1 at hroots
            simpa [hrawI, hrawJ] using hroots
          obtain ⟨iso, hiso, hisoRoot⟩ :=
            HexRootsMathlib.isolate_root_mem_of_pos
              (ZPoly.squareFreeCore raw) hsimple
              (separationDepth (ZPoly.squareFreeCore raw) : Int)
              .nkThenPellet hdegree hisolate hpRoot
          obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
          have hi : i < isolations.size := by simpa using hiList
          have hj : i < refined.size := by simpa [← hmapSize] using hi
          have hto := hmapGet i hi hj
          have hrawIso : refined[i].1 = isolations[i] := by
            rw [DyadicRootIsolation.toRefined?] at hto
            split at hto
            · exact (congrArg Subtype.val (Option.some.inj hto)).symm
            · simp at hto
          have harrIso : isolations[i] = iso := by
            rw [← hidx]
            exact (Array.getElem_toList hi).symm
          have hrefinedRoot :
              HexRootsMathlib.RefinedIsolation.root refined[i] = z := by
            change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 = z
            rw [hrawIso, harrIso]
            exact hisoRoot
          have hzCandidate : z ∈ refined[i].1.square.toBall.set := by
            rw [← hrefinedRoot]
            exact DyadicComplexBall.mem_toBall
              (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc refined[i])
          have hmeet : refined[i].1.square.meetsBall ball = true := by
            simpa [DyadicSquare.meetsBall] using
              DyadicComplexBall.meets_of_mem hzCandidate hzball
          have hmem : refined[i] ∈ refined.toList.filter fun r =>
              r.1.square.meetsBall ball := by
            simp [hmeet]
          cases hselected : refined.toList.filter fun r =>
              r.1.square.meetsBall ball with
          | nil => simp [hselected] at hmem
          | cons matching rest =>
              cases rest with
              | nil => rfl
              | cons second tail =>
                  have hfilteredPairwise := hrefinedPairwise.filter fun r =>
                    r.1.square.meetsBall ball
                  rw [hselected] at hfilteredPairwise
                  have hneRoots : matching.root ≠ second.root :=
                    List.rel_of_pairwise_cons hfilteredPairwise (by simp)
                  have hmatching := List.mem_filter.mp (show matching ∈
                      refined.toList.filter fun r =>
                        r.1.square.meetsBall ball by simp [hselected])
                  have hsecond := List.mem_filter.mp (show second ∈
                      refined.toList.filter fun r =>
                        r.1.square.meetsBall ball by simp [hselected])
                  have hmatchingRoot : matching.root = z :=
                    QAdjoin.root_eq_of_meetsBall hpne matching hpRoot
                      hzball hballRadius hmatching.2
                  have hsecondRoot : second.root = z :=
                    QAdjoin.root_eq_of_meetsBall hpne second hpRoot
                      hzball hballRadius hsecond.2
                  exact (hneRoots (hmatchingRoot.trans hsecondRoot.symm)).elim

namespace AlgebraicRoot

/-- Reflection computes complex negation. -/
theorem neg_toComplex (a : AlgebraicRoot) :
    a.neg.toComplex = -a.toComplex := by
  have hroot :
      (HexRootsMathlib.toPolyℂ a.p.negRoots).IsRoot (-a.toComplex) :=
    HexRootsMathlib.ZPoly.isRoot_negRoots
      a.prim
      (AlgebraicRoot.toComplex_isRoot a)
  have hmem :
      -a.toComplex ∈
        HexRootsMathlib.DyadicSquare.closedDisc a.neg.rep.1.square := by
    exact HexRootsMathlib.DyadicSquare.closedDisc_neg.mpr
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc a.rep)
  exact (HexRootsMathlib.RefinedIsolation.eq_root_of_mem_closedDisc
    a.neg.rep hroot hmem).symm

/-- A certified lazy sum denotes the sum of its inputs. -/
theorem add?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.add? b = some c) :
    c.toComplex = a.toComplex + b.toComplex := by
  unfold AlgebraicRoot.add? at h
  apply AlgebraicRoot.ofEliminant?_sound
    (raw := ZPoly.addEliminant a.p b.p)
    (ballAt := fun prec => do
      let target := prec + 4
      let ar ← a.rep.refineTo? target
      let br ← b.rep.refineTo? target
      some (ar.1.1.square.toBall.add br.1.1.square.toBall))
    h (ZPoly.addEliminant_isRoot a b)
  intro ball hball
  dsimp only at hball
  obtain ⟨ar, har, hball⟩ := Option.bind_eq_some_iff.mp hball
  obtain ⟨br, hbr, hball⟩ := Option.bind_eq_some_iff.mp hball
  have hballEq := Option.some.inj hball
  subst ball
  apply DyadicComplexBall.add_mem
  · have harRoot :
        HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
      exact (HexRootsMathlib.RefinedIsolation.refineTo_root
        a.rep _ .nkThenPellet har).trans rfl
    rw [← harRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
  · have hbrRoot :
        HexRootsMathlib.RefinedIsolation.root br.1 = b.toComplex := by
      exact (HexRootsMathlib.RefinedIsolation.refineTo_root
        b.rep _ .nkThenPellet hbr).trans rfl
    rw [← hbrRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc br.1)

/-- The bounded lazy addition search always finds its certificate. -/
theorem add?_isSome (a b : AlgebraicRoot) :
    (a.add? b).isSome := by
  unfold AlgebraicRoot.add?
  have harSome := RefinedIsolation.refineTo?_isSome a.rep
    ((separationDepth (ZPoly.squareFreeCore
      (ZPoly.addEliminant a.p b.p)) : Int) + 4)
  cases har : a.rep.refineTo?
      ((separationDepth (ZPoly.squareFreeCore
        (ZPoly.addEliminant a.p b.p)) : Int) + 4) .nkThenPellet with
  | none => simp [har] at harSome
  | some ar =>
      have hbrSome := RefinedIsolation.refineTo?_isSome b.rep
        ((separationDepth (ZPoly.squareFreeCore
          (ZPoly.addEliminant a.p b.p)) : Int) + 4)
      cases hbr : b.rep.refineTo?
          ((separationDepth (ZPoly.squareFreeCore
            (ZPoly.addEliminant a.p b.p)) : Int) + 4) .nkThenPellet with
      | none => simp [hbr] at hbrSome
      | some br =>
          apply AlgebraicRoot.ofEliminant?_isSome
            (raw := ZPoly.addEliminant a.p b.p)
            (ballAt := fun prec => do
              let target := prec + 4
              let ar ← a.rep.refineTo? target
              let br ← b.rep.refineTo? target
              some (ar.1.1.square.toBall.add br.1.1.square.toBall))
            (z := a.toComplex + b.toComplex)
            (ZPoly.addEliminant_ne_zero a b)
            (ZPoly.addEliminant_isRoot a b)
            (ar.1.1.square.toBall.add br.1.1.square.toBall)
          · dsimp only
            rw [har, hbr]
            rfl
          · apply DyadicComplexBall.add_mem
            · have harRoot :
                  HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
                exact (HexRootsMathlib.RefinedIsolation.refineTo_root
                  a.rep _ .nkThenPellet har).trans rfl
              rw [← harRoot]
              exact DyadicComplexBall.mem_toBall
                (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
            · have hbrRoot :
                  HexRootsMathlib.RefinedIsolation.root br.1 = b.toComplex := by
                exact (HexRootsMathlib.RefinedIsolation.refineTo_root
                  b.rep _ .nkThenPellet hbr).trans rfl
              rw [← hbrRoot]
              exact DyadicComplexBall.mem_toBall
                (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc br.1)
          · rw [DyadicComplexBall.realRadius_add]
            have harPrec := RefinedIsolation.refineTo?_precision a.rep
              ((separationDepth (ZPoly.squareFreeCore
                (ZPoly.addEliminant a.p b.p)) : Int) + 4)
              .nkThenPellet har
            have hbrPrec := RefinedIsolation.refineTo?_precision b.rep
              ((separationDepth (ZPoly.squareFreeCore
                (ZPoly.addEliminant a.p b.p)) : Int) + 4)
              .nkThenPellet hbr
            have hsepNat :
                mahlerPrec (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) ≤
                  separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) := by
              rw [separationDepth]
              omega
            have hsepInt :
                (mahlerPrec
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) ≤
                  (separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) := by
              exact_mod_cast hsepNat
            have hpow :
                (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) ≤
                  (2 : ℝ) ^ (-(mahlerPrec
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
            calc
              ar.1.1.square.toBall.realRadius +
                    br.1.1.square.toBall.realRadius ≤
                  2 * (2 : ℝ) ^ (-((separationDepth
                      (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) + 4)) +
                    2 * (2 : ℝ) ^ (-((separationDepth
                      (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) + 4)) :=
                add_le_add
                  (DyadicComplexBall.realRadius_toBall_le harPrec)
                  (DyadicComplexBall.realRadius_toBall_le hbrPrec)
              _ = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := by
                rw [show -((separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) + 4) =
                    -(separationDepth
                      (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) - 4 by
                  omega]
                rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
                norm_num
                ring
              _ ≤ (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := by
                have hnonneg : 0 ≤ (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := by
                  positivity
                nlinarith
              _ ≤ (2 : ℝ) ^ (-(mahlerPrec
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := hpow

/-- Total lazy addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicRoot) :
    (a.add b).toComplex = a.toComplex + b.toComplex := by
  cases h : a.add? b with
  | none =>
      have hsome := add?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.add, h] using add?_sound a b h

/-- A certified lazy difference denotes the difference of its inputs. -/
theorem sub?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.sub? b = some c) :
    c.toComplex = a.toComplex - b.toComplex := by
  have hsum : c.toComplex = a.toComplex + b.neg.toComplex :=
    add?_sound a b.neg h
  rw [neg_toComplex] at hsum
  exact hsum

/-- The bounded lazy subtraction search always finds its certificate. -/
theorem sub?_isSome (a b : AlgebraicRoot) :
    (a.sub? b).isSome := by
  exact add?_isSome a b.neg

/-- Total lazy subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicRoot) :
    (a.sub b).toComplex = a.toComplex - b.toComplex := by
  cases h : a.sub? b with
  | none =>
      have hsome := sub?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.sub, h] using sub?_sound a b h

/-- A certified lazy product denotes the product of its inputs. -/
theorem mul?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.mul? b = some c) :
    c.toComplex = a.toComplex * b.toComplex := by
  unfold AlgebraicRoot.mul? at h
  split at h
  · rename_i hzero
    have hc := Option.some.inj h
    subst c
    change (0 : AlgebraicNumber).toComplex =
      a.toComplex * b.toComplex
    rw [AlgebraicNumber.zero_toComplex]
    rw [Bool.or_eq_true] at hzero
    rcases hzero with ha | hb
    · rw [(AlgebraicRoot.isZero_iff a).mp ha]
      simp
    · rw [(AlgebraicRoot.isZero_iff b).mp hb]
      simp
  · rename_i hnonzero
    have ha : a.toComplex ≠ 0 := by
      intro ha
      have hazero : a.isZero = true :=
        (AlgebraicRoot.isZero_iff a).mpr ha
      simp [hazero] at hnonzero
    have hb : b.toComplex ≠ 0 := by
      intro hb
      have hbzero : b.isZero = true :=
        (AlgebraicRoot.isZero_iff b).mpr hb
      simp [hbzero] at hnonzero
    let raw := (ZPoly.mulEliminant a.p b.p).removeX
    have hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot
        (a.toComplex * b.toComplex) := by
      exact ZPoly.removeX_isRoot (mul_ne_zero ha hb)
        (ZPoly.mulEliminant_isRoot a b ha)
    apply AlgebraicRoot.ofEliminant?_sound
      (raw := raw)
      (ballAt := fun prec => do
        let target := prec + (AlgebraicRoot.mulGuardBits a b : Int)
        let ar ← a.rep.refineTo? target
        let br ← b.rep.refineTo? target
        some (ar.1.1.square.toBall.mul br.1.1.square.toBall))
      h hroot
    intro ball hball
    dsimp only at hball
    obtain ⟨ar, har, hball⟩ := Option.bind_eq_some_iff.mp hball
    obtain ⟨br, hbr, hball⟩ := Option.bind_eq_some_iff.mp hball
    have hballEq := Option.some.inj hball
    subst ball
    apply DyadicComplexBall.mul_mem
    · have harRoot :
          HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
        exact (HexRootsMathlib.RefinedIsolation.refineTo_root
          a.rep _ .nkThenPellet har).trans rfl
      rw [← harRoot]
      exact DyadicComplexBall.mem_toBall
        (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
    · have hbrRoot :
          HexRootsMathlib.RefinedIsolation.root br.1 = b.toComplex := by
        exact (HexRootsMathlib.RefinedIsolation.refineTo_root
          b.rep _ .nkThenPellet hbr).trans rfl
      rw [← hbrRoot]
      exact DyadicComplexBall.mem_toBall
        (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc br.1)

/-- The bounded lazy multiplication search always finds its certificate. -/
theorem mul?_isSome (a b : AlgebraicRoot) :
    (a.mul? b).isSome := by
  unfold AlgebraicRoot.mul?
  split
  · simp
  · rename_i hnonzero
    have ha : a.toComplex ≠ 0 := by
      intro ha
      have hazero : a.isZero = true :=
        (AlgebraicRoot.isZero_iff a).mpr ha
      simp [hazero] at hnonzero
    have hb : b.toComplex ≠ 0 := by
      intro hb
      have hbzero : b.isZero = true :=
        (AlgebraicRoot.isZero_iff b).mpr hb
      simp [hbzero] at hnonzero
    let raw := (ZPoly.mulEliminant a.p b.p).removeX
    have hraw : raw ≠ 0 := by
      exact ZPoly.removeX_ne_zero (ZPoly.mulEliminant_ne_zero a b)
    have hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot
        (a.toComplex * b.toComplex) := by
      exact ZPoly.removeX_isRoot (mul_ne_zero ha hb)
        (ZPoly.mulEliminant_isRoot a b ha)
    have harSome := RefinedIsolation.refineTo?_isSome a.rep
      ((separationDepth (ZPoly.squareFreeCore raw) : Int) +
        (AlgebraicRoot.mulGuardBits a b : Int))
    cases har : a.rep.refineTo?
        ((separationDepth (ZPoly.squareFreeCore raw) : Int) +
          (AlgebraicRoot.mulGuardBits a b : Int)) .nkThenPellet with
    | none => simp [har] at harSome
    | some ar =>
      have hbrSome := RefinedIsolation.refineTo?_isSome b.rep
        ((separationDepth (ZPoly.squareFreeCore raw) : Int) +
          (AlgebraicRoot.mulGuardBits a b : Int))
      cases hbr : b.rep.refineTo?
          ((separationDepth (ZPoly.squareFreeCore raw) : Int) +
            (AlgebraicRoot.mulGuardBits a b : Int)) .nkThenPellet with
      | none => simp [hbr] at hbrSome
      | some br =>
        apply AlgebraicRoot.ofEliminant?_isSome
          (raw := raw)
          (ballAt := fun prec => do
            let target := prec + (AlgebraicRoot.mulGuardBits a b : Int)
            let ar ← a.rep.refineTo? target
            let br ← b.rep.refineTo? target
            some (ar.1.1.square.toBall.mul br.1.1.square.toBall))
          (z := a.toComplex * b.toComplex)
          hraw hroot
          (ar.1.1.square.toBall.mul br.1.1.square.toBall)
        · dsimp only
          rw [har, hbr]
          rfl
        · apply DyadicComplexBall.mul_mem
          · have harRoot :
                HexRootsMathlib.RefinedIsolation.root ar.1 =
                  a.toComplex := by
              exact (HexRootsMathlib.RefinedIsolation.refineTo_root
                a.rep _ .nkThenPellet har).trans rfl
            rw [← harRoot]
            exact DyadicComplexBall.mem_toBall
              (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
          · have hbrRoot :
                HexRootsMathlib.RefinedIsolation.root br.1 =
                  b.toComplex := by
              exact (HexRootsMathlib.RefinedIsolation.refineTo_root
                b.rep _ .nkThenPellet hbr).trans rfl
            rw [← hbrRoot]
            exact DyadicComplexBall.mem_toBall
              (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc br.1)
        · have hguardRadius :
              (ar.1.1.square.toBall.mul br.1.1.square.toBall).realRadius ≤
                (2 : ℝ) ^ (-((separationDepth
                  (ZPoly.squareFreeCore raw) : Int) + 4)) := by
            exact RefinedIsolation.mulRadius_le a.rep b.rep
              (separationDepth (ZPoly.squareFreeCore raw) : Int)
              .nkThenPellet
              (by simpa [AlgebraicRoot.mulGuardBits] using har)
              (by simpa [AlgebraicRoot.mulGuardBits] using hbr)
          have hsepNat :
              mahlerPrec (ZPoly.squareFreeCore raw) ≤
                separationDepth (ZPoly.squareFreeCore raw) := by
            rw [separationDepth]
            omega
          have hsepInt :
              (mahlerPrec (ZPoly.squareFreeCore raw) : Int) ≤
                (separationDepth (ZPoly.squareFreeCore raw) : Int) := by
            exact_mod_cast hsepNat
          have hshift :
              (2 : ℝ) ^ (-((separationDepth
                  (ZPoly.squareFreeCore raw) : Int) + 4)) ≤
                (2 : ℝ) ^ (-(separationDepth
                  (ZPoly.squareFreeCore raw) : Int)) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hpow :
              (2 : ℝ) ^ (-(separationDepth
                  (ZPoly.squareFreeCore raw) : Int)) ≤
                (2 : ℝ) ^ (-(mahlerPrec
                  (ZPoly.squareFreeCore raw) : Int)) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          exact hguardRadius.trans (hshift.trans hpow)

/-- Total lazy multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicRoot) :
    (a.mul b).toComplex = a.toComplex * b.toComplex := by
  cases h : a.mul? b with
  | none =>
      have hsome := mul?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.mul, h] using mul?_sound a b h

/-- A certified lazy inverse denotes the reciprocal of its input, including
the executable convention `0⁻¹ = 0`. -/
theorem inv?_sound (a : AlgebraicRoot) {b : AlgebraicRoot}
    (h : a.inv? = some b) :
    b.toComplex = a.toComplex⁻¹ := by
  unfold AlgebraicRoot.inv? at h
  split at h
  · rename_i hzero
    have hb := Option.some.inj h
    subst b
    change (0 : AlgebraicNumber).toComplex = a.toComplex⁻¹
    rw [AlgebraicNumber.zero_toComplex,
      (AlgebraicRoot.isZero_iff a).mp hzero]
    simp
  · rename_i hnonzero
    have ha : a.toComplex ≠ 0 := by
      intro ha
      exact hnonzero ((AlgebraicRoot.isZero_iff a).mpr ha)
    have hp : a.p ≠ 0 :=
      HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
    have hroot : (HexRootsMathlib.toPolyℂ a.p.reciprocal).IsRoot
        a.toComplex⁻¹ :=
      ZPoly.reciprocal_isRoot hp ha (AlgebraicRoot.toComplex_isRoot a)
    apply AlgebraicRoot.ofEliminant?_sound
      (raw := a.p.reciprocal)
      (ballAt := fun prec => do
        let target := prec + (AlgebraicRoot.invGuardBits a : Int)
        let ar ← a.rep.refineTo? target
        ar.1.1.square.toBall.inv? target)
      h hroot
    intro ball hball
    dsimp only at hball
    obtain ⟨ar, har, hball⟩ := Option.bind_eq_some_iff.mp hball
    apply DyadicComplexBall.inv_mem (h := hball)
    have harRoot :
        HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
      exact (HexRootsMathlib.RefinedIsolation.refineTo_root
        a.rep _ .nkThenPellet har).trans rfl
    rw [← harRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)

/-- The bounded lazy inverse search always finds its certificate. -/
theorem inv?_isSome (a : AlgebraicRoot) :
    a.inv?.isSome := by
  unfold AlgebraicRoot.inv?
  split
  · simp
  · rename_i hnonzero
    have ha : a.toComplex ≠ 0 := by
      intro ha
      exact hnonzero ((AlgebraicRoot.isZero_iff a).mpr ha)
    have hp : a.p ≠ 0 :=
      HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
    let raw := a.p.reciprocal
    have hraw : raw ≠ 0 := ZPoly.reciprocal_ne_zero hp
    have hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot a.toComplex⁻¹ := by
      exact ZPoly.reciprocal_isRoot hp ha
        (AlgebraicRoot.toComplex_isRoot a)
    have harSome := RefinedIsolation.refineTo?_isSome a.rep
      ((separationDepth (ZPoly.squareFreeCore raw) : Int) +
        (AlgebraicRoot.invGuardBits a : Int))
    cases har : a.rep.refineTo?
        ((separationDepth (ZPoly.squareFreeCore raw) : Int) +
          (AlgebraicRoot.invGuardBits a : Int)) .nkThenPellet with
    | none => simp [har] at harSome
    | some ar =>
        obtain ⟨ball, hinv, hguardRadius⟩ :=
          RefinedIsolation.invBall_exists a.rep
            (separationDepth (ZPoly.squareFreeCore raw) : Int)
            (by positivity) .nkThenPellet
            (AlgebraicRoot.inv_norm_lower a ha)
            (by simpa only [AlgebraicRoot.invGuardBits] using har)
        apply AlgebraicRoot.ofEliminant?_isSome
          (raw := raw)
          (ballAt := fun prec => do
            let target := prec + (AlgebraicRoot.invGuardBits a : Int)
            let ar ← a.rep.refineTo? target
            ar.1.1.square.toBall.inv? target)
          (z := a.toComplex⁻¹) hraw hroot ball
        · dsimp only
          rw [har]
          simp only [Option.bind_eq_bind, Option.bind_some]
          simpa only [AlgebraicRoot.invGuardBits] using hinv
        · apply DyadicComplexBall.inv_mem (h := hinv)
          have harRoot :
              HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
            exact (HexRootsMathlib.RefinedIsolation.refineTo_root
              a.rep _ .nkThenPellet har).trans rfl
          rw [← harRoot]
          exact DyadicComplexBall.mem_toBall
            (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
        · have hshift :
              (2 : ℝ) ^ (-((separationDepth
                  (ZPoly.squareFreeCore raw) : Int) + 4)) ≤
                (2 : ℝ) ^ (-(separationDepth
                  (ZPoly.squareFreeCore raw) : Int)) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hsepNat :
              mahlerPrec (ZPoly.squareFreeCore raw) ≤
                separationDepth (ZPoly.squareFreeCore raw) := by
            rw [separationDepth]
            omega
          have hsepInt :
              (mahlerPrec (ZPoly.squareFreeCore raw) : Int) ≤
                (separationDepth (ZPoly.squareFreeCore raw) : Int) := by
            exact_mod_cast hsepNat
          have hpow :
              (2 : ℝ) ^ (-(separationDepth
                  (ZPoly.squareFreeCore raw) : Int)) ≤
                (2 : ℝ) ^ (-(mahlerPrec
                  (ZPoly.squareFreeCore raw) : Int)) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          exact hguardRadius.trans (hshift.trans hpow)

/-- Total lazy inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicRoot) :
    a.inv.toComplex = a.toComplex⁻¹ := by
  cases h : a.inv? with
  | none =>
      have hsome := inv?_isSome a
      simp [h] at hsome
  | some b =>
      simpa [AlgebraicRoot.inv, h] using inv?_sound a h

/-- A certified lazy quotient denotes the quotient of its inputs. -/
theorem div?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.div? b = some c) :
    c.toComplex = a.toComplex / b.toComplex := by
  cases hb : b.inv? with
  | none => simp [AlgebraicRoot.div?, hb] at h
  | some bInv =>
      have hmul : a.mul? bInv = some c := by
        simpa [AlgebraicRoot.div?, hb] using h
      rw [mul?_sound a bInv hmul, inv?_sound b hb]
      rfl

/-- The bounded lazy division search always finds its certificate. -/
theorem div?_isSome (a b : AlgebraicRoot) :
    (a.div? b).isSome := by
  cases hb : b.inv? with
  | none =>
      have hsome := inv?_isSome b
      simp [hb] at hsome
  | some bInv =>
      simpa [AlgebraicRoot.div?, hb] using mul?_isSome a bInv

/-- Total lazy division computes complex division. -/
theorem div_toComplex (a b : AlgebraicRoot) :
    (a.div b).toComplex = a.toComplex / b.toComplex := by
  cases h : a.div? b with
  | none =>
      have hsome := div?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.div, h] using div?_sound a b h

end AlgebraicRoot

namespace AlgebraicNumber

/-- Canonical addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicNumber) :
    (a + b).toComplex = a.toComplex + b.toComplex := by
  change (AlgebraicNumber.add a b).toComplex = _
  rw [AlgebraicNumber.add]
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.add_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicNumber) :
    (a - b).toComplex = a.toComplex - b.toComplex := by
  change (AlgebraicNumber.sub a b).toComplex = _
  rw [AlgebraicNumber.sub]
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.sub_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicNumber) :
    (a * b).toComplex = a.toComplex * b.toComplex := by
  change (AlgebraicNumber.mul a b).toComplex = _
  rw [AlgebraicNumber.mul]
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.mul_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical negation computes complex negation. -/
theorem neg_toComplex (a : AlgebraicNumber) :
    (-a).toComplex = -a.toComplex := by
  change (AlgebraicNumber.neg a).toComplex = _
  rw [AlgebraicNumber.neg]
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.neg_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicNumber) :
    a⁻¹.toComplex = a.toComplex⁻¹ := by
  change (AlgebraicNumber.inv a).toComplex = _
  rw [AlgebraicNumber.inv]
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.inv_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical division computes complex division. -/
theorem div_toComplex (a b : AlgebraicNumber) :
    (a / b).toComplex = a.toComplex / b.toComplex := by
  change (AlgebraicNumber.div a b).toComplex = _
  rw [AlgebraicNumber.div]
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.div_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

end AlgebraicNumber

/-! The lazy arithmetic totality headlines must not inherit unfinished proofs. -/

/--
info: 'Hex.AlgebraicRoot.add?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicRoot.add?_isSome

/--
info: 'Hex.AlgebraicRoot.mul?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicRoot.mul?_isSome

/--
info: 'Hex.AlgebraicRoot.inv?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicRoot.inv?_isSome

/--
info: 'Hex.AlgebraicRoot.div?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicRoot.div?_isSome

/--
info: 'Hex.AlgebraicNumber.add_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicNumber.add_toComplex

/--
info: 'Hex.AlgebraicNumber.div_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicNumber.div_toComplex

end

end Hex
