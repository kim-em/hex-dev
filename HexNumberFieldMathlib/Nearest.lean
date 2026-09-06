/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.IntegerRoots

public section

/-!
The exact primitives of `HexNumberField/Nearest.lean` do what their names say:
`I` is the imaginary unit, `conj` is complex conjugation, and `realCompare`
orders real algebraic numbers. Each proof is the same argument: at
`separationPrec` the approximation balls of two distinct roots of one
polynomial are disjoint, because `mahlerPrec` separates the roots by more
than four radii, so a ball that meets a given point's ball belongs to a
unique root.
-/

open HexRootsMathlib

namespace Hex

namespace DyadicComplexBall

/-- The centre of a ball, componentwise. -/
theorem center_re (b : DyadicComplexBall) : b.center.re = Dyadic.toReal b.re :=
  GaussDyadic.toComplex_re (b.re, b.im)

theorem center_im (b : DyadicComplexBall) : b.center.im = Dyadic.toReal b.im :=
  GaussDyadic.toComplex_im (b.re, b.im)

/-- A point of a ball is within the radius of the centre. -/
theorem dist_le_of_mem {b : DyadicComplexBall} {z : ℂ} (h : z ∈ b.set) :
    dist z b.center ≤ b.realRadius :=
  Metric.mem_closedBall.mp h

/-- A ball with a point has nonnegative radius. -/
theorem radius_nonneg_of_mem {b : DyadicComplexBall} {z : ℂ} (h : z ∈ b.set) :
    0 ≤ b.realRadius :=
  dist_nonneg.trans (dist_le_of_mem h)

/-- Two balls with a common point meet. -/
theorem meets_of_mem_set {b₁ b₂ : DyadicComplexBall} {z : ℂ}
    (h₁ : z ∈ b₁.set) (h₂ : z ∈ b₂.set) : b₁.meets b₂ = true := by
  unfold meets
  rw [decide_eq_true_eq, ← Dyadic.toReal_le_toReal_iff, Dyadic.toReal_mul,
    Dyadic.toReal_add, DyadicSquare.toReal_distSq]
  have h₁' := dist_le_of_mem h₁
  have h₂' := dist_le_of_mem h₂
  have htri : dist b₁.center b₂.center ≤ b₁.realRadius + b₂.realRadius := by
    calc dist b₁.center b₂.center ≤ dist b₁.center z + dist z b₂.center := dist_triangle _ _ _
      _ ≤ b₁.realRadius + b₂.realRadius := by rw [dist_comm b₁.center z]; exact add_le_add h₁' h₂'
  have hnn : 0 ≤ b₁.realRadius + b₂.realRadius :=
    add_nonneg (radius_nonneg_of_mem h₁) (radius_nonneg_of_mem h₂)
  change dist b₁.center b₂.center ^ 2 ≤ (b₁.realRadius + b₂.realRadius) * (b₁.realRadius + b₂.realRadius)
  rw [← sq]
  exact pow_le_pow_left₀ dist_nonneg htri 2

/-- Points of two balls that meet are within twice the radius sum of each other. -/
theorem dist_le_of_meets {b₁ b₂ : DyadicComplexBall} {z w : ℂ}
    (h : b₁.meets b₂ = true) (hz : z ∈ b₁.set) (hw : w ∈ b₂.set) :
    dist z w ≤ 2 * (b₁.realRadius + b₂.realRadius) := by
  unfold meets at h
  rw [decide_eq_true_eq, ← Dyadic.toReal_le_toReal_iff, Dyadic.toReal_mul,
    Dyadic.toReal_add, DyadicSquare.toReal_distSq] at h
  have hnn : 0 ≤ b₁.realRadius + b₂.realRadius :=
    add_nonneg (radius_nonneg_of_mem hz) (radius_nonneg_of_mem hw)
  have hcenters : dist b₁.center b₂.center ≤ b₁.realRadius + b₂.realRadius := by
    change dist b₁.center b₂.center ^ 2 ≤ (b₁.realRadius + b₂.realRadius) * (b₁.realRadius + b₂.realRadius) at h
    rw [← sq] at h
    exact pow_le_pow_iff_left₀ dist_nonneg hnn (by norm_num) |>.mp h
  calc dist z w ≤ dist z b₁.center + dist b₁.center b₂.center + dist b₂.center w :=
        dist_triangle4 _ _ _ _
    _ ≤ b₁.realRadius + (b₁.realRadius + b₂.realRadius) + b₂.realRadius := by
        have := dist_le_of_mem hz
        have := dist_le_of_mem hw
        rw [dist_comm b₂.center w]
        linarith
    _ = 2 * (b₁.realRadius + b₂.realRadius) := by ring

end DyadicComplexBall

namespace AlgebraicNumber

/-- The mirror ball contains the conjugates of the ball's points. -/
theorem conj_mem_mirrorBall {b : DyadicComplexBall} {z : ℂ} (h : z ∈ b.set) :
    starRingEnd ℂ z ∈ (mirrorBall b).set := by
  have hre : (mirrorBall b).re = b.re := rfl
  have him : (mirrorBall b).im = -b.im := rfl
  have hcenter : (mirrorBall b).center = starRingEnd ℂ b.center := by
    apply Complex.ext
    · rw [DyadicComplexBall.center_re, Complex.conj_re, DyadicComplexBall.center_re, hre]
    · rw [DyadicComplexBall.center_im, Complex.conj_im, DyadicComplexBall.center_im, him,
        Dyadic.toReal_neg]
  have hradius : (mirrorBall b).realRadius = b.realRadius := rfl
  rw [DyadicComplexBall.set, Metric.mem_closedBall, hcenter, hradius, Complex.dist_conj_conj]
  exact DyadicComplexBall.dist_le_of_mem h

/-- At `separationPrec p`, the ball radius is at most a quarter of the
separation guaranteed by `mahlerPrec p`, in the form the proofs use. -/
theorem approx_radius_separationPrec (a : AlgebraicNumber) (p : ZPoly) :
    (a.approx (separationPrec p)).realRadius ≤ (2 : ℝ) ^ (-(mahlerPrec p : ℤ)) / 4 := by
  have h := approx_radius a (separationPrec p)
  have : (2 : ℝ) ^ (-(separationPrec p)) = (2 : ℝ) ^ (-(mahlerPrec p : ℤ)) / 4 := by
    unfold separationPrec
    rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  rw [this] at h
  exact h

/-- Two roots of `p` whose balls at `separationPrec p` meet are equal. -/
theorem eq_of_meets {p : ZPoly} (hp : p ≠ 0) {a b : AlgebraicNumber}
    (ha : (toPolyℂ p).IsRoot a.toComplex) (hb : (toPolyℂ p).IsRoot b.toComplex)
    {ballA ballB : DyadicComplexBall}
    (hA : a.toComplex ∈ ballA.set) (hB : b.toComplex ∈ ballB.set)
    (hrA : ballA.realRadius ≤ (2 : ℝ) ^ (-(mahlerPrec p : ℤ)) / 4)
    (hrB : ballB.realRadius ≤ (2 : ℝ) ^ (-(mahlerPrec p : ℤ)) / 4)
    (hmeets : ballA.meets ballB = true) : a.toComplex = b.toComplex := by
  by_contra hne
  have hsep := mahlerPrec_separates p hp _ _ ha hb hne
  have hclose := DyadicComplexBall.dist_le_of_meets hmeets hA hB
  rw [dist_eq_norm] at hclose
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(mahlerPrec p : ℤ)) := zpow_pos (by norm_num) _
  linarith

end AlgebraicNumber

end Hex

namespace Hex.AlgebraicNumber

open HexRootsMathlib Polynomial

/-- `conj` is complex conjugation. -/
theorem conj_toComplex (a : AlgebraicNumber) :
    a.conj.toComplex = starRingEnd ℂ a.toComplex := by
  unfold conj
  split
  · rename_i hreal
    exact (Complex.conj_eq_iff_im.mpr ((isReal_iff a).mp hreal)).symm
  · rename_i hreal
    have hpne : a.p ≠ 0 := RefinedIsolation.poly_ne_zero a.rep
    have hroot : (toPolyℂ a.p).IsRoot a.toComplex := RefinedIsolation.isRoot a.rep
    have hconj := isRoot_conj hroot
    obtain ⟨c, hcmem, hcval⟩ := (ZPoly.mem_algebraicRoots_iff a.p hpne _).mpr hconj
    have hconjmem : starRingEnd ℂ a.toComplex ∈
        (mirrorBall (a.approx (separationPrec a.p))).set :=
      conj_mem_mirrorBall (approx_mem a (separationPrec a.p))
    have hpredc : (c.approx (separationPrec a.p)).meets
        (mirrorBall (a.approx (separationPrec a.p))) = true :=
      DyadicComplexBall.meets_of_mem_set (z := starRingEnd ℂ a.toComplex)
        (hcval ▸ approx_mem c (separationPrec a.p)) hconjmem
    have hsome : ((ZPoly.algebraicRoots a.p).find? fun c =>
        (c.approx (separationPrec a.p)).meets
          (mirrorBall (a.approx (separationPrec a.p)))).isSome = true :=
      Array.find?_isSome.mpr ⟨c, by simpa using hcmem, hpredc⟩
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hsome
    show (((ZPoly.algebraicRoots a.p).find? fun c =>
        (c.approx (separationPrec a.p)).meets
          (mirrorBall (a.approx (separationPrec a.p)))).getD _).toComplex = _
    rw [hc', Option.getD_some]
    have hmem' : c' ∈ ZPoly.algebraicRoots a.p := Array.mem_of_find?_eq_some hc'
    have hpred' := Array.find?_some hc'
    have hroot' : (toPolyℂ a.p).IsRoot c'.toComplex :=
      (ZPoly.mem_algebraicRoots_iff a.p hpne _).mp ⟨c', by simpa using hmem', rfl⟩
    have hrootc : (toPolyℂ a.p).IsRoot c.toComplex := hcval ▸ hconj
    have hcmirror : c.toComplex ∈ (mirrorBall (a.approx (separationPrec a.p))).set :=
      hcval ▸ hconjmem
    have := eq_of_meets hpne hroot' hrootc (approx_mem c' (separationPrec a.p)) hcmirror
      (approx_radius_separationPrec c' a.p) (approx_radius_separationPrec a a.p) hpred'
    exact this.trans hcval

/-- A root of the product of two minimal polynomials. -/
theorem isRoot_mul_left (a b : AlgebraicNumber) :
    (toPolyℂ (a.p * b.p)).IsRoot a.toComplex := by
  show ((HexPolyZMathlib.toPolynomial (a.p * b.p)).map (Int.castRingHom ℂ)).IsRoot _
  rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul]
  exact root_mul_right_of_isRoot _ (RefinedIsolation.isRoot a.rep)

theorem isRoot_mul_right (a b : AlgebraicNumber) :
    (toPolyℂ (a.p * b.p)).IsRoot b.toComplex := by
  show ((HexPolyZMathlib.toPolynomial (a.p * b.p)).map (Int.castRingHom ℂ)).IsRoot _
  rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul]
  exact root_mul_left_of_isRoot _ (RefinedIsolation.isRoot b.rep)

/-- The product of two minimal polynomials is nonzero. -/
theorem mul_p_ne_zero (a b : AlgebraicNumber) : a.p * b.p ≠ 0 := by
  intro h
  have ha : toPolyℂ a.p ≠ 0 := toPolyℂ_ne_zero a.p (by
    intro hsize
    exact RefinedIsolation.poly_ne_zero a.rep ((DensePoly.size_eq_zero_iff _).mp hsize))
  have hb : toPolyℂ b.p ≠ 0 := toPolyℂ_ne_zero b.p (by
    intro hsize
    exact RefinedIsolation.poly_ne_zero b.rep ((DensePoly.size_eq_zero_iff _).mp hsize))
  have hprod : toPolyℂ (a.p * b.p) = toPolyℂ a.p * toPolyℂ b.p := by
    show (HexPolyZMathlib.toPolynomial (a.p * b.p)).map (Int.castRingHom ℂ) = _
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul]
  rw [h] at hprod
  have : toPolyℂ (0 : ZPoly) = 0 := by
    ext n
    simp
  rw [this] at hprod
  exact mul_ne_zero ha hb hprod.symm

/-- The real part of a number is within the ball radius of the centre's. -/
theorem abs_re_sub_center_le (a : AlgebraicNumber) (prec : Int) :
    |a.toComplex.re - Dyadic.toReal (a.approx prec).re| ≤ (a.approx prec).realRadius := by
  have h := DyadicComplexBall.dist_le_of_mem (approx_mem a prec)
  rw [dist_eq_norm] at h
  have h' := Complex.abs_re_le_norm (a.toComplex - (a.approx prec).center)
  rw [Complex.sub_re, DyadicComplexBall.center_re] at h'
  exact h'.trans h

/-- `realCompare` is the order of the real parts. -/
theorem realCompare_eq (a b : AlgebraicNumber) (ha : a.isReal = true)
    (hb : b.isReal = true) :
    a.realCompare b = compare a.toComplex.re b.toComplex.re := by
  unfold realCompare
  split
  · rename_i heq
    rw [(beq_iff a b).mp heq]
    exact (compare_eq_iff_eq.mpr rfl).symm
  · rename_i hne
    have hne' : a.toComplex ≠ b.toComplex := fun h => hne ((beq_iff a b).mpr h)
    have haim := (isReal_iff a).mp ha
    have hbim := (isReal_iff b).mp hb
    have hsep := mahlerPrec_separates (a.p * b.p) (mul_p_ne_zero a b) _ _
      (isRoot_mul_left a b) (isRoot_mul_right a b) hne'
    have hnorm : ‖a.toComplex - b.toComplex‖ = |a.toComplex.re - b.toComplex.re| := by
      have : a.toComplex - b.toComplex = ((a.toComplex.re - b.toComplex.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [haim, hbim]
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hsep
    have hdA := (abs_re_sub_center_le a (separationPrec (a.p * b.p))).trans
      (approx_radius_separationPrec a (a.p * b.p))
    have hdB := (abs_re_sub_center_le b (separationPrec (a.p * b.p))).trans
      (approx_radius_separationPrec b (a.p * b.p))
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(mahlerPrec (a.p * b.p) : ℤ)) := zpow_pos (by norm_num) _
    rw [abs_le] at hdA hdB
    show (if (a.approx (separationPrec (a.p * b.p))).re < (b.approx (separationPrec (a.p * b.p))).re
        then Ordering.lt else Ordering.gt) = _
    split
    · rename_i hlt
      have hlt' := Dyadic.toReal_lt_toReal_iff.mpr hlt
      symm
      rw [compare_lt_iff_lt]
      by_contra hge
      push_neg at hge
      rw [abs_of_nonneg (by linarith)] at hsep
      linarith
    · rename_i hnlt
      have hge' : Dyadic.toReal (b.approx (separationPrec (a.p * b.p))).re ≤
          Dyadic.toReal (a.approx (separationPrec (a.p * b.p))).re :=
        not_lt.mp fun h => hnlt (Dyadic.toReal_lt_toReal_iff.mp h)
      symm
      rw [compare_gt_iff_gt]
      by_contra hle
      push_neg at hle
      rw [abs_of_nonpos (by linarith)] at hsep
      linarith

/-- The complex interpretation of `X² + 1`. -/
theorem toPolyℂ_xsq_add_one : toPolyℂ #p[1, 0, 1] = X ^ 2 + 1 := by
  ext n
  rw [coeff_toPolyℂ, coeff_add, coeff_X_pow, coeff_one]
  have h0 : (#p[1, 0, 1] : ZPoly).coeff 0 = 1 := by decide
  have h1 : (#p[1, 0, 1] : ZPoly).coeff 1 = 0 := by decide
  have h2 : (#p[1, 0, 1] : ZPoly).coeff 2 = 1 := by decide
  have hsize : (#p[1, 0, 1] : ZPoly).size = 3 := by decide
  rcases n with _ | _ | _ | n
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega)]
    simp <;> rfl

/-- `mahlerPrec` is at least three. -/
theorem three_le_mahlerPrec (p : ZPoly) : 3 ≤ mahlerPrec p :=
  Nat.le_add_right 3 _

/-- A root of `X² + 1` has a stored isolation centre in the upper half plane
exactly when it is the imaginary unit. -/
theorem square_im_pos_iff {d : AlgebraicNumber}
    (hd : d ∈ ZPoly.algebraicRoots #p[1, 0, 1]) :
    0 < d.rep.1.square.im ↔ d.toComplex = Complex.I := by
  have hp : (#p[1, 0, 1] : ZPoly) ≠ 0 := by decide
  have hroot : (toPolyℂ #p[1, 0, 1]).IsRoot d.toComplex :=
    (ZPoly.mem_algebraicRoots_iff _ hp _).mp ⟨d, by simpa using hd, rfl⟩
  rw [toPolyℂ_xsq_add_one] at hroot
  have hsq : d.toComplex ^ 2 = Complex.I ^ 2 := by
    rw [Complex.I_sq]
    have := hroot
    simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at this
    linear_combination this
  have hcases := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  set s := d.rep.1.square with hs
  have hmem : d.toComplex ∈ HexRootsMathlib.DyadicSquare.closedDisc s :=
    RefinedIsolation.root_mem_closedDisc d.rep
  have hdist : dist d.toComplex (HexRootsMathlib.DyadicSquare.center s) ≤
      HexRootsMathlib.DyadicSquare.radius s := by
    simpa only [HexRootsMathlib.DyadicSquare.closedDisc, Metric.mem_closedBall] using hmem
  have hcenter : (HexRootsMathlib.DyadicSquare.center s).im = Dyadic.toReal s.im := by
    simp [HexRootsMathlib.DyadicSquare.center_eq, Hex.DyadicSquare.center]
  have himDist : |d.toComplex.im - Dyadic.toReal s.im| ≤
      HexRootsMathlib.DyadicSquare.radius s := by
    have h := Complex.abs_im_le_norm (d.toComplex - HexRootsMathlib.DyadicSquare.center s)
    rw [Complex.sub_im, hcenter] at h
    rw [dist_eq_norm] at hdist
    exact h.trans hdist
  have hrad : HexRootsMathlib.DyadicSquare.radius s < 1 / 4 := by
    rw [HexRootsMathlib.DyadicSquare.radius_eq]
    have hprec : (3 : ℤ) ≤ s.prec := by
      have := d.rep.property
      have := three_le_mahlerPrec d.p
      rw [← hs] at *
      omega
    have h2 : (2 : ℝ) ^ (-s.prec) ≤ (2 : ℝ) ^ (-(3 : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hsqrt : √2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-s.prec) := zpow_pos (by norm_num) _
    calc (2 : ℝ) ^ (-s.prec) * √2 < (2 : ℝ) ^ (-s.prec) * 2 :=
          mul_lt_mul_of_pos_left hsqrt hpos
      _ ≤ (2 : ℝ) ^ (-(3 : ℤ)) * 2 := by gcongr
      _ = 1 / 4 := by norm_num
  rw [← Dyadic.toReal_lt_toReal_iff, Dyadic.toReal_zero]
  rw [abs_le] at himDist
  rcases hcases with h | h
  · rw [h] at himDist ⊢
    simp only [Complex.I_im] at himDist
    exact ⟨fun _ => rfl, fun _ => by linarith⟩
  · rw [h] at himDist ⊢
    simp only [Complex.neg_im, Complex.I_im] at himDist
    constructor
    · intro hlt
      linarith
    · intro heq
      have : Complex.I = -Complex.I := heq.symm
      have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination this
      simp at h2

/-- `I` is the imaginary unit. -/
theorem I_toComplex : I.toComplex = Complex.I := by
  unfold I
  have hp : (#p[1, 0, 1] : ZPoly) ≠ 0 := by decide
  have hrootI : (toPolyℂ #p[1, 0, 1]).IsRoot Complex.I := by
    rw [toPolyℂ_xsq_add_one]
    simp [IsRoot.def, Complex.I_sq]
  obtain ⟨c, hcmem, hcval⟩ := (ZPoly.mem_algebraicRoots_iff _ hp _).mpr hrootI
  have hcmem' : c ∈ ZPoly.algebraicRoots #p[1, 0, 1] := by simpa using hcmem
  have hsome : ((ZPoly.algebraicRoots #p[1, 0, 1]).find? fun a =>
      0 < a.rep.1.square.im).isSome = true :=
    Array.find?_isSome.mpr ⟨c, hcmem', decide_eq_true ((square_im_pos_iff hcmem').mpr hcval)⟩
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hsome
  rw [hc', Option.getD_some]
  have hmem' := Array.mem_of_find?_eq_some hc'
  have hpred := Array.find?_some hc'
  exact (square_im_pos_iff hmem').mp (of_decide_eq_true hpred)

/--
info: 'Hex.AlgebraicNumber.I_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms I_toComplex

/--
info: 'Hex.AlgebraicNumber.conj_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms conj_toComplex

/--
info: 'Hex.AlgebraicNumber.realCompare_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms realCompare_eq

end Hex.AlgebraicNumber
