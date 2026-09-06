/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.IntegerRoots
public import HexNumberFieldMathlib.Lazy
public import HexNumberFieldMathlib.Field

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
      have hge' := not_lt.mp hge
      rw [abs_of_nonneg (by linarith)] at hsep
      linarith
    · rename_i hnlt
      have hge' : Dyadic.toReal (b.approx (separationPrec (a.p * b.p))).re ≤
          Dyadic.toReal (a.approx (separationPrec (a.p * b.p))).re :=
        not_lt.mp fun h => hnlt (Dyadic.toReal_lt_toReal_iff.mp h)
      symm
      rw [compare_gt_iff_gt]
      by_contra hle
      have hle' := not_lt.mp hle
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
    (simp; rfl)

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

namespace Hex.AlgebraicNumber

open HexRootsMathlib

/-- The complex value of a rational point. -/
theorem ofPoint_toComplex (re im : Rat) :
    (ofPoint re im).toComplex = (re : ℂ) + (im : ℂ) * Complex.I := by
  unfold ofPoint
  rw [add_toComplex, mul_toComplex, ofRat_toComplex, ofRat_toComplex, I_toComplex]

/-- The conjugate of a rational point. -/
theorem ofPoint_neg_toComplex (re im : Rat) :
    (ofPoint re (-im)).toComplex = starRingEnd ℂ ((re : ℂ) + (im : ℂ) * Complex.I) := by
  rw [ofPoint_toComplex]
  apply Complex.ext <;> simp

/-- `distSqTo` is the squared distance to the point. -/
theorem distSqTo_toComplex (a : AlgebraicNumber) (re im : Rat) :
    (a.distSqTo re im).toComplex =
      ((‖a.toComplex - ((re : ℂ) + (im : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  unfold distSqTo
  rw [mul_toComplex, sub_toComplex, sub_toComplex, conj_toComplex, ofPoint_toComplex,
    ofPoint_neg_toComplex, ← map_sub, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `distSqTo` is real. -/
theorem distSqTo_isReal (a : AlgebraicNumber) (re im : Rat) :
    (a.distSqTo re im).isReal = true := by
  rw [isReal_iff, distSqTo_toComplex, Complex.ofReal_im]

end Hex.AlgebraicNumber

namespace Hex.AlgebraicNumber

open HexRootsMathlib

/-- The point named by two rationals. -/
noncomputable abbrev point (re im : Rat) : ℂ := (re : ℂ) + (im : ℂ) * Complex.I

theorem absRat_cast (q : Rat) : ((absRat q : Rat) : ℝ) = |(q : ℝ)| := by
  unfold absRat
  split
  · rename_i h
    rw [abs_of_neg (by exact_mod_cast h)]
    push_cast
    ring
  · rename_i h
    rw [abs_of_nonneg (by exact_mod_cast not_lt.mp h)]

/-- The squared distance from the point to the centre, as a real. -/
theorem ballDistSq_cast (b : DyadicComplexBall) (re im : Rat) :
    ((ballDistSq b re im : Rat) : ℝ) = ‖b.center - point re im‖ ^ 2 := by
  unfold ballDistSq
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    DyadicComplexBall.center_re, DyadicComplexBall.center_im]
  simp only [point, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Dyadic.toReal, Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  ring

/-- The centre distance is at most the coordinate bound. -/
theorem norm_center_sub_le (b : DyadicComplexBall) (re im : Rat) :
    ‖b.center - point re im‖ ≤ ((ballDistBound b re im : Rat) : ℝ) := by
  unfold ballDistBound
  push_cast
  rw [absRat_cast, absRat_cast]
  have h := Complex.norm_le_abs_re_add_abs_im (b.center - point re im)
  rw [Complex.sub_re, Complex.sub_im, DyadicComplexBall.center_re,
    DyadicComplexBall.center_im] at h
  simp only [point, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Dyadic.toReal, Complex.ratCast_re, Complex.ratCast_im] at h
  push_cast
  simpa using h

theorem realRadius_eq (b : DyadicComplexBall) : b.realRadius = ((b.radius.toRat : Rat) : ℝ) :=
  rfl

/-- The squared distance from the point to any point of a ball is at most
`ballUpper`. -/
theorem sq_norm_le_ballUpper {b : DyadicComplexBall} {z : ℂ} (hz : z ∈ b.set)
    (re im : Rat) :
    ‖z - point re im‖ ^ 2 ≤ ((ballUpper b re im : Rat) : ℝ) := by
  unfold ballUpper
  push_cast
  rw [ballDistSq_cast, ← realRadius_eq]
  have hr := DyadicComplexBall.radius_nonneg_of_mem hz
  have hzc := DyadicComplexBall.dist_le_of_mem hz
  rw [dist_eq_norm] at hzc
  have hl := norm_center_sub_le b re im
  have htri : ‖z - point re im‖ ≤ ‖b.center - point re im‖ + b.realRadius := by
    calc ‖z - point re im‖ = ‖(z - b.center) + (b.center - point re im)‖ := by ring_nf
      _ ≤ ‖z - b.center‖ + ‖b.center - point re im‖ := norm_add_le _ _
      _ ≤ b.realRadius + ‖b.center - point re im‖ := by linarith
      _ = _ := by ring
  have hnn : 0 ≤ ‖b.center - point re im‖ + b.realRadius := by positivity
  calc ‖z - point re im‖ ^ 2 ≤ (‖b.center - point re im‖ + b.realRadius) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ = ‖b.center - point re im‖ ^ 2 + 2 * b.realRadius * ‖b.center - point re im‖ +
        b.realRadius * b.realRadius := by ring
    _ ≤ ‖b.center - point re im‖ ^ 2 + 2 * b.realRadius * ((ballDistBound b re im : Rat) : ℝ) +
        b.realRadius * b.realRadius := by
        have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 2 * b.realRadius)
        linarith

/-- The squared distance from the point to any point of a ball is at least
`ballLower`. -/
theorem ballLower_le_sq_norm {b : DyadicComplexBall} {z : ℂ} (hz : z ∈ b.set)
    (re im : Rat) :
    ((ballLower b re im : Rat) : ℝ) ≤ ‖z - point re im‖ ^ 2 := by
  show (((if b.radius.toRat * b.radius.toRat ≤ ballDistSq b re im then
      ballDistSq b re im - 2 * b.radius.toRat * ballDistBound b re im +
        b.radius.toRat * b.radius.toRat
    else 0 : Rat)) : ℝ) ≤ _
  split
  · rename_i hfar
    push_cast
    rw [ballDistSq_cast, ← realRadius_eq]
    have hfar' : b.realRadius ^ 2 ≤ ‖b.center - point re im‖ ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hfar
      push_cast at this
      rw [ballDistSq_cast, ← realRadius_eq] at this
      linarith [sq b.realRadius]
    have hr := DyadicComplexBall.radius_nonneg_of_mem hz
    have hrle : b.realRadius ≤ ‖b.center - point re im‖ :=
      pow_le_pow_iff_left₀ hr (norm_nonneg _) (by norm_num) |>.mp hfar'
    have hzc := DyadicComplexBall.dist_le_of_mem hz
    rw [dist_eq_norm] at hzc
    have hl := norm_center_sub_le b re im
    have hrev : ‖b.center - point re im‖ - b.realRadius ≤ ‖z - point re im‖ := by
      have := norm_sub_norm_le (b.center - point re im) (b.center - z)
      have heq : b.center - point re im - (b.center - z) = z - point re im := by ring
      rw [heq, norm_sub_rev b.center z] at this
      linarith
    have hnn : 0 ≤ ‖b.center - point re im‖ - b.realRadius := by linarith
    calc ‖b.center - point re im‖ ^ 2 - 2 * b.realRadius * ((ballDistBound b re im : Rat) : ℝ) +
          b.realRadius * b.realRadius
        ≤ ‖b.center - point re im‖ ^ 2 - 2 * b.realRadius * ‖b.center - point re im‖ +
          b.realRadius * b.realRadius := by
          have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 2 * b.realRadius)
          linarith
      _ = (‖b.center - point re im‖ - b.realRadius) ^ 2 := by ring
      _ ≤ ‖z - point re im‖ ^ 2 := pow_le_pow_left₀ hnn hrev 2
  · push_cast
    positivity

end Hex.AlgebraicNumber

namespace Hex.AlgebraicNumber

open HexRootsMathlib

/-- The exact comparison of squared distances decides the strict order of
distances. -/
theorem realCompare_distSqTo_lt (c b : AlgebraicNumber) (re im : Rat) :
    ((c.distSqTo re im).realCompare (b.distSqTo re im) == .lt) = true ↔
      ‖c.toComplex - point re im‖ < ‖b.toComplex - point re im‖ := by
  rw [beq_iff_eq, realCompare_eq _ _ (distSqTo_isReal c re im) (distSqTo_isReal b re im),
    compare_lt_iff_lt, distSqTo_toComplex, distSqTo_toComplex, Complex.ofReal_re,
    Complex.ofReal_re]
  exact pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)

/-- A certified nearest root is nearest. -/
theorem certifiedNearest_sound {roots : Array AlgebraicNumber} {a : AlgebraicNumber}
    {prec : Int} {re im : Rat} (h : certifiedNearest roots a prec re im = true) :
    ∀ c ∈ roots, ‖a.toComplex - point re im‖ ≤ ‖c.toComplex - point re im‖ := by
  intro c hc
  unfold certifiedNearest at h
  have hc' := (Array.all_eq_true_iff_forall_mem.mp h) c hc
  rw [Bool.or_eq_true] at hc'
  rcases hc' with heq | hlt
  · rw [(beq_iff c a).mp heq]
  · rw [decide_eq_true_eq] at hlt
    have hlt' := (Rat.cast_lt (K := ℝ)).mpr hlt
    have hupper := sq_norm_le_ballUpper (approx_mem a prec) re im
    have hlower := ballLower_le_sq_norm (approx_mem c prec) re im
    have hsq : ‖a.toComplex - point re im‖ ^ 2 < ‖c.toComplex - point re im‖ ^ 2 := by
      linarith
    exact le_of_lt ((pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      (by norm_num)).mp hsq)

theorem exactStep_none (re im : Rat) (c : AlgebraicNumber) :
    exactStep re im none c = some c := rfl

theorem exactStep_some (re im : Rat) (b c : AlgebraicNumber) :
    exactStep re im (some b) c =
      if (c.distSqTo re im).realCompare (b.distSqTo re im) == .lt then some c
      else some b := rfl

/-- The fold behind `exactNearest`, on lists. -/
theorem foldl_exactStep (re im : Rat) :
    ∀ (l : List AlgebraicNumber) (acc : Option AlgebraicNumber),
      match l.foldl (exactStep re im) acc with
      | none => l = [] ∧ acc = none
      | some r => (r ∈ l ∨ acc = some r) ∧
          (∀ c ∈ l, ‖r.toComplex - point re im‖ ≤ ‖c.toComplex - point re im‖) ∧
          (∀ b, acc = some b → ‖r.toComplex - point re im‖ ≤ ‖b.toComplex - point re im‖) := by
  intro l
  induction l with
  | nil =>
    intro acc
    cases acc with
    | none => exact ⟨rfl, rfl⟩
    | some b =>
      refine ⟨Or.inr rfl, fun c hc => absurd hc List.not_mem_nil, fun b' hb' => ?_⟩
      cases hb'
      exact le_rfl
  | cons c rest ih =>
    intro acc
    rw [List.foldl_cons]
    cases acc with
    | none =>
      rw [exactStep_none]
      have := ih (some c)
      revert this
      generalize rest.foldl (exactStep re im) (some c) = result
      intro this
      cases result with
      | none => exact absurd this.2 (by simp)
      | some r =>
        obtain ⟨hmem, hall, hacc⟩ := this
        refine ⟨?_, ?_, fun b hb => by cases hb⟩
        · rcases hmem with hmem | hmem
          · exact Or.inl (List.mem_cons_of_mem _ hmem)
          · exact Or.inl (Option.some.inj hmem ▸ List.mem_cons_self)
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hacc _ rfl
          · exact hall d hd
    | some b =>
      rw [exactStep_some]
      by_cases hlt : ((c.distSqTo re im).realCompare (b.distSqTo re im) == .lt) = true
      · rw [ite_eq_left hlt]
        have := ih (some c)
        revert this
        generalize rest.foldl (exactStep re im) (some c) = result
        intro this
        cases result with
        | none => exact absurd this.2 (by simp)
        | some r =>
          obtain ⟨hmem, hall, hacc⟩ := this
          have hcb := (realCompare_distSqTo_lt c b re im).mp hlt
          refine ⟨?_, ?_, ?_⟩
          · rcases hmem with hmem | hmem
            · exact Or.inl (List.mem_cons_of_mem _ hmem)
            · exact Or.inl (Option.some.inj hmem ▸ List.mem_cons_self)
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hacc _ rfl
            · exact hall d hd
          · intro b' hb'
            cases hb'
            exact (hacc _ rfl).trans (le_of_lt hcb)
      · rw [ite_eq_right hlt]
        have := ih (some b)
        revert this
        generalize rest.foldl (exactStep re im) (some b) = result
        intro this
        cases result with
        | none => exact absurd this.2 (by simp)
        | some r =>
          obtain ⟨hmem, hall, hacc⟩ := this
          have hbc : ‖b.toComplex - point re im‖ ≤ ‖c.toComplex - point re im‖ :=
            not_lt.mp fun h => hlt ((realCompare_distSqTo_lt c b re im).mpr h)
          refine ⟨?_, ?_, ?_⟩
          · rcases hmem with hmem | hmem
            · exact Or.inl (List.mem_cons_of_mem _ hmem)
            · exact Or.inr hmem
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact (hacc _ rfl).trans hbc
            · exact hall d hd
          · exact hacc

/-- `exactNearest` on a nonempty array is a nearest root. -/
theorem exactNearest_spec (roots : Array AlgebraicNumber) (re im : Rat) :
    match exactNearest roots re im with
    | none => roots = #[]
    | some r => r ∈ roots ∧
        ∀ c ∈ roots, ‖r.toComplex - point re im‖ ≤ ‖c.toComplex - point re im‖ := by
  have h := foldl_exactStep re im roots.toList none
  have hfold : exactNearest roots re im = roots.toList.foldl (exactStep re im) none :=
    (Array.foldl_toList _).symm
  rw [hfold]
  revert h
  generalize roots.toList.foldl (exactStep re im) none = result
  intro h
  cases result with
  | none =>
    obtain ⟨hnil, _⟩ := h
    exact Array.toList_eq_nil_iff.mp hnil
  | some r =>
    obtain ⟨hmem, hall, _⟩ := h
    refine ⟨?_, fun c hc => hall c (Array.mem_def.mp hc)⟩
    rcases hmem with hmem | hmem
    · exact Array.mem_def.mpr hmem
    · cases hmem

end Hex.AlgebraicNumber

namespace Hex

open HexRootsMathlib

/-- A polynomial of positive degree has a root in `algebraicRoots`. -/
theorem ZPoly.algebraicRoots_ne_empty {p : ZPoly} (hp : 0 < p.degree?.getD 0) :
    p.algebraicRoots ≠ #[] := by
  have hpne : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hdeg : 0 < (toPolyℂ p).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, natDegree_toPolyℂ]
    exact hp
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  obtain ⟨a, ha, _⟩ := (ZPoly.mem_algebraicRoots_iff p hpne z).mpr hz
  intro hempty
  rw [hempty] at ha
  simp at ha

/-- `rootNear` returns a root. -/
theorem ZPoly.rootNear_mem (p : ZPoly) (hp : 0 < p.degree?.getD 0) (re im : Rat) :
    p.rootNear re im ∈ p.algebraicRoots := by
  unfold ZPoly.rootNear
  dsimp only
  split
  · next a ha => exact Array.mem_of_find?_eq_some ha
  · next _ =>
    have hspec := AlgebraicNumber.exactNearest_spec p.algebraicRoots re im
    revert hspec
    generalize AlgebraicNumber.exactNearest p.algebraicRoots re im = r
    intro hspec
    cases r with
    | none => exact absurd hspec (ZPoly.algebraicRoots_ne_empty hp)
    | some r => exact hspec.1

/-- `rootNear` is nearest. -/
theorem ZPoly.rootNear_nearest (p : ZPoly) (re im : Rat) (b : AlgebraicNumber)
    (hb : b ∈ p.algebraicRoots) :
    ‖(p.rootNear re im).toComplex - AlgebraicNumber.point re im‖ ≤
      ‖b.toComplex - AlgebraicNumber.point re im‖ := by
  unfold ZPoly.rootNear
  dsimp only
  split
  · next a ha =>
    have hcert : AlgebraicNumber.certifiedNearest p.algebraicRoots a
        (AlgebraicNumber.separationPrec p) re im = true :=
      @Array.find?_some _ (fun a => AlgebraicNumber.certifiedNearest p.algebraicRoots a
        (AlgebraicNumber.separationPrec p) re im) a p.algebraicRoots ha
    exact AlgebraicNumber.certifiedNearest_sound hcert b hb
  · next _ =>
    have hspec := AlgebraicNumber.exactNearest_spec p.algebraicRoots re im
    revert hspec
    generalize AlgebraicNumber.exactNearest p.algebraicRoots re im = r
    intro hspec
    cases r with
    | none =>
      rw [hspec] at hb
      simp at hb
    | some r => exact hspec.2 b hb

/-- A point within half the guaranteed separation of a number names it. -/
theorem ZPoly.rootNear_of_close (a : AlgebraicNumber) (re im : Rat)
    (h : ‖AlgebraicNumber.point re im - a.toComplex‖ <
      2 * ((2 : ℝ) ^ (-(mahlerPrec a.p : ℤ)) * (1449 / 1024))) :
    a.p.rootNear re im = a := by
  have hpne : a.p ≠ 0 := RefinedIsolation.poly_ne_zero a.rep
  have hamem : a ∈ a.p.algebraicRoots := by
    obtain ⟨c, hc, hcval⟩ :=
      (ZPoly.mem_algebraicRoots_iff a.p hpne a.toComplex).mpr (RefinedIsolation.isRoot a.rep)
    have := AlgebraicNumber.toComplex_injective hcval
    subst this
    exact Array.mem_def.mpr hc
  have hrmem : a.p.rootNear re im ∈ a.p.algebraicRoots :=
    ZPoly.rootNear_mem a.p a.pos_degree re im
  have hnear := ZPoly.rootNear_nearest a.p re im a hamem
  by_contra hne
  have hne' : (a.p.rootNear re im).toComplex ≠ a.toComplex :=
    fun h => hne (AlgebraicNumber.toComplex_injective h)
  have hrroot : (toPolyℂ a.p).IsRoot (a.p.rootNear re im).toComplex :=
    (ZPoly.mem_algebraicRoots_iff a.p hpne _).mp ⟨_, Array.mem_def.mp hrmem, rfl⟩
  have hsep : (2 : ℝ) ^ (-(mahlerPrec a.p : ℤ)) * (1449 / 1024) <
      ‖(a.p.rootNear re im).toComplex - a.toComplex‖ / 4 :=
    mahlerPrec_separates a.p hpne _ _ hrroot (RefinedIsolation.isRoot a.rep) hne'
  have htri := norm_sub_le_norm_sub_add_norm_sub (a.p.rootNear re im).toComplex
    (AlgebraicNumber.point re im) a.toComplex
  rw [norm_sub_rev a.toComplex] at hnear
  linarith

/--
info: 'Hex.ZPoly.rootNear_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZPoly.rootNear_mem

/--
info: 'Hex.ZPoly.rootNear_nearest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZPoly.rootNear_nearest

/--
info: 'Hex.ZPoly.rootNear_of_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZPoly.rootNear_of_close

end Hex
