/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.SoftPellet
public import HexRootsMathlib.ArgumentPrinciple
public import HexRootsMathlib.Basic
public import HexRootsMathlib.Geometry
public import HexRootsMathlib.Taylor
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Splits

public section

/-!
# Soundness of soft Pellet and Graeffe iteration

The first layer develops the polynomial Graeffe transform independently of
the executable coefficient balls.  The transform splits a polynomial into
its even and odd coefficient parts and forms `E² - X O²`.  Its roots are the
squares of the input roots, with multiplicity.
-/

open Complex Polynomial

namespace HexRootsMathlib

noncomputable section

/-- Coefficients of even powers, with exponents divided by two. -/
def graeffeEvenPart (p : ℂ[X]) : ℂ[X] := p.contract 2

/-- Coefficients of odd powers, with one `X` removed and exponents divided by
two. -/
def graeffeOddPart (p : ℂ[X]) : ℂ[X] := p.divX.contract 2

/-- One exact Graeffe transform. -/
def graeffePoly (p : ℂ[X]) : ℂ[X] :=
  graeffeEvenPart p ^ 2 - X * graeffeOddPart p ^ 2

/-- The Graeffe transform fixes the zero polynomial. -/
@[simp] theorem graeffePoly_zero : graeffePoly (0 : ℂ[X]) = 0 := by
  have hc : contract 2 (0 : ℂ[X]) = 0 := by
    simpa only [C_0] using (contract_C (R := ℂ) 2 0)
  simp [graeffePoly, graeffeEvenPart, graeffeOddPart, hc]

private theorem coeff_expand_even (p : ℂ[X]) (k : Nat) :
    (expand ℂ 2 (graeffeEvenPart p)).coeff (2 * k) = p.coeff (2 * k) := by
  calc
    _ = (graeffeEvenPart p).coeff k := coeff_expand_mul' (by omega) _ _
    _ = p.coeff (k * 2) := by rw [graeffeEvenPart, coeff_contract (by omega)]
    _ = p.coeff (2 * k) := by rw [Nat.mul_comm]

private theorem coeff_expand_even_odd (p : ℂ[X]) (k : Nat) :
    (expand ℂ 2 (graeffeEvenPart p)).coeff (2 * k + 1) = 0 := by
  rw [coeff_expand (by omega), if_neg]
  omega

private theorem coeff_expand_odd (p : ℂ[X]) (k : Nat) :
    (expand ℂ 2 (graeffeOddPart p)).coeff (2 * k) = p.coeff (2 * k + 1) := by
  calc
    _ = (graeffeOddPart p).coeff k := coeff_expand_mul' (by omega) _ _
    _ = p.divX.coeff (k * 2) := by rw [graeffeOddPart, coeff_contract (by omega)]
    _ = p.coeff (2 * k + 1) := by
      rw [coeff_divX]
      congr 1
      omega

private theorem coeff_expand_odd_odd (p : ℂ[X]) (k : Nat) :
    (expand ℂ 2 (graeffeOddPart p)).coeff (2 * k + 1) = 0 := by
  rw [coeff_expand (by omega), if_neg]
  omega

/-- Recombining the contracted even and odd parts recovers the polynomial. -/
theorem expand_graeffe_parts (p : ℂ[X]) :
    expand ℂ 2 (graeffeEvenPart p) + X * expand ℂ 2 (graeffeOddPart p) = p := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [coeff_add, coeff_expand_even]
    cases k with
    | zero => simp
    | succ k =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, coeff_X_mul,
        coeff_expand_odd_odd]
      simp
  · rw [coeff_add, coeff_expand_even_odd]
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, coeff_X_mul, coeff_expand_odd]
    simp

/-- A polynomial in `X²` is unchanged by substituting `-X`. -/
private theorem comp_neg_X_expand_two (p : ℂ[X]) :
    (expand ℂ 2 p).comp (-X) = expand ℂ 2 p := by
  simp only [expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp [pow_two, mul_comp]

/-- Defining identity for one Graeffe step:
`G(p)(X²) = p(X) p(-X)`. -/
theorem expand_graeffePoly (p : ℂ[X]) :
    expand ℂ 2 (graeffePoly p) = p * p.comp (-X) := by
  let e := expand ℂ 2 (graeffeEvenPart p)
  let o := expand ℂ 2 (graeffeOddPart p)
  have hp : e + X * o = p := expand_graeffe_parts p
  have he : e.comp (-X) = e := by
    simpa only [e] using comp_neg_X_expand_two (graeffeEvenPart p)
  have ho : o.comp (-X) = o := by
    simpa only [o] using comp_neg_X_expand_two (graeffeOddPart p)
  have hn : e - X * o = p.comp (-X) := by
    rw [← hp]
    rw [add_comp, mul_comp, X_comp, he, ho]
    ring
  calc
    expand ℂ 2 (graeffePoly p) = e ^ 2 - X ^ 2 * o ^ 2 := by
      simp [graeffePoly, e, o]
    _ = (e + X * o) * (e - X * o) := by ring
    _ = p * p.comp (-X) := by rw [hp, hn]

/-- The polynomial built directly from the squared root multiset.  The scalar
is chosen so its expansion has the same leading coefficient as
`p(X) p(-X)`. -/
private def squaredRootPoly (p : ℂ[X]) : ℂ[X] :=
  C (((-1 : ℂ) ^ p.roots.card) * p.leadingCoeff ^ 2) *
    (p.roots.map fun z => X - C (z ^ 2)).prod

private theorem roots_squaredRootPoly {p : ℂ[X]} (hp : p ≠ 0) :
    (squaredRootPoly p).roots = p.roots.map fun z => z ^ 2 := by
  unfold squaredRootPoly
  rw [roots_C_mul _]
  · simpa only [Multiset.map_map, Function.comp_apply] using
      (roots_multiset_prod_X_sub_C (R := ℂ) (p.roots.map fun z => z ^ 2))
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hp))

/-- Pairing the factors at `x` and `-x` contributes one sign per root. -/
private theorem prod_square (roots : Multiset ℂ) (x : ℂ) :
    (-1 : ℂ) ^ roots.card * (roots.map fun z => x ^ 2 - z ^ 2).prod =
      (roots.map fun z => x - z).prod * (roots.map fun z => -x - z).prod := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons z roots ih =>
      simp only [Multiset.card_cons]
      rw [show (-1 : ℂ) ^ (roots.card + 1) =
        (-1 : ℂ) ^ roots.card * (-1) by rw [pow_succ]]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      calc
        (-1) ^ roots.card * -1 *
            ((x ^ 2 - z ^ 2) * (roots.map fun z => x ^ 2 - z ^ 2).prod) =
            (-(x ^ 2 - z ^ 2)) *
              ((-1) ^ roots.card * (roots.map fun z => x ^ 2 - z ^ 2).prod) := by ring
        _ = (-(x ^ 2 - z ^ 2)) *
              ((roots.map fun z => x - z).prod *
                (roots.map fun z => -x - z).prod) := by rw [ih]
        _ = (x - z) * (roots.map fun z => x - z).prod *
              ((-x - z) * (roots.map fun z => -x - z).prod) := by ring

private theorem expand_squaredRootPoly {p : ℂ[X]} (_hp : p ≠ 0) :
    expand ℂ 2 (squaredRootPoly p) = p * p.comp (-X) := by
  apply Polynomial.funext
  intro x
  have hsplit : p.Splits := IsAlgClosed.splits p
  rw [expand_eval, eval_mul, eval_comp, eval_neg, eval_X]
  rw [hsplit.eval_eq_prod_roots x, hsplit.eval_eq_prod_roots (-x)]
  simp only [squaredRootPoly, eval_mul, eval_C, eval_multiset_prod,
    Multiset.map_map, Function.comp_apply, eval_sub, eval_X]
  calc
    (-1) ^ p.roots.card * p.leadingCoeff ^ 2 *
        (p.roots.map fun z => x ^ 2 - z ^ 2).prod =
        p.leadingCoeff ^ 2 *
          ((-1) ^ p.roots.card *
            (p.roots.map fun z => x ^ 2 - z ^ 2).prod) := by ring
    _ = p.leadingCoeff ^ 2 *
          ((p.roots.map fun z => x - z).prod *
            (p.roots.map fun z => -x - z).prod) := by rw [prod_square]
    _ = p.leadingCoeff * (p.roots.map fun z => x - z).prod *
          (p.leadingCoeff * (p.roots.map fun z => -x - z).prod) := by ring

/-- One Graeffe step squares every complex root, preserving multiplicity. -/
theorem roots_graeffePoly {p : ℂ[X]} (hp : p ≠ 0) :
    (graeffePoly p).roots = p.roots.map fun z => z ^ 2 := by
  have hpoly : graeffePoly p = squaredRootPoly p := by
    apply expand_injective (R := ℂ) (n := 2) (by norm_num)
    rw [expand_graeffePoly, expand_squaredRootPoly hp]
  rw [hpoly, roots_squaredRootPoly hp]

/-- A Graeffe step of a nonzero polynomial is nonzero. -/
theorem graeffePoly_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : graeffePoly p ≠ 0 := by
  intro hg
  have hmul : p * p.comp (-X) = 0 := by
    rw [← expand_graeffePoly, hg]
    exact map_zero (expand ℂ 2)
  rcases mul_eq_zero.mp hmul with h | h
  · exact hp h
  · exact hp (comp_neg_X_eq_zero_iff.mp h)

/-- Squaring all roots and the radius preserves the number of roots in the
open disc. -/
theorem rootsInDisc_graeffePoly {p : ℂ[X]} (hp : p ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    rootsInDisc (graeffePoly p) 0 (r ^ 2) = rootsInDisc p 0 r := by
  unfold rootsInDisc
  rw [roots_graeffePoly hp]
  induction p.roots using Multiset.induction_on with
  | empty => simp
  | @cons z roots ih =>
      rw [Multiset.map_cons, Multiset.countP_cons, Multiset.countP_cons, ih]
      congr 1
      simp only [Metric.mem_ball, dist_zero_right, norm_pow]
      by_cases hz : ‖z‖ < r
      · rw [if_pos hz, if_pos]
        nlinarith [norm_nonneg z]
      · rw [if_neg hz, if_neg]
        nlinarith [norm_nonneg z]

/-! # Coefficient-ball arithmetic -/

/-- The coordinate `L¹` norm used by the executable coefficient balls. -/
private def complexL1 (z : ℂ) : ℝ := |z.re| + |z.im|

private theorem complexL1_nonneg (z : ℂ) : 0 ≤ complexL1 z := by
  unfold complexL1
  positivity

private theorem complexL1_add_le (z w : ℂ) :
    complexL1 (z + w) ≤ complexL1 z + complexL1 w := by
  unfold complexL1
  change |z.re + w.re| + |z.im + w.im| ≤
    (|z.re| + |z.im|) + (|w.re| + |w.im|)
  linarith [abs_add_le z.re w.re, abs_add_le z.im w.im]

private theorem complexL1_neg (z : ℂ) : complexL1 (-z) = complexL1 z := by
  simp [complexL1]

private theorem complexL1_mul_le (z w : ℂ) :
    complexL1 (z * w) ≤ complexL1 z * complexL1 w := by
  unfold complexL1
  simp only [mul_re, mul_im]
  calc
    |z.re * w.re - z.im * w.im| + |z.re * w.im + z.im * w.re| ≤
        (|z.re * w.re| + |z.im * w.im|) +
          (|z.re * w.im| + |z.im * w.re|) := by
            gcongr
            · exact abs_sub _ _
            · exact abs_add_le _ _
    _ = (|z.re| + |z.im|) * (|w.re| + |w.im|) := by
      simp only [abs_mul]
      ring

namespace CoeffBall

/-- A coefficient ball encloses `z` when the coordinate `L¹` distance from
its stored centre is at most its real-valued radius. -/
def Encloses (b : Hex.CoeffBall) (z : ℂ) : Prop :=
  complexL1 (z - GaussDyadic.toComplex b.center) ≤ Dyadic.toReal b.radius

private theorem centerL1 (z : Hex.GaussDyadic) :
    complexL1 (GaussDyadic.toComplex z) =
      Dyadic.toReal (Hex.CoeffBall.normOne z) := by
  simp [complexL1, Hex.CoeffBall.normOne]

private theorem normalize_encloses (bits : Nat) (raw : Hex.GaussDyadic)
    (error : _root_.Dyadic) (z : ℂ)
    (h : complexL1 (z - GaussDyadic.toComplex raw) ≤ Dyadic.toReal error) :
    Encloses (Hex.CoeffBall.normalize bits raw error) z := by
  let re := raw.1.roundDown (Hex.CoeffBall.sigPrec bits raw.1)
  let im := raw.2.roundDown (Hex.CoeffBall.sigPrec bits raw.2)
  let displacement := Hex.Dyadic.abs (raw.1 - re) + Hex.Dyadic.abs (raw.2 - im)
  have hdisp : complexL1
      (GaussDyadic.toComplex raw - GaussDyadic.toComplex (re, im)) =
        Dyadic.toReal displacement := by
    simp [complexL1, displacement, GaussDyadic.toComplex]
  have htri : complexL1 (z - GaussDyadic.toComplex (re, im)) ≤
      complexL1 (z - GaussDyadic.toComplex raw) +
        complexL1 (GaussDyadic.toComplex raw - GaussDyadic.toComplex (re, im)) := by
    rw [show z - GaussDyadic.toComplex (re, im) =
      (z - GaussDyadic.toComplex raw) +
        (GaussDyadic.toComplex raw - GaussDyadic.toComplex (re, im)) by ring]
    exact complexL1_add_le _ _
  have hround : Dyadic.toReal (error + displacement) ≤
      Dyadic.toReal (Hex.CoeffBall.roundRadius bits (error + displacement)) := by
    exact Dyadic.toReal_le_toReal_iff.mpr Dyadic.le_roundUp
  unfold Encloses Hex.CoeffBall.normalize
  dsimp only
  change complexL1 (z - GaussDyadic.toComplex (re, im)) ≤ _
  rw [Dyadic.toReal_add] at hround
  rw [hdisp] at htri
  have herr := add_le_add h (le_refl (Dyadic.toReal displacement))
  exact htri.trans (herr.trans hround)

/-- A rounded point ball encloses its exact Gaussian-dyadic input. -/
theorem point_encloses (bits : Nat) (z : Hex.GaussDyadic) :
    Encloses (Hex.CoeffBall.point bits z) (GaussDyadic.toComplex z) := by
  apply normalize_encloses
  simp [complexL1]

/-- Outward-rounded ball addition is sound. -/
theorem add_encloses {x y : Hex.CoeffBall} {z w : ℂ}
    (hz : Encloses x z) (hw : Encloses y w) (bits : Nat) :
    Encloses (Hex.CoeffBall.add bits x y) (z + w) := by
  apply normalize_encloses
  rw [GaussDyadic.toComplex_add, Dyadic.toReal_add]
  have htri := complexL1_add_le
    (z - GaussDyadic.toComplex x.center) (w - GaussDyadic.toComplex y.center)
  rw [show z + w - (GaussDyadic.toComplex x.center + GaussDyadic.toComplex y.center) =
    (z - GaussDyadic.toComplex x.center) +
      (w - GaussDyadic.toComplex y.center) by ring]
  exact htri.trans (add_le_add hz hw)

/-- Outward-rounded ball subtraction is sound. -/
theorem sub_encloses {x y : Hex.CoeffBall} {z w : ℂ}
    (hz : Encloses x z) (hw : Encloses y w) (bits : Nat) :
    Encloses (Hex.CoeffBall.sub bits x y) (z - w) := by
  apply normalize_encloses
  rw [GaussDyadic.toComplex_sub, Dyadic.toReal_add]
  have htri := complexL1_add_le
    (z - GaussDyadic.toComplex x.center) (-(w - GaussDyadic.toComplex y.center))
  rw [complexL1_neg] at htri
  rw [show z - w - (GaussDyadic.toComplex x.center - GaussDyadic.toComplex y.center) =
    (z - GaussDyadic.toComplex x.center) +
      -(w - GaussDyadic.toComplex y.center) by ring]
  exact htri.trans (add_le_add hz hw)

/-- Outward-rounded ball multiplication is sound. -/
theorem mul_encloses {x y : Hex.CoeffBall} {z w : ℂ}
    (hz : Encloses x z) (hw : Encloses y w) (bits : Nat) :
    Encloses (Hex.CoeffBall.mul bits x y) (z * w) := by
  let cx := GaussDyadic.toComplex x.center
  let cy := GaussDyadic.toComplex y.center
  let dx := z - cx
  let dy := w - cy
  have hz' : complexL1 dx ≤ Dyadic.toReal x.radius := hz
  have hw' : complexL1 dy ≤ Dyadic.toReal y.radius := hw
  have hxy : complexL1 (z * w - cx * cy) ≤
      complexL1 cx * Dyadic.toReal y.radius +
        complexL1 cy * Dyadic.toReal x.radius +
          Dyadic.toReal x.radius * Dyadic.toReal y.radius := by
    calc
      complexL1 (z * w - cx * cy) = complexL1 (cx * dy + cy * dx + dx * dy) := by
        congr 1
        dsimp only [dx, dy]
        ring
      _ ≤ complexL1 (cx * dy) + complexL1 (cy * dx) + complexL1 (dx * dy) := by
        exact (complexL1_add_le (cx * dy + cy * dx) (dx * dy)).trans <|
          add_le_add (complexL1_add_le (cx * dy) (cy * dx)) le_rfl
      _ ≤ complexL1 cx * complexL1 dy + complexL1 cy * complexL1 dx +
          complexL1 dx * complexL1 dy := by
        gcongr <;> apply complexL1_mul_le
      _ ≤ complexL1 cx * Dyadic.toReal y.radius +
          complexL1 cy * Dyadic.toReal x.radius +
            Dyadic.toReal x.radius * Dyadic.toReal y.radius := by
        have hzx : 0 ≤ Dyadic.toReal x.radius :=
          (complexL1_nonneg dx).trans hz'
        have hwy : 0 ≤ Dyadic.toReal y.radius :=
          (complexL1_nonneg dy).trans hw'
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hw' (complexL1_nonneg cx))
            (mul_le_mul_of_nonneg_left hz' (complexL1_nonneg cy)))
          (mul_le_mul hz' hw' (complexL1_nonneg dy) hzx)
  apply normalize_encloses
  rw [GaussDyadic.toComplex_mul]
  simpa only [Hex.CoeffBall.mul, centerL1, Dyadic.toReal_add,
    Dyadic.toReal_mul, cx, cy] using hxy

/-- The executable lower endpoint of an enclosing coefficient ball is below
the exact complex modulus. -/
theorem lo_le_norm {b : Hex.CoeffBall} {z : ℂ} (h : Encloses b z) :
    Dyadic.toReal b.lo ≤ ‖z‖ := by
  let c := GaussDyadic.toComplex b.center
  have hrad : 0 ≤ Dyadic.toReal b.radius :=
    (complexL1_nonneg (z - c)).trans h
  have hdist : ‖z - c‖ ≤ Dyadic.toReal b.radius :=
    (Complex.norm_le_abs_re_add_abs_im (z - c)).trans h
  have hctri : ‖c‖ ≤ ‖z‖ + ‖z - c‖ := by
    calc
      ‖c‖ = ‖z + (c - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖c - z‖ := norm_add_le z (c - z)
      _ = ‖z‖ + ‖z - c‖ := by rw [norm_sub_rev]
  have hcenter :
      max |c.re| |c.im| ≤ ‖z‖ + Dyadic.toReal b.radius := by
    calc
      max |c.re| |c.im| ≤ ‖c‖ :=
        max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
      _ ≤ ‖z‖ + ‖z - c‖ := hctri
      _ ≤ ‖z‖ + Dyadic.toReal b.radius := add_le_add le_rfl hdist
  simp only [Hex.CoeffBall.lo, Dyadic.toReal_max, Dyadic.toReal_zero,
    Dyadic.toReal_sub, Dyadic.toReal_abs, max_le_iff]
  constructor
  · exact norm_nonneg _
  · dsimp only [c] at hcenter
    exact sub_le_iff_le_add.mpr hcenter

/-- The exact complex modulus is below the executable upper endpoint of an
enclosing coefficient ball. -/
theorem norm_le_hi {b : Hex.CoeffBall} {z : ℂ} (h : Encloses b z) :
    ‖z‖ ≤ Dyadic.toReal b.hi := by
  let c := GaussDyadic.toComplex b.center
  have hdist : ‖z - c‖ ≤ Dyadic.toReal b.radius :=
    (Complex.norm_le_abs_re_add_abs_im (z - c)).trans h
  have hztri : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
    calc
      ‖z‖ = ‖c + (z - c)‖ := by congr 1; ring
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le c (z - c)
  calc
    ‖z‖ ≤ ‖c‖ + ‖z - c‖ := hztri
    _ ≤ complexL1 c + Dyadic.toReal b.radius :=
      add_le_add (Complex.norm_le_abs_re_add_abs_im c) hdist
    _ = Dyadic.toReal b.hi := by
      rw [show complexL1 c = Dyadic.toReal (Hex.CoeffBall.normOne b.center) by
        exact centerL1 b.center]
      simp [Hex.CoeffBall.hi]

private theorem zero_encloses : Encloses Hex.CoeffBall.zero 0 := by
  simp [Encloses, Hex.CoeffBall.zero, complexL1, GaussDyadic.toComplex]

private theorem softTaylorState_encloses (p : Hex.ZPoly) (c : Hex.GaussDyadic)
    (bits k n : Nat) :
    Encloses (Hex.softTaylorState p c bits k n).1
        (∑ r ∈ Finset.range n,
          ((k + r).choose k : ℂ) * (p.coeff (k + r) : ℂ) *
            GaussDyadic.toComplex c ^ r) ∧
      Encloses (Hex.softTaylorState p c bits k n).2
        (GaussDyadic.toComplex c ^ n) := by
  induction n with
  | zero =>
      constructor
      · simpa [Hex.softTaylorState] using zero_encloses
      · simpa [Hex.softTaylorState] using
          point_encloses bits (Hex.GaussDyadic.ofInt 1)
  | succ n ih =>
      have hstate : Hex.softTaylorState p c bits k (n + 1) =
          Hex.softTaylorStep p c bits k (Hex.softTaylorState p c bits k n) n := by
        simp [Hex.softTaylorState, List.range_succ]
      rw [hstate]
      let scalar : Int := Int.ofNat (Hex.Nat.binom (k + n) k) * p.coeff (k + n)
      have hscalar : GaussDyadic.toComplex (Hex.GaussDyadic.ofInt scalar) =
          ((k + n).choose k : ℂ) * (p.coeff (k + n) : ℂ) := by
        simp [scalar, Hex.Nat.binom_eq_choose, choose_eq_choose]
      have hterm := mul_encloses (point_encloses bits (Hex.GaussDyadic.ofInt scalar))
        ih.2 bits
      have hsum := add_encloses ih.1 hterm bits
      have hpow := mul_encloses ih.2 (point_encloses bits c) bits
      constructor
      · simpa only [Hex.softTaylorStep, scalar, hscalar, Finset.sum_range_succ,
          Finset.sum_mul, mul_assoc] using hsum
      · simpa only [Hex.softTaylorStep, pow_succ] using hpow

/-- The soft Taylor coefficient encloses the corresponding coefficient of the
exact Taylor shift, scaled by `h^k`. -/
theorem softTaylorCoeff_encloses (p : Hex.ZPoly) (c : Hex.GaussDyadic)
    (h : _root_.Dyadic) (bits k : Nat) :
    Encloses (Hex.softTaylorCoeff p c h bits k)
      (GaussDyadic.toComplex (Hex.taylorCoeff p c k) *
        (Dyadic.toReal h : ℂ) ^ k) := by
  have hs := (softTaylorState_encloses p c bits k (p.size - k)).1
  have hh := point_encloses bits (h ^ k, 0)
  have hmul := mul_encloses hs hh bits
  have hcast : GaussDyadic.toComplex (h ^ k, 0) = (Dyadic.toReal h : ℂ) ^ k := by
    calc
      GaussDyadic.toComplex (h ^ k, 0) = Complex.ofReal (Dyadic.toReal (h ^ k)) := by
        apply Complex.ext
        · rfl
        · exact Dyadic.toReal_zero
      _ = Complex.ofReal (Dyadic.toReal h ^ k) := by rw [Dyadic.toReal_pow]
      _ = (Dyadic.toReal h : ℂ) ^ k := Complex.ofReal_pow _ _
  rw [hcast] at hmul
  rw [toComplex_taylorCoeff]
  exact hmul

end CoeffBall

/-- The exact polynomial in square-local coordinates.  Its unit square has
the original square's half-width. -/
@[expose] def localPoly (p : Hex.ZPoly) (s : Hex.DyadicSquare) : ℂ[X] :=
  let h : ℂ := Dyadic.toReal (.ofIntWithPrec 1 s.prec)
  (toPolyℂ p).comp (C h * X + C (GaussDyadic.toComplex s.center))

private theorem localPoly_coeff (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    (localPoly p s).coeff k =
      GaussDyadic.toComplex (Hex.taylorCoeff p s.center k) *
        (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) ^ k := by
  let h : ℂ := Dyadic.toReal (.ofIntWithPrec 1 s.prec)
  let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex s.center))
  have hlocal : localPoly p s = q.comp (C h * X) := by
    unfold localPoly q
    rw [comp_assoc]
    simp only [add_comp, X_comp, C_comp]
    ring
  rw [hlocal, comp_C_mul_X_coeff]
  dsimp only [h, q]
  rw [← taylor_coeff p s.center k, Hex.taylor_getD]
  split <;> rename_i hk
  · rfl
  · simp [Hex.taylorCoeff, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hk)]

private theorem softShift_natDegree_lt_size (p : Hex.ZPoly) (hp : 0 < p.size)
    (c : ℂ) : ((toPolyℂ p).comp (X + C c)).natDegree < p.size := by
  have hpoly : (toPolyℂ p).natDegree < p.size := by
    rw [natDegree_toPolyℂ]
    have hdegree : p.degree? = some (p.size - 1) := by
      simp [Hex.DensePoly.degree?, Nat.ne_of_gt hp]
    rw [hdegree, Option.getD_some]
    omega
  exact Polynomial.natDegree_comp_le.trans_lt (by simpa using hpoly)

/-- Every initial coefficient ball encloses the matching coefficient of the
exact local polynomial. -/
theorem taylorBalls_enclose (p : Hex.ZPoly) (s : Hex.DyadicSquare) (bits k : Nat) :
    CoeffBall.Encloses ((Hex.taylorBalls p s bits).getD k Hex.CoeffBall.zero)
      ((localPoly p s).coeff k) := by
  by_cases hk : k < p.size
  · rw [localPoly_coeff]
    simpa [Hex.taylorBalls, hk] using
      (CoeffBall.softTaylorCoeff_encloses p s.center
        (.ofIntWithPrec 1 s.prec) bits k)
  · have hsize : (Hex.taylorBalls p s bits).size = p.size := by
      simp [Hex.taylorBalls]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
      rw [hsize]
      omega)]
    by_cases hp : p.size = 0
    · have hp0 : p = 0 := by
        apply Hex.DensePoly.ext_coeff
        intro i
        rw [Hex.DensePoly.coeff_zero]
        exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)
      have hlocal : localPoly p s = 0 := by simp [hp0, localPoly, toPolyℂ]
      rw [hlocal, coeff_zero]
      exact CoeffBall.zero_encloses
    · have hshift := softShift_natDegree_lt_size p (Nat.pos_of_ne_zero hp)
          (GaussDyadic.toComplex s.center)
      let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex s.center))
      have hlocal : localPoly p s = q.comp
          (C (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * X) := by
        unfold localPoly q
        rw [comp_assoc]
        simp only [add_comp, X_comp, C_comp]
      have hdegree : (localPoly p s).natDegree < p.size := by
        rw [hlocal]
        calc
          (q.comp (C (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * X)).natDegree ≤
              q.natDegree * (C (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * X).natDegree :=
            natDegree_comp_le
          _ ≤ q.natDegree * 1 := Nat.mul_le_mul_left _
            (natDegree_C_mul_le _ _ |>.trans natDegree_X_le)
          _ = q.natDegree := Nat.mul_one _
          _ < p.size := by simpa [q] using hshift
      rw [coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hk))]
      exact CoeffBall.zero_encloses

/-- The exact-shift ball constructor encloses the same local polynomial
coefficients. -/
theorem exactTaylorBalls_enclose (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (bits k : Nat) :
    CoeffBall.Encloses
      ((Hex.exactTaylorBalls p s bits).getD k Hex.CoeffBall.zero)
      ((localPoly p s).coeff k) := by
  by_cases hk : k < p.size
  · rw [localPoly_coeff]
    have hp := CoeffBall.point_encloses bits <|
      Hex.GaussDyadic.mul ((Hex.taylor p s.center).getD k (0, 0))
        ((.ofIntWithPrec 1 s.prec : _root_.Dyadic) ^ k, 0)
    have hpow :
        GaussDyadic.toComplex
            (((.ofIntWithPrec 1 s.prec : _root_.Dyadic) ^ k), 0) =
          (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) ^ k := by
      calc
        GaussDyadic.toComplex
            (((.ofIntWithPrec 1 s.prec : _root_.Dyadic) ^ k), 0) =
            Complex.ofReal
              (Dyadic.toReal ((.ofIntWithPrec 1 s.prec : _root_.Dyadic) ^ k)) := by
          apply Complex.ext
          · rfl
          · exact Dyadic.toReal_zero
        _ = Complex.ofReal
            (Dyadic.toReal (.ofIntWithPrec 1 s.prec) ^ k) := by
          rw [Dyadic.toReal_pow]
        _ = (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) ^ k :=
          Complex.ofReal_pow _ _
    rw [Hex.taylor_getD_of_lt p s.center k hk] at hp
    have hball :
        (Hex.exactTaylorBalls p s bits).getD k Hex.CoeffBall.zero =
          Hex.CoeffBall.point bits
            (Hex.GaussDyadic.mul (Hex.taylorCoeff p s.center k)
              ((.ofIntWithPrec 1 s.prec : _root_.Dyadic) ^ k, 0)) := by
      rw [Array.getD_eq_getD_getElem?]
      simp [Hex.exactTaylorBalls, Hex.seededTaylorBalls, Hex.taylor_size, hk]
      rw [Array.getElem_eq_getD (0, 0)]
      rw [Hex.taylor_getD_of_lt p s.center k hk]
    rw [hball]
    simpa [GaussDyadic.toComplex_mul, hpow] using hp
  · have ht := taylorBalls_enclose p s bits k
    have hsoft :
        (Hex.taylorBalls p s bits).getD k Hex.CoeffBall.zero =
          Hex.CoeffBall.zero := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [show (Hex.taylorBalls p s bits).size = p.size by
          simp [Hex.taylorBalls]]
        exact Nat.le_of_not_gt hk)]
      rfl
    have hexact :
        (Hex.exactTaylorBalls p s bits).getD k Hex.CoeffBall.zero =
          Hex.CoeffBall.zero := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [show (Hex.exactTaylorBalls p s bits).size = p.size by
          simp [Hex.exactTaylorBalls, Hex.seededTaylorBalls, Hex.taylor_size]]
        exact Nat.le_of_not_gt hk)]
      rfl
    rw [hsoft] at ht
    rw [hexact]
    exact ht

/-- A coefficient array encloses a polynomial through its stored degree. -/
def BallsEnclose (cs : Array Hex.CoeffBall) (q : ℂ[X]) : Prop :=
  q.natDegree < cs.size ∧
    ∀ k, k < cs.size → CoeffBall.Encloses (cs.getD k Hex.CoeffBall.zero) (q.coeff k)

/-- The degree bound carried by a complete coefficient-ball enclosure. -/
theorem BallsEnclose.degree_lt {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    (h : BallsEnclose cs q) : q.natDegree < cs.size := h.1

private theorem localPoly_degree_lt (p : Hex.ZPoly) (s : Hex.DyadicSquare) :
    (localPoly p s).natDegree < p.size ∨ p.size = 0 := by
  by_cases hp : p.size = 0
  · exact Or.inr hp
  · left
    have hshift := softShift_natDegree_lt_size p (Nat.pos_of_ne_zero hp)
      (GaussDyadic.toComplex s.center)
    let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex s.center))
    have hlocal : localPoly p s = q.comp
        (C (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * X) := by
      unfold localPoly q
      rw [comp_assoc]
      simp only [add_comp, X_comp, C_comp]
    rw [hlocal]
    calc
      (q.comp (C (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * X)).natDegree ≤
          q.natDegree * (C (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * X).natDegree :=
        natDegree_comp_le
      _ ≤ q.natDegree * 1 := Nat.mul_le_mul_left _
        (natDegree_C_mul_le _ _ |>.trans natDegree_X_le)
      _ = q.natDegree := Nat.mul_one _
      _ < p.size := by simpa [q] using hshift

/-- The initial soft Taylor array encloses the complete local polynomial. -/
theorem taylorBalls_enclosePoly (p : Hex.ZPoly) (s : Hex.DyadicSquare) (bits : Nat)
    (hp : 0 < p.size) : BallsEnclose (Hex.taylorBalls p s bits) (localPoly p s) := by
  constructor
  · simpa [Hex.taylorBalls] using (localPoly_degree_lt p s).resolve_right (by omega)
  · intro k hk
    exact taylorBalls_enclose p s bits k

/-- The exact-shift array is also a complete coefficient-ball enclosure. -/
theorem exactTaylorBalls_enclosePoly (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (bits : Nat) (hp : 0 < p.size) :
    BallsEnclose (Hex.exactTaylorBalls p s bits) (localPoly p s) := by
  constructor
  · simpa [Hex.exactTaylorBalls, Hex.seededTaylorBalls, Hex.taylor_size] using
      (localPoly_degree_lt p s).resolve_right (by omega)
  · intro k _
    exact exactTaylorBalls_enclose p s bits k

private theorem ballFold_encloses (bits n : Nat) (f : Nat → Hex.CoeffBall)
    (g : Nat → ℂ) (h : ∀ i, CoeffBall.Encloses (f i) (g i)) :
    CoeffBall.Encloses
      ((List.range n).foldl (fun acc i => Hex.CoeffBall.add bits acc (f i))
        Hex.CoeffBall.zero)
      (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa using CoeffBall.zero_encloses
  | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ]
      exact CoeffBall.add_encloses ih (h n) bits

private theorem ballsEnclose_getD {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    (h : BallsEnclose cs q) (k : Nat) :
    CoeffBall.Encloses (cs.getD k Hex.CoeffBall.zero) (q.coeff k) := by
  by_cases hk : k < cs.size
  · exact h.2 k hk
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_gt hk),
      coeff_eq_zero_of_natDegree_lt (h.1.trans_le (Nat.le_of_not_gt hk))]
    exact CoeffBall.zero_encloses

private theorem graeffeEven_encloses {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    (h : BallsEnclose cs q) (bits k : Nat) :
    CoeffBall.Encloses (Hex.graeffeEven bits cs k)
      ((graeffeEvenPart q ^ 2).coeff k) := by
  have hfold := ballFold_encloses bits (k + 1)
    (fun i => Hex.CoeffBall.mul bits (cs.getD (2 * i) Hex.CoeffBall.zero)
      (cs.getD (2 * (k - i)) Hex.CoeffBall.zero))
    (fun i => q.coeff (2 * i) * q.coeff (2 * (k - i)))
    (fun i => CoeffBall.mul_encloses (ballsEnclose_getD h (2 * i))
      (ballsEnclose_getD h (2 * (k - i))) bits)
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa [Hex.graeffeEven, graeffeEvenPart, coeff_contract, Nat.mul_comm] using hfold

private theorem graeffeOdd_encloses {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    (h : BallsEnclose cs q) (bits k : Nat) :
    CoeffBall.Encloses (Hex.graeffeOdd bits cs k)
      ((graeffeOddPart q ^ 2).coeff k) := by
  have hfold := ballFold_encloses bits (k + 1)
    (fun i => Hex.CoeffBall.mul bits (cs.getD (2 * i + 1) Hex.CoeffBall.zero)
      (cs.getD (2 * (k - i) + 1) Hex.CoeffBall.zero))
    (fun i => q.coeff (2 * i + 1) * q.coeff (2 * (k - i) + 1))
    (fun i => CoeffBall.mul_encloses (ballsEnclose_getD h (2 * i + 1))
      (ballsEnclose_getD h (2 * (k - i) + 1)) bits)
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa [Hex.graeffeOdd, graeffeOddPart, coeff_contract, coeff_divX, Nat.mul_comm,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfold

/-- A Graeffe step preserves natural degree for nonzero complex polynomials. -/
theorem natDegree_graeffePoly {q : ℂ[X]} (hq : q ≠ 0) :
    (graeffePoly q).natDegree = q.natDegree := by
  rw [(IsAlgClosed.splits (graeffePoly q)).natDegree_eq_card_roots,
    roots_graeffePoly hq, Multiset.card_map,
    ← (IsAlgClosed.splits q).natDegree_eq_card_roots]

/-- One executable coefficient-ball Graeffe step encloses the exact transform. -/
theorem graeffe_enclosePoly {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    (h : BallsEnclose cs q) (bits : Nat) :
    BallsEnclose (Hex.graeffe bits cs) (graeffePoly q) := by
  have hsize : (Hex.graeffe bits cs).size = cs.size := by simp [Hex.graeffe]
  constructor
  · rw [hsize]
    by_cases hq : q = 0
    · subst q
      rw [graeffePoly_zero]
      simpa using h.1
    · rw [natDegree_graeffePoly hq]
      exact h.1
  · intro k hk
    have hkcs : k < cs.size := by simpa [hsize] using hk
    have hget : (Hex.graeffe bits cs).getD k Hex.CoeffBall.zero =
        if k = 0 then Hex.graeffeEven bits cs 0
        else Hex.CoeffBall.sub bits (Hex.graeffeEven bits cs k)
          (Hex.graeffeOdd bits cs (k - 1)) := by
      rw [Array.getD_eq_getD_getElem?]
      simp [Hex.graeffe, hkcs]
    rw [hget]
    by_cases hk0 : k = 0
    · subst k
      simpa [graeffePoly] using graeffeEven_encloses h bits 0
    · have he := graeffeEven_encloses h bits k
      have ho := graeffeOdd_encloses h bits (k - 1)
      have hs := CoeffBall.sub_encloses he ho bits
      rw [if_neg hk0]
      have hx : (X * graeffeOddPart q ^ 2).coeff k =
          (graeffeOddPart q ^ 2).coeff (k - 1) := by
        let n := k - 1
        have hkn : k = n + 1 := by simp only [n]; omega
        calc
          (X * graeffeOddPart q ^ 2).coeff k =
              (X * graeffeOddPart q ^ 2).coeff (n + 1) := by rw [hkn]
          _ = (graeffeOddPart q ^ 2).coeff n := coeff_X_mul _ n
          _ = (graeffeOddPart q ^ 2).coeff (k - 1) := rfl
      unfold graeffePoly
      rw [coeff_sub, hx]
      exact hs

/-! # Soundness of a soft coefficient comparison -/

private theorem sum_erase_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n k : ℕ) :
    (∑ i ∈ (Finset.range n).erase k, f i) =
      ∑ i ∈ Finset.range n, if i = k then 0 else f i := by
  classical
  calc
    (∑ i ∈ (Finset.range n).erase k, f i) =
        ∑ i ∈ (Finset.range n).filter (fun i => i ≠ k), f i := by
      congr 1
      ext i
      simp [and_comm]
    _ = ∑ i ∈ Finset.range n, if i ≠ k then f i else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ Finset.range n, if i = k then 0 else f i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hik : i = k <;> simp [hik]

/-- Closed form of the soft-Pellet accumulator. -/
private theorem softPelletFold (cs : Array Hex.CoeffBall) (k : Nat)
    (r : _root_.Dyadic) (n : Nat) :
    let result := (List.range n).foldl
        (fun acc i =>
          let acc' := if i = k then acc.1
            else acc.1 + (cs.getD i Hex.CoeffBall.zero).hi * acc.2
          (acc', acc.2 * r))
        ((0 : _root_.Dyadic), (1 : _root_.Dyadic))
    Dyadic.toReal result.1 =
        (∑ i ∈ Finset.range n,
          if i = k then 0 else
            Dyadic.toReal (cs.getD i Hex.CoeffBall.zero).hi *
              Dyadic.toReal r ^ i) ∧
      Dyadic.toReal result.2 = Dyadic.toReal r ^ n := by
  induction n with
  | zero =>
      constructor
      · simp
      · change Dyadic.toReal (_root_.Dyadic.ofInt 1) = 1
        simp
  | succ n ih =>
      dsimp at ih
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      constructor
      · by_cases hnk : n = k
        · rw [if_pos hnk, ih.1, Finset.sum_range_succ]
          simp only [hnk, if_pos, add_zero]
        · rw [if_neg hnk, Dyadic.toReal_add, Dyadic.toReal_mul, ih.1, ih.2,
            Finset.sum_range_succ]
          simp only [hnk, if_false]
      · rw [Dyadic.toReal_mul, ih.2, pow_succ]

/-- A successful soft comparison names a stored coefficient. -/
theorem softPelletAt_size {cs : Array Hex.CoeffBall} {k : ℕ}
    {rlo rhi : _root_.Dyadic} (h : Hex.softPelletAt cs k rlo rhi = true) :
    k < cs.size := by
  unfold Hex.softPelletAt at h
  by_contra hk
  rw [if_neg (by omega)] at h
  contradiction

/-- A successful three-radius comparison names a stored coefficient. -/
theorem softPelletThree_size {cs : Array Hex.CoeffBall} {k : ℕ}
    {rs : Hex.SoftRadii} (h : Hex.softPelletThree cs k rs = true) :
    k < cs.size := by
  have hbase : Hex.softPelletAt cs k rs.baseLo rs.baseHi = true := by
    have hall :
        (Hex.softPelletAt cs k rs.baseLo rs.baseHi = true ∧
          Hex.softPelletAt cs k rs.twoLo rs.twoHi = true) ∧
        Hex.softPelletAt cs k rs.fourLo rs.fourHi = true := by
      simpa [Hex.softPelletThree] using h
    exact hall.1.1
  exact softPelletAt_size hbase

/-- Array size is invariant through Graeffe, so any successful loop result
still names a coefficient in the initial array. -/
theorem softGraeffeLoop_size {cs : Array Hex.CoeffBall} {bits k rounds : ℕ}
    {rs : Hex.SoftRadii}
    (h : Hex.softGraeffeLoop bits k rounds cs rs = true) :
    k < cs.size := by
  induction rounds generalizing cs rs with
  | zero => exact softPelletThree_size h
  | succ rounds ih =>
      simp only [Hex.softGraeffeLoop, Bool.or_eq_true] at h
      rcases h with hnow | hlater
      · exact softPelletThree_size hnow
      · have hsize := ih hlater
        simpa [Hex.graeffe] using hsize

/-- A successful soft comparison exposes its strict real endpoint
inequality. -/
theorem softPelletAt_bound {cs : Array Hex.CoeffBall} {k : ℕ}
    {rlo rhi : _root_.Dyadic} (h : Hex.softPelletAt cs k rlo rhi = true) :
    (∑ i ∈ (Finset.range cs.size).erase k,
        Dyadic.toReal (cs.getD i Hex.CoeffBall.zero).hi *
          Dyadic.toReal rhi ^ i) <
      Dyadic.toReal (cs.getD k Hex.CoeffBall.zero).lo *
        Dyadic.toReal rlo ^ k := by
  have hk := softPelletAt_size h
  unfold Hex.softPelletAt at h
  rw [if_pos hk] at h
  let result := (List.range cs.size).foldl
      (fun acc i =>
        let acc' := if i = k then acc.1
          else acc.1 + (cs.getD i Hex.CoeffBall.zero).hi * acc.2
        (acc', acc.2 * rhi))
      ((0 : _root_.Dyadic), (1 : _root_.Dyadic))
  have hdyadic : result.1 <
      (cs.getD k Hex.CoeffBall.zero).lo * rlo ^ k := by
    simpa [result] using of_decide_eq_true h
  have hreal := Dyadic.toReal_lt_toReal_iff.mpr hdyadic
  have hfold := (softPelletFold cs k rhi cs.size).1
  rw [show Dyadic.toReal result.1 =
      (∑ i ∈ Finset.range cs.size,
        if i = k then 0 else
          Dyadic.toReal (cs.getD i Hex.CoeffBall.zero).hi *
            Dyadic.toReal rhi ^ i) from hfold] at hreal
  simpa only [Dyadic.toReal_mul, Dyadic.toReal_pow, sum_erase_range] using hreal

/-- Endpoint bounds plus coefficient-ball enclosure imply the exact
coefficient dominance required by Pellet's theorem at every real radius in
the supplied interval. -/
theorem softPelletAt_dominates {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    {k : ℕ} {rlo rhi : _root_.Dyadic} {r : ℝ}
    (henclose : BallsEnclose cs q)
    (h : Hex.softPelletAt cs k rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hlo : Dyadic.toReal rlo ≤ r)
    (hhi : r ≤ Dyadic.toReal rhi) :
    (∑ i ∈ (Finset.range cs.size).erase k, ‖q.coeff i‖ * r ^ i) <
      ‖q.coeff k‖ * r ^ k := by
  have hr : 0 ≤ r := hrlo.trans hlo
  calc
    (∑ i ∈ (Finset.range cs.size).erase k, ‖q.coeff i‖ * r ^ i) ≤
        ∑ i ∈ (Finset.range cs.size).erase k,
          Dyadic.toReal (cs.getD i Hex.CoeffBall.zero).hi *
            Dyadic.toReal rhi ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoeff := CoeffBall.norm_le_hi (ballsEnclose_getD henclose i)
      have hrhi : 0 ≤ Dyadic.toReal rhi := hr.trans hhi
      have hbound : 0 ≤ Dyadic.toReal (cs.getD i Hex.CoeffBall.zero).hi :=
        (norm_nonneg _).trans hcoeff
      gcongr
    _ < Dyadic.toReal (cs.getD k Hex.CoeffBall.zero).lo *
        Dyadic.toReal rlo ^ k := softPelletAt_bound h
    _ ≤ ‖q.coeff k‖ * r ^ k := by
      have hcoeff := CoeffBall.lo_le_norm (ballsEnclose_getD henclose k)
      have hlo0 : 0 ≤ Dyadic.toReal (cs.getD k Hex.CoeffBall.zero).lo := by
        simp [Hex.CoeffBall.lo]
      gcongr


end

end HexRootsMathlib
