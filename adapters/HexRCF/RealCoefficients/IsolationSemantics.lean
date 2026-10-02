/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.Carrier
public import HexRealAlgebraicMathlib.Order
public import HexRealAlgebraicMathlib.Approx
public import HexRealAlgebraicMathlib.Roots

public section

/-! The canonical real-algebraic producer feeds the generic checked-root
semantics through the shared root-sum theorem consumed by
`IsolationReplay.check_roots`. -/

namespace Hex.RCF.RealCoefficients

open HexRealRootsMathlib HexPolyMathlib.Interpret

private theorem algebraic_sign (a : RealAlgebraicNumber) :
    a.sign = (SignType.sign a.toReal : Int) := by
  rw [RealAlgebraicNumber.sign_eq]
  rcases lt_trichotomy a.toReal 0 with h | h | h
  · simp [h, _root_.sign_neg h]
  · simp [h]
  · simp [not_lt_of_ge h.le, ne_of_gt h, _root_.sign_pos h]

/-- The canonical real interpretation reflects zero. -/
theorem algebraic_zero (a : RealAlgebraicNumber) :
    a.toReal = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply RealAlgebraicNumber.toReal_injective
    simpa only [RealAlgebraicNumber.zero_toReal] using h
  · rintro rfl
    exact RealAlgebraicNumber.zero_toReal

/-- A successful canonical-algebraic isolation covers every real root of the
interpreted head and places one in each returned interval. -/
theorem isolateAt_roots [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber) (precision : Nat)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (h : isolateAt context head precision = some cert) :
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      (∀ i, (interpret RealAlgebraicNumber.toReal algebraic_zero head).IsRoot (root i) ∧
        HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper) ∧
      StrictMono root ∧
      (∀ x, (interpret RealAlgebraicNumber.toReal algebraic_zero head).IsRoot x ↔
        ∃ i, root i = x) ∧
      (∀ cut, Cell.Region root (.open cut)
        (HexRealRootsMathlib.Dyadic.toReal (cert.isolations.openPoint cut))) := by
  exact cert.check_roots RealAlgebraicNumber.toReal
    algebraic_zero
    RealAlgebraicNumber.one_toReal RealAlgebraicNumber.add_toReal
    RealAlgebraicNumber.sub_toReal RealAlgebraicNumber.mul_toReal
    (fun n => by change RealAlgebraicNumber.toRealHom (n : RealAlgebraicNumber) = (n : ℝ); simp)
    RealAlgebraicNumber.sign algebraic_sign
    (fun d => RealAlgebraicNumber.ofRat d.toRat)
    (fun d => by simp [HexRealRootsMathlib.toReal_eq_cast_toRat])
    context head (isolateAt_checked context head precision cert h)

/-- Every requested precision produces a strict enclosure, with a width bound
that shrinks along a cofinal precision schedule. -/
theorem rootInterval_spec (root : RealAlgebraicNumber) (precision : Nat) :
    ∃ interval, rootInterval root precision = some interval ∧
      HexRealRootsMathlib.Dyadic.toReal interval.lower < root.toReal ∧
      root.toReal < HexRealRootsMathlib.Dyadic.toReal interval.upper ∧
      HexRealRootsMathlib.Dyadic.toReal interval.upper -
        HexRealRootsMathlib.Dyadic.toReal interval.lower ≤
          4 * (2 : ℝ) ^ (-(precision : Int)) := by
  let ball := root.approxBall (precision : Int)
  let margin := Dyadic.ofInt 1 >>> (precision : Int)
  let lower := ball.re - ball.radius - margin
  let upper := ball.re + ball.radius + margin
  have hm : HexRootsMathlib.Dyadic.toReal margin =
      (2 : ℝ) ^ (-(precision : Int)) := by
    simp [margin, HexRootsMathlib.Dyadic.toReal_shiftRight]
  have hmpos : 0 < HexRootsMathlib.Dyadic.toReal margin := by
    rw [hm]
    positivity
  have he := root.approx_enclosure (precision : Int)
  have hr := AlgebraicNumber.approx_radius root.toAlgebraic (precision : Int)
  change HexRootsMathlib.Dyadic.toReal ball.radius ≤
    (2 : ℝ) ^ (-(precision : Int)) at hr
  have hlo : HexRootsMathlib.Dyadic.toReal lower < root.toReal := by
    dsimp [lower]
    rw [HexRootsMathlib.Dyadic.toReal_sub, HexRootsMathlib.Dyadic.toReal_sub]
    change ((ball.re.toRat : ℝ) - (ball.radius.toRat : ℝ)) -
      HexRootsMathlib.Dyadic.toReal margin < root.toReal
    push_cast at he
    linarith [he.1]
  have hhi : root.toReal < HexRootsMathlib.Dyadic.toReal upper := by
    dsimp [upper]
    rw [HexRootsMathlib.Dyadic.toReal_add, HexRootsMathlib.Dyadic.toReal_add]
    change root.toReal < ((ball.re.toRat : ℝ) + (ball.radius.toRat : ℝ)) +
      HexRootsMathlib.Dyadic.toReal margin
    push_cast at he
    linarith [he.2]
  have hlt : lower < upper :=
    HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mp (hlo.trans hhi)
  have hlo' : HexRealRootsMathlib.Dyadic.toReal lower < root.toReal := by
    simpa only [HexRealRootsMathlib.toReal_eq_cast_toRat,
      HexRootsMathlib.Dyadic.toReal] using hlo
  have hhi' : root.toReal < HexRealRootsMathlib.Dyadic.toReal upper := by
    simpa only [HexRealRootsMathlib.toReal_eq_cast_toRat,
      HexRootsMathlib.Dyadic.toReal] using hhi
  refine ⟨⟨lower, upper, hlt⟩, ?_, hlo', hhi', ?_⟩
  · simp [rootInterval, ball, margin, lower, upper, hlt]
  · simp only [HexRealRootsMathlib.toReal_eq_cast_toRat]
    change HexRootsMathlib.Dyadic.toReal upper -
      HexRootsMathlib.Dyadic.toReal lower ≤ _
    dsimp [upper, lower]
    simp only [HexRootsMathlib.Dyadic.toReal_add, HexRootsMathlib.Dyadic.toReal_sub]
    linarith


private theorem precision_small (epsilon : ℝ) (h : 0 < epsilon) :
    ∃ N : Nat, ∀ n ≥ N, (2 : ℝ) ^ (-(n : Int)) < epsilon := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  have he := (tendsto_order.mp hp).2 epsilon h
  simp only [Filter.eventually_atTop] at he
  obtain ⟨N, hN⟩ := he
  refine ⟨N, fun n hn => ?_⟩
  have hi : (2 : ℝ) ^ (-(n : Int)) = (1 / 2 : ℝ) ^ n := by
    simp [zpow_neg, inv_pow]
  rw [hi]
  exact hN n hn

/-- Precision progress is preserved under every explicitly cofinal schedule.
This proves enclosure production, not root separation or a decision theorem. -/
theorem rootInterval_progress (root : RealAlgebraicNumber)
    (schedule : Nat → Nat)
    (hprecision : Filter.Tendsto schedule Filter.atTop Filter.atTop)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K : Nat, ∀ k ≥ K, ∃ interval,
      rootInterval root (schedule k) = some interval ∧
      HexRealRootsMathlib.Dyadic.toReal interval.lower < root.toReal ∧
      root.toReal < HexRealRootsMathlib.Dyadic.toReal interval.upper ∧
      HexRealRootsMathlib.Dyadic.toReal interval.upper -
        HexRealRootsMathlib.Dyadic.toReal interval.lower < epsilon := by
  obtain ⟨N, hN⟩ := precision_small (epsilon / 4) (by positivity)
  have he := hprecision.eventually (Filter.eventually_ge_atTop N)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp he
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨interval, produced, hlo, hhi, hwidth⟩ := rootInterval_spec root (schedule k)
  refine ⟨interval, produced, hlo, hhi, ?_⟩
  have hsmall := hN (schedule k) (hK k hk)
  linarith

/-- The canonical solver receives precisely the interpreted dense head. -/
theorem solver_polynomial (head : DensePoly RealAlgebraicNumber) :
    (RealAlgebraicPoly.ofArray head.toArray).toPolynomial =
      interpret RealAlgebraicNumber.toReal algebraic_zero head := by
  ext n
  rw [RealAlgebraicPoly.coeff_ofArray, HexPolyMathlib.Interpret.coeff_interpret]
  exact congrArg RealAlgebraicNumber.toReal (DensePoly.toArray_getD head n)

/-- Finite interval proposals exist for every nonzero head and every precision.
Separation and replay acceptance remain separate obligations. -/
theorem proposeIsolations_isSome [RealAlgebraicNumber.Laws]
    (head : DensePoly RealAlgebraicNumber) (hhead : head ≠ 0) (precision : Nat) :
    (proposeIsolations head precision).isSome = true := by
  classical
  have hpoly : (RealAlgebraicPoly.ofArray head.toArray).toPolynomial ≠ 0 := by
    rw [solver_polynomial]
    exact fun h => hhead ((interpret_eq_zero RealAlgebraicNumber.toReal algebraic_zero head).mp h)
  cases hroots : (RealAlgebraicPoly.ofArray head.toArray).roots with
  | all =>
      exact False.elim (hpoly ((RealAlgebraicPoly.roots_all_iff _).mp hroots))
  | finite roots =>
      let interval := fun r : RealRootCount => (rootInterval_spec r.root precision).choose
      have hinterval : (fun r : RealRootCount => rootInterval r.root precision) =
          (fun r => (pure (interval r) : Option DyadicInterval)) := by
        funext r
        exact (rootInterval_spec r.root precision).choose_spec.1
      have hmap : roots.mapM (fun r => rootInterval r.root precision) =
          some (roots.map interval) := by
        rw [hinterval]
        exact Array.mapM_pure
      simp [proposeIsolations, hroots, RealRootSet.finite?, hmap]

/-- Zero has a universal root set, so no finite proposal is returned. -/
theorem proposeIsolations_zero [RealAlgebraicNumber.Laws] (precision : Nat) :
    proposeIsolations (0 : DensePoly RealAlgebraicNumber) precision = none := by
  have hroots : (RealAlgebraicPoly.ofArray
      (0 : DensePoly RealAlgebraicNumber).toArray).roots = .all := by
    apply (RealAlgebraicPoly.roots_all_iff _).mpr
    rw [solver_polynomial]
    exact interpret_zero RealAlgebraicNumber.toReal algebraic_zero
  simp [proposeIsolations, hroots, RealRootSet.finite?]

/-- The producer's only finite-proposal obstruction is the universal root set. -/
theorem proposeIsolations_isSome_iff [RealAlgebraicNumber.Laws]
    (head : DensePoly RealAlgebraicNumber) (precision : Nat) :
    (proposeIsolations head precision).isSome = true ↔ head ≠ 0 := by
  constructor
  · intro h hzero
    subst head
    rw [proposeIsolations_zero] at h
    contradiction
  · exact fun h => proposeIsolations_isSome head h precision

/-- The actual specialized carrier always has finite interval proposals,
including formulas whose atoms specialize to zero or constants. -/
theorem carrier_proposals [RealAlgebraicNumber.Laws]
    (values : Fin n → RealAlgebraicNumber) (formula : RealFormula.QF (n + 1))
    (precision : Nat) :
    (proposeIsolations (Specialize.product values formula) precision).isSome = true :=
  proposeIsolations_isSome _ (Specialize.product_ne_zero values formula) precision

end Hex.RCF.RealCoefficients
