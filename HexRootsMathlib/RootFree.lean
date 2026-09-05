/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.SoftPellet

public section

/-!
# Soundness of the elementary root-exclusion test

`Hex.rootFree` is the `k = 0` Taylor dominance inequality.  Its soundness is
only the triangle inequality: no Rouché theorem or complex integration is
needed.
-/

open Polynomial Finset

namespace HexRootsMathlib

noncomputable section

/-- Closed form of the accumulator used by `pelletAt`: its first component is
the sum with coefficient `k` omitted, and its second component is the next
power of the radius. Shared by the elementary `rootFree` proof here and the
general Pellet correspondence in `Pellet.lean`. -/
theorem pelletFold (cs : Array Hex.GaussDyadic) (k : Nat)
    (r : _root_.Dyadic) (n : Nat) :
    let result := (List.range n).foldl
        (fun acc i =>
          let acc' := if i = k then acc.1
            else acc.1 + Hex.GaussDyadic.hi (cs.getD i (0, 0)) * acc.2
          (acc', acc.2 * r))
        ((0 : _root_.Dyadic), (1 : _root_.Dyadic))
    Dyadic.toReal result.1 =
        (∑ i ∈ Finset.range n,
          if i = k then 0 else
            Dyadic.toReal (Hex.GaussDyadic.hi (cs.getD i (0, 0))) *
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
        · rw [ite_eq_left hnk, ih.1, Finset.sum_range_succ]
          simp only [hnk, ite_eq_left, add_zero]
        · rw [ite_eq_right hnk, Dyadic.toReal_add, Dyadic.toReal_mul, ih.1, ih.2,
            Finset.sum_range_succ]
          simp only [hnk, ite_false]
      · rw [Dyadic.toReal_mul, ih.2, pow_succ]

/-- A polynomial cannot vanish where its constant coefficient strictly
dominates the norms of all remaining evaluated terms. -/
private theorem eval_ne_zero_of_dominates {q : Polynomial ℂ} {z : ℂ} {n : Nat}
    (hn : q.natDegree < n)
    (hdom :
      (∑ i ∈ Finset.range n,
        if i = 0 then 0 else ‖q.coeff i‖ * ‖z‖ ^ i) < ‖q.coeff 0‖) :
    q.eval z ≠ 0 := by
  intro hz
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  rw [Polynomial.eval_eq_sum_range' hn, Finset.sum_range_succ'] at hz
  simp only [pow_zero, mul_one] at hz
  rw [Finset.sum_range_succ'] at hdom
  simp only [ite_eq_left, pow_zero, mul_one, Nat.succ_ne_zero, ite_false, add_zero] at hdom
  have hcoeff : ‖q.coeff 0‖ ≤
      ∑ i ∈ Finset.range m, ‖q.coeff (i + 1)‖ * ‖z‖ ^ (i + 1) := by
    calc
      ‖q.coeff 0‖ = ‖-(∑ i ∈ Finset.range m, q.coeff (i + 1) * z ^ (i + 1))‖ := by
        rw [eq_neg_of_add_eq_zero_right hz]
      _ = ‖∑ i ∈ Finset.range m, q.coeff (i + 1) * z ^ (i + 1)‖ := norm_neg _
      _ ≤ ∑ i ∈ Finset.range m, ‖q.coeff (i + 1) * z ^ (i + 1)‖ :=
        norm_sum_le _ _
      _ = ∑ i ∈ Finset.range m, ‖q.coeff (i + 1)‖ * ‖z‖ ^ (i + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, norm_pow]
  exact (hcoeff.trans_lt hdom).false

/-- A successful root-exclusion test can only occur for a nonempty stored
polynomial. -/
theorem exactRootFree_size_pos {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.exactRootFree p s = true) : 0 < p.size := by
  unfold Hex.exactRootFree Hex.pelletAt at h
  rw [Hex.taylor_size] at h
  by_contra hp
  rw [ite_eq_right (by omega)] at h
  contradiction

/-- A nonempty polynomial's shift has degree strictly below its executable
coefficient count. Shared by the elementary and general Pellet proofs. -/
theorem shift_natDegree_lt_size (p : Hex.ZPoly) (hp : 0 < p.size) (c : ℂ) :
    ((toPolyℂ p).comp (X + C c)).natDegree < p.size := by
  have hpoly : (toPolyℂ p).natDegree < p.size := by
    rw [natDegree_toPolyℂ]
    have hdegree : p.degree? = some (p.size - 1) := by
      simp [Hex.DensePoly.degree?, Nat.ne_of_gt hp]
    rw [hdegree, Option.getD_some]
    omega
  exact (Polynomial.natDegree_comp_le.trans_lt (by simpa using hpoly))

/-- The Boolean `rootFree` result exposes the strict real Taylor-dominance
inequality used by its soundness proof. -/
theorem exactRootFree_bound {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.exactRootFree p s = true) :
    (∑ i ∈ Finset.range p.size,
        if i = 0 then 0 else
          Dyadic.toReal (Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0))) *
            Dyadic.toReal s.radiusHi ^ i) <
      Dyadic.toReal (Hex.GaussDyadic.lo ((Hex.taylor p s.center).getD 0 (0, 0))) := by
  have hsize : 0 < p.size := exactRootFree_size_pos h
  unfold Hex.exactRootFree Hex.pelletAt at h
  rw [Hex.taylor_size] at h
  rw [ite_eq_left hsize] at h
  simp only [_root_.Dyadic.pow_zero, _root_.Dyadic.mul_one] at h
  let result := (List.range p.size).foldl
      (fun acc i =>
        let acc' := if i = 0 then acc.1 else
          acc.1 + Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0)) * acc.2
        (acc', acc.2 * s.radiusHi))
      ((0 : _root_.Dyadic), (1 : _root_.Dyadic))
  have hdyadic : result.1 <
      Hex.GaussDyadic.lo ((Hex.taylor p s.center).getD 0 (0, 0)) := by
    simpa [result] using of_decide_eq_true h
  have hreal := Dyadic.toReal_lt_toReal_iff.mpr hdyadic
  have hfold := (pelletFold (Hex.taylor p s.center) 0 s.radiusHi p.size).1
  rw [show Dyadic.toReal result.1 =
      (∑ i ∈ Finset.range p.size,
        if i = 0 then 0 else
          Dyadic.toReal (Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0))) *
            Dyadic.toReal s.radiusHi ^ i) from hfold] at hreal
  exact hreal

/-- **Elementary `T₀` soundness.** If `rootFree` succeeds, the polynomial has
no zero anywhere in the open disc using the executable upper-radius bound.
This is stronger than exclusion on the square's circumscribed disc. -/
private theorem exactRootFree_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.exactRootFree p s = true) {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  let c := DyadicSquare.center s
  let d := z - c
  let q := (toPolyℂ p).comp (X + C c)
  have hsize : 0 < p.size := exactRootFree_size_pos h
  have hdegree : q.natDegree < p.size := shift_natDegree_lt_size p hsize c
  have hdist : ‖d‖ < Dyadic.toReal s.radiusHi := by
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    simpa only [d] using hz
  have hdom :
      (∑ i ∈ Finset.range p.size,
        if i = 0 then 0 else ‖q.coeff i‖ * ‖d‖ ^ i) < ‖q.coeff 0‖ := by
    calc
      (∑ i ∈ Finset.range p.size,
          if i = 0 then 0 else ‖q.coeff i‖ * ‖d‖ ^ i) ≤
          ∑ i ∈ Finset.range p.size,
            if i = 0 then 0 else
              Dyadic.toReal
                  (Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0))) *
                Dyadic.toReal s.radiusHi ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hi0 : i = 0
        · simp [hi0]
        · simp only [hi0, ite_false]
          have hcoeff : ‖q.coeff i‖ ≤ Dyadic.toReal
              (Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0))) := by
            rw [show q.coeff i =
                GaussDyadic.toComplex ((Hex.taylor p s.center).getD i (0, 0)) by
              change ((toPolyℂ p).comp
                (X + C (GaussDyadic.toComplex s.center))).coeff i = _
              exact (taylor_coeff p s.center i).symm]
            exact GaussDyadic.norm_le_hi _
          have hpow : ‖d‖ ^ i ≤ Dyadic.toReal s.radiusHi ^ i := by
            gcongr
          have hhi : 0 ≤ Dyadic.toReal
              (Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0))) :=
            (norm_nonneg _).trans hcoeff
          exact mul_le_mul hcoeff hpow (pow_nonneg (norm_nonneg _) _)
            hhi
      _ < Dyadic.toReal
          (Hex.GaussDyadic.lo ((Hex.taylor p s.center).getD 0 (0, 0))) :=
        exactRootFree_bound h
      _ ≤ ‖q.coeff 0‖ := by
        rw [show q.coeff 0 =
            GaussDyadic.toComplex ((Hex.taylor p s.center).getD 0 (0, 0)) by
          change ((toPolyℂ p).comp
            (X + C (GaussDyadic.toComplex s.center))).coeff 0 = _
          exact (taylor_coeff p s.center 0).symm]
        exact GaussDyadic.lo_le_norm _
  have hq : q.eval d ≠ 0 := eval_ne_zero_of_dominates hdegree hdom
  intro hpz
  apply hq
  change ((toPolyℂ p).comp (X + C c)).eval d = 0
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  simpa only [d, c, sub_add_cancel] using hpz

private theorem softPelletZero_eval {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    {rlo rhi : _root_.Dyadic} (henclose : BallsEnclose cs q)
    (hcheck : Hex.softPelletAt cs 0 rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo) (hlo : Dyadic.toReal rlo ≤ Dyadic.toReal rhi)
    {z : ℂ} (hz : ‖z‖ < Dyadic.toReal rhi) : q.eval z ≠ 0 := by
  have hdomR := softPelletAt_dominates henclose hcheck hrlo hlo le_rfl
  have hdomR' :
      (∑ i ∈ Finset.range cs.size,
        if i = 0 then 0 else ‖q.coeff i‖ * Dyadic.toReal rhi ^ i) <
          ‖q.coeff 0‖ := by
    simpa only [sum_erase_range, pow_zero, mul_one] using hdomR
  have hdomZ :
      (∑ i ∈ Finset.range cs.size,
        if i = 0 then 0 else ‖q.coeff i‖ * ‖z‖ ^ i) < ‖q.coeff 0‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range cs.size,
          if i = 0 then 0 else ‖q.coeff i‖ * Dyadic.toReal rhi ^ i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = 0
        · simp [hi]
        · simp only [hi, ite_false]
          gcongr
      _ < ‖q.coeff 0‖ := hdomR'
  exact eval_ne_zero_of_dominates henclose.degree_lt hdomZ

private theorem softRootFreeLoop_size {bits rounds : Nat}
    {cs : Array Hex.CoeffBall} {rlo rhi : _root_.Dyadic}
    (h : Hex.softRootFreeLoop bits rounds cs rlo rhi = true) : 0 < cs.size := by
  induction rounds generalizing cs rlo rhi with
  | zero => exact softPelletAt_size h
  | succ rounds ih =>
      simp only [Hex.softRootFreeLoop, Bool.or_eq_true] at h
      rcases h with hnow | hlater
      · exact softPelletAt_size hnow
      · have hs := ih hlater
        simpa [Hex.graeffe] using hs

private theorem softRootFreeLoop_eval {cs : Array Hex.CoeffBall} {q : ℂ[X]}
    {bits rounds : Nat} {rlo rhi : _root_.Dyadic}
    (henclose : BallsEnclose cs q)
    (hcheck : Hex.softRootFreeLoop bits rounds cs rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo) (hlo : Dyadic.toReal rlo ≤ Dyadic.toReal rhi)
    {z : ℂ} (hz : ‖z‖ < Dyadic.toReal rhi) : q.eval z ≠ 0 := by
  induction rounds generalizing cs q rlo rhi z with
  | zero => exact softPelletZero_eval henclose hcheck hrlo hlo hz
  | succ rounds ih =>
      simp only [Hex.softRootFreeLoop, Bool.or_eq_true] at hcheck
      rcases hcheck with hnow | hlater
      · exact softPelletZero_eval henclose hnow hrlo hlo hz
      · have hhi : 0 ≤ Dyadic.toReal rhi := hrlo.trans hlo
        have hrlo' : 0 ≤ Dyadic.toReal (rlo * rlo) := by
          simp only [Dyadic.toReal_mul]
          positivity
        have hlo' :
            Dyadic.toReal (rlo * rlo) ≤ Dyadic.toReal (rhi * rhi) := by
          simp only [Dyadic.toReal_mul]
          nlinarith
        have hz' : ‖z ^ 2‖ < Dyadic.toReal (rhi * rhi) := by
          rw [norm_pow, Dyadic.toReal_mul]
          nlinarith [norm_nonneg z]
        have hrec := ih (graeffe_enclosePoly henclose bits) hlater hrlo' hlo' hz'
        intro hqz
        apply hrec
        have heval := congrArg (fun f : ℂ[X] => f.eval z) (expand_graeffePoly q)
        rw [expand_eval, eval_mul, eval_comp, eval_neg, eval_X] at heval
        rw [heval, hqz, zero_mul]

private theorem firstSoftRootCount_zero {cs : Array Hex.CoeffBall}
    {rlo rhi : _root_.Dyadic} {ks : List Nat}
    (h : Hex.firstSoftRootCount? cs rlo rhi ks = some 0) :
    Hex.softPelletAt cs 0 rlo rhi = true := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
      unfold Hex.firstSoftRootCount? at h
      split at h <;> rename_i hcheck
      · have hk : k = 0 := by simpa using h
        simpa [hk] using hcheck
      · exact ih h

private theorem softRootCountLoop_zero {bits rounds : Nat} {ks : List Nat}
    {cs : Array Hex.CoeffBall} {rlo rhi : _root_.Dyadic}
    (h : Hex.softRootCountLoop bits ks rounds cs rlo rhi = some 0) :
    Hex.softRootFreeLoop bits rounds cs rlo rhi = true := by
  induction rounds generalizing cs rlo rhi with
  | zero => exact firstSoftRootCount_zero h
  | succ rounds ih =>
      unfold Hex.softRootCountLoop at h
      split at h <;> rename_i hfirst
      · rename_i k
        have hk : k = 0 := by simpa using h
        subst k
        simp [Hex.softRootFreeLoop, firstSoftRootCount_zero hfirst]
      · have hrec := ih h
        simp [Hex.softRootFreeLoop, hrec]

private theorem rootFreeLoop_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {bits : Nat} {cs : Array Hex.CoeffBall}
    (henclose : BallsEnclose cs (localPoly p s))
    (hcheck : Hex.softRootFreeLoop bits (Hex.graeffeRounds (p.degree?.getD 0))
      cs Hex.softSqrt2Lo Hex.softSqrt2Hi = true)
    {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  let q := localPoly p s
  let R := Dyadic.toReal Hex.softSqrt2Hi
  have hrlo : 0 ≤ Dyadic.toReal Hex.softSqrt2Lo := by
    simp [Hex.softSqrt2Lo, Dyadic.toReal_ofIntWithPrec]
  have hlo : Dyadic.toReal Hex.softSqrt2Lo ≤ R := by
    change Dyadic.toReal Hex.sqrt2Lo ≤ Dyadic.toReal Hex.sqrt2Hi
    exact sqrt2Lo_lt_sqrt_two.le.trans sqrt_two_lt_sqrt2Hi.le
  let width : ℝ := Dyadic.toReal (.ofIntWithPrec 1 s.prec)
  let c : ℂ := DyadicSquare.center s
  let w : ℂ := (width : ℂ)⁻¹ * (z - c)
  have hwidth : 0 < width := by
    simp only [width, Dyadic.toReal_ofIntWithPrec]
    positivity
  have hwidthEq : width = DyadicSquare.halfWidth s := by
    simp [width, DyadicSquare.halfWidth_eq, Dyadic.toReal_ofIntWithPrec]
  have hwNorm : ‖w‖ < R := by
    simp only [w, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwidth]
    have hdist : dist z c < width * R := by
      have hz' : dist z c < Dyadic.toReal s.radiusHi := by
        simpa only [Metric.mem_ball, c] using hz
      rw [DyadicSquare.radiusHi_eq] at hz'
      rw [hwidthEq]
      simpa only [R, Hex.softSqrt2Hi, Hex.sqrt2Hi] using hz'
    rw [show ‖z - c‖ = dist z c by rw [Complex.dist_eq]]
    exact (inv_mul_lt_iff₀ hwidth).mpr hdist
  have hqeval : q.eval w ≠ 0 := by
    apply softRootFreeLoop_eval (q := q) henclose hcheck hrlo hlo hwNorm
  have hwidthℂ : (width : ℂ) ≠ 0 := by exact_mod_cast hwidth.ne'
  have hwarg : (width : ℂ) * w + c = z := by
    dsimp only [w]
    rw [← mul_assoc, mul_inv_cancel₀ hwidthℂ, one_mul]
    ring
  intro hpz
  apply hqeval
  dsimp only [q]
  unfold localPoly
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
  have hwarg' :
      (Dyadic.toReal (.ofIntWithPrec 1 s.prec) : ℂ) * w +
        GaussDyadic.toComplex s.center = z := by
    simpa only [width, c, DyadicSquare.center_eq] using hwarg
  rw [hwarg']
  exact hpz

private theorem softRootFreeAt_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {bits : Nat} (hcheck : Hex.softRootFreeAt p s bits = true) {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  have hk : 0 < p.size := by
    have hsize := softRootFreeLoop_size hcheck
    simpa [Hex.softRootFreeAt, Hex.taylorBalls] using hsize
  apply rootFreeLoop_ne_zero (taylorBalls_enclosePoly p s bits hk) hcheck hz

private theorem softSeededCount_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hcheck : Hex.softSeededRootCount? p s (Array.range p.size).toList 64 = some 0)
    {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  have hloop := softRootCountLoop_zero hcheck
  have hk : 0 < p.size := by
    have hsize := softRootFreeLoop_size hloop
    simpa [Hex.exactTaylorBalls, Hex.seededTaylorBalls, Hex.taylor_size] using hsize
  apply rootFreeLoop_ne_zero (exactTaylorBalls_enclosePoly p s 64 hk) hloop hz

private theorem softRootFree_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.softRootFree p s = true) {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  have hcases :
      Hex.softRootFreeAt p s 64 = true ∨
      Hex.softRootFreeAt p s 128 = true ∨
      Hex.softRootFreeAt p s 256 = true := by
    simpa [Hex.softRootFree, Hex.softPrecisions] using h
  rcases hcases with h | h | h
  all_goals exact softRootFreeAt_ne_zero h hz

/-- **Combined `T₀` soundness.** The bounded-precision filter and the exact
Taylor fallback both exclude every zero from the executable upper-radius
disc. -/
theorem rootFree_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.rootFree p s = true) {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  unfold Hex.rootFree at h
  split at h
  · split at h
    · dsimp only at h
      split at h <;> rename_i hcount
      · exact softSeededCount_ne_zero hcount hz
      · exact exactRootFree_ne_zero h hz
    · simp only [Bool.or_eq_true] at h
      rcases h with hsoft | hexact
      · exact softRootFree_ne_zero hsoft hz
      · exact exactRootFree_ne_zero hexact hz
  · exact exactRootFree_ne_zero h hz

/-- A successful `rootFree` test excludes roots from the represented closed
square. -/
theorem rootFree_closedSquare {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.rootFree p s = true) {z : ℂ} (hz : z ∈ DyadicSquare.closedSquare s) :
    (toPolyℂ p).eval z ≠ 0 :=
  rootFree_ne_zero h (DyadicSquare.closedSquare_subset_ball_radiusHi s hz)

/-- The stated circumscribed closed disc is root-free as well; its radius is
strictly below the executable upper-radius bound used by `rootFree`. -/
theorem rootFree_closedDisc {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.rootFree p s = true) {z : ℂ} (hz : z ∈ DyadicSquare.closedDisc s) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply rootFree_ne_zero h
  rw [DyadicSquare.closedDisc, Metric.mem_closedBall] at hz
  rw [Metric.mem_ball]
  exact hz.trans_lt (DyadicSquare.radius_lt_radiusHi s)

end

end HexRootsMathlib
