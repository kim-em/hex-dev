/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Taylor
public import HexRootsMathlib.Geometry

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
power of the radius. -/
private theorem pelletFold (cs : Array Hex.GaussDyadic) (k : Nat)
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
        · rw [if_pos hnk, ih.1, Finset.sum_range_succ]
          simp only [hnk, if_pos, add_zero]
        · rw [if_neg hnk, Dyadic.toReal_add, Dyadic.toReal_mul, ih.1, ih.2,
            Finset.sum_range_succ]
          simp only [hnk, if_false]
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
  simp only [if_pos, pow_zero, mul_one, Nat.succ_ne_zero, if_false, add_zero] at hdom
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
theorem rootFree_size_pos {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.rootFree p s = true) : 0 < p.size := by
  unfold Hex.rootFree Hex.pelletAt at h
  rw [Hex.taylor_size] at h
  by_contra hp
  rw [if_neg (by omega)] at h
  contradiction

/-- A nonempty polynomial's shift has degree strictly below its executable
coefficient count. -/
private theorem shift_natDegree_lt_size (p : Hex.ZPoly) (hp : 0 < p.size) (c : ℂ) :
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
theorem rootFree_bound {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.rootFree p s = true) :
    (∑ i ∈ Finset.range p.size,
        if i = 0 then 0 else
          Dyadic.toReal (Hex.GaussDyadic.hi ((Hex.taylor p s.center).getD i (0, 0))) *
            Dyadic.toReal s.radiusHi ^ i) <
      Dyadic.toReal (Hex.GaussDyadic.lo ((Hex.taylor p s.center).getD 0 (0, 0))) := by
  have hsize : 0 < p.size := rootFree_size_pos h
  unfold Hex.rootFree Hex.pelletAt at h
  rw [Hex.taylor_size] at h
  rw [if_pos hsize] at h
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
theorem rootFree_ne_zero {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.rootFree p s = true) {z : ℂ}
    (hz : z ∈ Metric.ball (DyadicSquare.center s) (Dyadic.toReal s.radiusHi)) :
    (toPolyℂ p).eval z ≠ 0 := by
  let c := DyadicSquare.center s
  let d := z - c
  let q := (toPolyℂ p).comp (X + C c)
  have hsize : 0 < p.size := rootFree_size_pos h
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
        · simp only [hi0, if_false]
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
        rootFree_bound h
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
