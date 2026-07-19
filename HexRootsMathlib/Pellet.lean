/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Rouche
public import HexRootsMathlib.RootFree

public section

/-!
# Pellet's theorem and executable witness soundness

The generic theorem is the usual application of Rouché's theorem to one
monomial.  The remainder of the file connects its exact coefficient
inequality to the dyadic three-radius witness used by `HexRoots`.
-/

open Complex Metric Polynomial Set Finset

namespace HexRootsMathlib

noncomputable section

/-- Writing an omitted summand as an erased range or as an `if` gives the
same finite sum. -/
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
      intro i hi
      by_cases hik : i = k <;> simp [hik]

/-- The coefficient-dominance hypothesis is exactly the boundary inequality
needed by Rouché's theorem. -/
private theorem pellet_norm_sub_lt {p : ℂ[X]} {n k : ℕ} {r : ℝ}
    (hn : p.natDegree < n) (hk : k < n)
    (hdom :
      (∑ i ∈ (Finset.range n).erase k, ‖p.coeff i‖ * r ^ i) <
        ‖p.coeff k‖ * r ^ k)
    {z : ℂ} (hz : z ∈ sphere 0 r) :
    ‖p.eval z - (monomial k (p.coeff k)).eval z‖ <
      ‖(monomial k (p.coeff k)).eval z‖ := by
  have hzr : ‖z‖ = r := by
    simpa only [mem_sphere, dist_zero_right] using hz
  have heval :
      (p - monomial k (p.coeff k)).eval z =
        ∑ i ∈ (Finset.range n).erase k, p.coeff i * z ^ i := by
    rw [eval_sub, eval_monomial, eval_eq_sum_range' hn]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hk)]
    ring
  rw [← eval_sub, heval]
  calc
    ‖∑ i ∈ (Finset.range n).erase k, p.coeff i * z ^ i‖ ≤
        ∑ i ∈ (Finset.range n).erase k, ‖p.coeff i * z ^ i‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ (Finset.range n).erase k, ‖p.coeff i‖ * r ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, norm_pow, hzr]
    _ < ‖p.coeff k‖ * r ^ k := hdom
    _ = ‖(monomial k (p.coeff k)).eval z‖ := by
      rw [eval_monomial, norm_mul, norm_pow, hzr]

/-- **Pellet's theorem.** If the `k`-th term strictly dominates all other
terms on a circle, then the polynomial has exactly `k` roots in its open
disc, counted with multiplicity. -/
theorem pellet {p : ℂ[X]} {n k : ℕ} {r : ℝ} (hn : p.natDegree < n)
    (hk : k < n) (hr : 0 ≤ r)
    (hdom :
      (∑ i ∈ (Finset.range n).erase k, ‖p.coeff i‖ * r ^ i) <
        ‖p.coeff k‖ * r ^ k) :
    rootsInDisc p 0 r = k := by
  classical
  have hsum : 0 ≤ ∑ i ∈ (Finset.range n).erase k, ‖p.coeff i‖ * r ^ i := by
    positivity
  have hterm : 0 < ‖p.coeff k‖ * r ^ k := hsum.trans_lt hdom
  have hcoeff : p.coeff k ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_mul] at hterm
    exact hterm.false
  have hrpos : k ≠ 0 → 0 < r := by
    intro hk0
    have hrpow : 0 < r ^ k := by
      rcases (mul_pos_iff.mp hterm) with hpos | hneg
      · exact hpos.2
      · exact (not_lt_of_ge (norm_nonneg _) hneg.1).elim
    by_contra hnot
    have hrzero : r = 0 := le_antisymm (not_lt.mp hnot) hr
    subst r
    simp [hk0] at hrpow
  calc
    rootsInDisc p 0 r = rootsInDisc (monomial k (p.coeff k)) 0 r := by
      apply rouche hr
      intro z hz
      exact pellet_norm_sub_lt hn hk hdom hz
    _ = k := by
      unfold rootsInDisc
      rw [roots_monomial hcoeff]
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hr' : 0 < r := hrpos hk0
        have hz : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr'
        rw [Multiset.countP_nsmul]
        change k * Multiset.countP (fun a : ℂ => a ∈ ball 0 r)
          ((0 : ℂ) ::ₘ 0) = k
        rw [Multiset.countP_cons_of_pos (0 : Multiset ℂ) hz]
        simp

/-- Under Pellet dominance the polynomial has no zero on the boundary
circle. -/
theorem pellet_ne_zero {p : ℂ[X]} {n k : ℕ} {r : ℝ}
    (hn : p.natDegree < n) (hk : k < n)
    (hdom :
      (∑ i ∈ (Finset.range n).erase k, ‖p.coeff i‖ * r ^ i) <
        ‖p.coeff k‖ * r ^ k)
    {z : ℂ} (hz : z ∈ sphere 0 r) : p.eval z ≠ 0 := by
  intro hpz
  have hlt := pellet_norm_sub_lt hn hk hdom hz
  rw [hpz, zero_sub, norm_neg] at hlt
  exact hlt.false

/-! ### Executable dyadic inequalities -/

/-- A successful executable Pellet check names an actual stored
coefficient. -/
theorem pelletAt_size {cs : Array Hex.GaussDyadic} {k : ℕ}
    {rlo rhi : _root_.Dyadic} (h : Hex.pelletAt cs k rlo rhi = true) :
    k < cs.size := by
  unfold Hex.pelletAt at h
  by_contra hk
  rw [if_neg (by omega)] at h
  contradiction

/-- A successful executable Pellet check exposes its strict real
coefficient-dominance inequality. -/
theorem pelletAt_bound {cs : Array Hex.GaussDyadic} {k : ℕ}
    {rlo rhi : _root_.Dyadic} (h : Hex.pelletAt cs k rlo rhi = true) :
    (∑ i ∈ (Finset.range cs.size).erase k,
        Dyadic.toReal (Hex.GaussDyadic.hi (cs.getD i (0, 0))) *
          Dyadic.toReal rhi ^ i) <
      Dyadic.toReal (Hex.GaussDyadic.lo (cs.getD k (0, 0))) *
        Dyadic.toReal rlo ^ k := by
  have hk := pelletAt_size h
  unfold Hex.pelletAt at h
  rw [if_pos hk] at h
  let result := (List.range cs.size).foldl
      (fun acc i =>
        let acc' := if i = k then acc.1
          else acc.1 + Hex.GaussDyadic.hi (cs.getD i (0, 0)) * acc.2
        (acc', acc.2 * rhi))
      ((0 : _root_.Dyadic), (1 : _root_.Dyadic))
  have hdyadic : result.1 < Hex.GaussDyadic.lo (cs.getD k (0, 0)) * rlo ^ k := by
    simpa [result] using of_decide_eq_true h
  have hreal := Dyadic.toReal_lt_toReal_iff.mpr hdyadic
  have hfold := (pelletFold cs k rhi cs.size).1
  rw [show Dyadic.toReal result.1 =
      (∑ i ∈ Finset.range cs.size,
        if i = k then 0 else
          Dyadic.toReal (Hex.GaussDyadic.hi (cs.getD i (0, 0))) *
            Dyadic.toReal rhi ^ i) from hfold] at hreal
  simpa only [Dyadic.toReal_mul, Dyadic.toReal_pow,
    sum_erase_range] using hreal

/-! ### Exact Taylor dominance -/

/-- Dyadic lower and upper coefficient/radius bounds imply the exact
coefficient dominance required by Pellet's theorem. -/
theorem pelletAt_dominates {p : Hex.ZPoly} {c : Hex.GaussDyadic}
    {k : ℕ} {rlo rhi : _root_.Dyadic} {r : ℝ}
    (h : Hex.pelletAt (Hex.taylor p c) k rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hlo : Dyadic.toReal rlo ≤ r)
    (hhi : r ≤ Dyadic.toReal rhi) :
    let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))
    (∑ i ∈ (Finset.range p.size).erase k, ‖q.coeff i‖ * r ^ i) <
      ‖q.coeff k‖ * r ^ k := by
  dsimp only
  let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))
  have hr : 0 ≤ r := hrlo.trans hlo
  calc
    (∑ i ∈ (Finset.range p.size).erase k, ‖q.coeff i‖ * r ^ i) ≤
        ∑ i ∈ (Finset.range p.size).erase k,
          Dyadic.toReal
              (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) *
            Dyadic.toReal rhi ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoeff : ‖q.coeff i‖ ≤ Dyadic.toReal
          (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) := by
        rw [show q.coeff i =
            GaussDyadic.toComplex ((Hex.taylor p c).getD i (0, 0)) by
          exact (taylor_coeff p c i).symm]
        exact GaussDyadic.norm_le_hi _
      have hrhi : 0 ≤ Dyadic.toReal rhi := hr.trans hhi
      have hhi0 : 0 ≤ Dyadic.toReal
          (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) :=
        (norm_nonneg _).trans hcoeff
      gcongr
    _ < Dyadic.toReal
          (Hex.GaussDyadic.lo ((Hex.taylor p c).getD k (0, 0))) *
        Dyadic.toReal rlo ^ k := by
      simpa only [Hex.taylor_size] using pelletAt_bound h
    _ ≤ ‖q.coeff k‖ * r ^ k := by
      have hcoeff : Dyadic.toReal
          (Hex.GaussDyadic.lo ((Hex.taylor p c).getD k (0, 0))) ≤
          ‖q.coeff k‖ := by
        rw [show q.coeff k =
            GaussDyadic.toComplex ((Hex.taylor p c).getD k (0, 0)) by
          exact (taylor_coeff p c k).symm]
        exact GaussDyadic.lo_le_norm _
      have hlo0 : 0 ≤ Dyadic.toReal
          (Hex.GaussDyadic.lo ((Hex.taylor p c).getD k (0, 0))) := by
        rw [GaussDyadic.toReal_lo]
        positivity
      gcongr

/-- One successful executable check implies exact Pellet soundness for any
real radius lying between the supplied dyadic lower and upper bounds. -/
theorem pelletAt_rootsInDisc {p : Hex.ZPoly} {c : Hex.GaussDyadic}
    {k : ℕ} {rlo rhi : _root_.Dyadic} {r : ℝ}
    (h : Hex.pelletAt (Hex.taylor p c) k rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hlo : Dyadic.toReal rlo ≤ r)
    (hhi : r ≤ Dyadic.toReal rhi) :
    rootsInDisc ((toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))) 0 r = k := by
  let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))
  have hk : k < p.size := by
    have := pelletAt_size h
    simpa only [Hex.taylor_size] using this
  have hp : 0 < p.size := Nat.zero_lt_of_lt hk
  have hdegree : q.natDegree < p.size :=
    shift_natDegree_lt_size p hp (GaussDyadic.toComplex c)
  have hr : 0 ≤ r := hrlo.trans hlo
  exact pellet hdegree hk hr (pelletAt_dominates h hrlo hlo hhi)

/-- The same executable check excludes roots from the boundary circle at
every real radius between its dyadic bounds. -/
theorem pelletAt_ne_zero {p : Hex.ZPoly} {c : Hex.GaussDyadic}
    {k : ℕ} {rlo rhi : _root_.Dyadic} {r : ℝ}
    (h : Hex.pelletAt (Hex.taylor p c) k rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hlo : Dyadic.toReal rlo ≤ r)
    (hhi : r ≤ Dyadic.toReal rhi)
    {z : ℂ} (hz : z ∈ sphere 0 r) :
    ((toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))).eval z ≠ 0 := by
  let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))
  have hk : k < p.size := by
    have := pelletAt_size h
    simpa only [Hex.taylor_size] using this
  have hp : 0 < p.size := Nat.zero_lt_of_lt hk
  have hdegree : q.natDegree < p.size :=
    shift_natDegree_lt_size p hp (GaussDyadic.toComplex c)
  exact pellet_ne_zero hdegree hk (pelletAt_dominates h hrlo hlo hhi) hz

/-- Translating the variable translates every root without changing its
multiplicity or its membership in the corresponding open disc. -/
theorem rootsInDisc_comp_X_add_C (p : ℂ[X]) (c : ℂ) (r : ℝ) :
    rootsInDisc (p.comp (X + C c)) 0 r = rootsInDisc p c r := by
  have hroots := roots_comp_C_mul_X_add_C p 1 c isUnit_one
  simp only [C_1, one_mul, Ring.inverse_one] at hroots
  unfold rootsInDisc
  rw [hroots]
  generalize p.roots = roots
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons a roots ih =>
      rw [Multiset.map_cons, Multiset.countP_cons, Multiset.countP_cons, ih]
      congr 1
      simp only [Metric.mem_ball, Complex.dist_eq, sub_zero]

/-- The executable check excludes roots from the corresponding circle about
the original Taylor centre. -/
theorem pelletAt_ne_zero_center {p : Hex.ZPoly} {c : Hex.GaussDyadic}
    {k : ℕ} {rlo rhi : _root_.Dyadic} {r : ℝ}
    (h : Hex.pelletAt (Hex.taylor p c) k rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hlo : Dyadic.toReal rlo ≤ r)
    (hhi : r ≤ Dyadic.toReal rhi)
    {z : ℂ} (hz : z ∈ sphere (GaussDyadic.toComplex c) r) :
    (toPolyℂ p).eval z ≠ 0 := by
  have hz' : z - GaussDyadic.toComplex c ∈ sphere 0 r := by
    simpa only [mem_sphere, Complex.dist_eq, sub_zero] using hz
  have hshift := pelletAt_ne_zero h hrlo hlo hhi hz'
  intro hpz
  apply hshift
  rw [eval_comp, eval_add, eval_X, eval_C]
  simpa only [sub_add_cancel] using hpz

namespace PelletWitness

/-- The three Boolean checks contained in an executable witness. -/
theorem checks {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) :
    (Hex.pelletAt (Hex.taylor p s.center) k s.radiusLo s.radiusHi = true ∧
      Hex.pelletAt (Hex.taylor p s.center) k
        (s.radiusLo <<< (1 : Int)) (s.radiusHi <<< (1 : Int)) = true) ∧
      Hex.pelletAt (Hex.taylor p s.center) k
        (s.radiusLo <<< (2 : Int)) (s.radiusHi <<< (2 : Int)) = true := by
  unfold Hex.witness Hex.witnessCheck at h
  simpa only [Bool.and_eq_true] using h

private theorem radiusLo_nonneg (s : Hex.DyadicSquare) :
    0 ≤ Dyadic.toReal s.radiusLo := by
  simp only [Hex.DyadicSquare.radiusLo, Dyadic.toReal_ofIntWithPrec]
  positivity

private theorem radiusLo_two_nonneg (s : Hex.DyadicSquare) :
    0 ≤ Dyadic.toReal (s.radiusLo <<< (1 : Int)) := by
  rw [Dyadic.toReal_shiftLeft]
  rw [show (2 : ℝ) ^ (1 : Int) = 2 by norm_num]
  exact mul_nonneg (radiusLo_nonneg s) (by norm_num)

private theorem radiusLo_two_le (s : Hex.DyadicSquare) :
    Dyadic.toReal (s.radiusLo <<< (1 : Int)) ≤ 2 * DyadicSquare.radius s := by
  rw [Dyadic.toReal_shiftLeft]
  rw [show (2 : ℝ) ^ (1 : Int) = 2 by norm_num]
  calc
    Dyadic.toReal s.radiusLo * 2 = 2 * Dyadic.toReal s.radiusLo := mul_comm _ _
    _ ≤ 2 * DyadicSquare.radius s :=
      mul_le_mul_of_nonneg_left (DyadicSquare.radiusLo_lt_radius s).le (by norm_num)

private theorem radius_two_le_hi (s : Hex.DyadicSquare) :
    2 * DyadicSquare.radius s ≤ Dyadic.toReal (s.radiusHi <<< (1 : Int)) := by
  rw [Dyadic.toReal_shiftLeft]
  rw [show (2 : ℝ) ^ (1 : Int) = 2 by norm_num]
  calc
    2 * DyadicSquare.radius s ≤ 2 * Dyadic.toReal s.radiusHi :=
      mul_le_mul_of_nonneg_left (DyadicSquare.radius_lt_radiusHi s).le (by norm_num)
    _ = Dyadic.toReal s.radiusHi * 2 := mul_comm _ _

private theorem radiusLo_four_nonneg (s : Hex.DyadicSquare) :
    0 ≤ Dyadic.toReal (s.radiusLo <<< (2 : Int)) := by
  rw [Dyadic.toReal_shiftLeft]
  rw [show (2 : ℝ) ^ (2 : Int) = 4 by norm_num]
  exact mul_nonneg (radiusLo_nonneg s) (by norm_num)

private theorem radiusLo_four_le (s : Hex.DyadicSquare) :
    Dyadic.toReal (s.radiusLo <<< (2 : Int)) ≤ 4 * DyadicSquare.radius s := by
  rw [Dyadic.toReal_shiftLeft]
  rw [show (2 : ℝ) ^ (2 : Int) = 4 by norm_num]
  calc
    Dyadic.toReal s.radiusLo * 4 = 4 * Dyadic.toReal s.radiusLo := mul_comm _ _
    _ ≤ 4 * DyadicSquare.radius s :=
      mul_le_mul_of_nonneg_left (DyadicSquare.radiusLo_lt_radius s).le (by norm_num)

private theorem radius_four_le_hi (s : Hex.DyadicSquare) :
    4 * DyadicSquare.radius s ≤ Dyadic.toReal (s.radiusHi <<< (2 : Int)) := by
  rw [Dyadic.toReal_shiftLeft]
  rw [show (2 : ℝ) ^ (2 : Int) = 4 by norm_num]
  calc
    4 * DyadicSquare.radius s ≤ 4 * Dyadic.toReal s.radiusHi :=
      mul_le_mul_of_nonneg_left (DyadicSquare.radius_lt_radiusHi s).le (by norm_num)
    _ = Dyadic.toReal s.radiusHi * 4 := mul_comm _ _

/-- A Pellet witness certifies exactly `k` roots in the square's
circumscribed open disc. -/
theorem roots {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s) (DyadicSquare.radius s) = k := by
  have hs := pelletAt_rootsInDisc (checks h).1.1 (radiusLo_nonneg s)
    (DyadicSquare.radiusLo_lt_radius s).le
    (DyadicSquare.radius_lt_radiusHi s).le
  simpa only [DyadicSquare.center_eq, rootsInDisc_comp_X_add_C] using hs

/-- The second check certifies the same root count in the doubled disc. -/
theorem roots_two {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (2 * DyadicSquare.radius s) = k := by
  have hs := pelletAt_rootsInDisc (checks h).1.2 (radiusLo_two_nonneg s)
    (radiusLo_two_le s) (radius_two_le_hi s)
  simpa only [DyadicSquare.center_eq, rootsInDisc_comp_X_add_C] using hs

/-- The third check certifies the same root count in the quadrupled disc. -/
theorem roots_four {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (4 * DyadicSquare.radius s) = k := by
  have hs := pelletAt_rootsInDisc (checks h).2 (radiusLo_four_nonneg s)
    (radiusLo_four_le s) (radius_four_le_hi s)
  simpa only [DyadicSquare.center_eq, rootsInDisc_comp_X_add_C] using hs

/-- The strict base-radius inequality excludes boundary roots. -/
theorem boundary {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply pelletAt_ne_zero_center (checks h).1.1 (radiusLo_nonneg s)
    (DyadicSquare.radiusLo_lt_radius s).le
    (DyadicSquare.radius_lt_radiusHi s).le
  simpa only [DyadicSquare.center_eq] using hz

/-- The doubled-radius inequality excludes boundary roots. -/
theorem boundary_two {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (2 * DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply pelletAt_ne_zero_center (checks h).1.2 (radiusLo_two_nonneg s)
    (radiusLo_two_le s) (radius_two_le_hi s)
  simpa only [DyadicSquare.center_eq] using hz

/-- The quadrupled-radius inequality excludes boundary roots. -/
theorem boundary_four {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (4 * DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply pelletAt_ne_zero_center (checks h).2 (radiusLo_four_nonneg s)
    (radiusLo_four_le s) (radius_four_le_hi s)
  simpa only [DyadicSquare.center_eq] using hz

/-- The `k = 1` Pellet disjunct certifies one interior simple root, unique in
the closed circumscribed disc. -/
theorem sound {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.witness p s 1) :
    ∃ z, (toPolyℂ p).eval z = 0 ∧
      z ∈ DyadicSquare.disc s ∧
      (toPolyℂ p).derivative.eval z ≠ 0 ∧
      ∀ w, (toPolyℂ p).eval w = 0 →
        w ∈ DyadicSquare.closedDisc s → w = z := by
  classical
  let q := toPolyℂ p
  let c := DyadicSquare.center s
  let r := DyadicSquare.radius s
  have hcount : rootsInDisc q c r = 1 := roots h
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero] at hcount
    simp [rootsInDisc] at hcount
  have hcard : (q.roots.filter fun z => z ∈ ball c r).card = 1 := by
    rw [← Multiset.countP_eq_card_filter]
    exact hcount
  obtain ⟨z, hfilter⟩ := Multiset.card_eq_one.mp hcard
  have hzfilter : z ∈ q.roots.filter fun z => z ∈ ball c r := by
    rw [hfilter]
    simp
  have hzrootMem : z ∈ q.roots := (Multiset.mem_filter.mp hzfilter).1
  have hzball : z ∈ ball c r := (Multiset.mem_filter.mp hzfilter).2
  have hzroot : q.eval z = 0 := (mem_roots hq).mp hzrootMem
  have hmultiplicity : q.rootMultiplicity z = 1 := by
    rw [← count_roots q]
    calc
      q.roots.count z = (q.roots.filter fun w => w ∈ ball c r).count z :=
        (Multiset.count_filter_of_pos hzball).symm
      _ = 1 := by rw [hfilter]; simp
  have hzderiv : q.derivative.eval z ≠ 0 := by
    intro hzderiv
    have hmultiple := (one_lt_rootMultiplicity_iff_isRoot hq).2 ⟨hzroot, hzderiv⟩
    rw [hmultiplicity] at hmultiple
    omega
  refine ⟨z, hzroot, ?_, hzderiv, ?_⟩
  · exact hzball
  · intro w hwroot hwclosed
    have hwle : dist w c ≤ r := by
      simpa only [DyadicSquare.closedDisc, c, r, mem_closedBall] using hwclosed
    have hwne : dist w c ≠ r := by
      intro hweq
      have hwsphere : w ∈ sphere (DyadicSquare.center s)
          (DyadicSquare.radius s) := by
        rw [mem_sphere]
        simpa only [c, r] using hweq
      exact (boundary h hwsphere) hwroot
    have hwball : w ∈ ball c r := mem_ball.mpr (lt_of_le_of_ne hwle hwne)
    have hwrootMem : w ∈ q.roots := (mem_roots hq).mpr hwroot
    have hwfilter : w ∈ q.roots.filter fun z => z ∈ ball c r :=
      Multiset.mem_filter.mpr ⟨hwrootMem, hwball⟩
    rw [hfilter] at hwfilter
    simpa using hwfilter

end PelletWitness

namespace DyadicRootCluster

/-- A certified cluster contains exactly its stored multiplicity count in
the enclosing square's circumscribed disc. -/
theorem roots {p : Hex.ZPoly} (cl : Hex.DyadicRootCluster p) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center (Hex.encSquare cl.squares))
      (DyadicSquare.radius (Hex.encSquare cl.squares)) = cl.k :=
  PelletWitness.roots cl.witness

/-- A certified cluster has no root on the boundary of its certified disc. -/
theorem boundary {p : Hex.ZPoly} (cl : Hex.DyadicRootCluster p) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center (Hex.encSquare cl.squares))
      (DyadicSquare.radius (Hex.encSquare cl.squares))) :
    (toPolyℂ p).eval z ≠ 0 :=
  PelletWitness.boundary cl.witness hz

end DyadicRootCluster

end

end HexRootsMathlib
