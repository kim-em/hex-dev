/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Rouche
public import HexRootsMathlib.RootFree
public import HexRootsMathlib.SoftPellet

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

/-! ### Graeffe coefficient-ball witnesses -/

/-- The three original radii transported through the Graeffe loop. -/
private inductive SoftRadiusChoice
  | base
  | two
  | four

private def SoftRadiusChoice.lo : SoftRadiusChoice → Hex.SoftRadii → _root_.Dyadic
  | .base, rs => rs.baseLo
  | .two, rs => rs.twoLo
  | .four, rs => rs.fourLo

private def SoftRadiusChoice.hi : SoftRadiusChoice → Hex.SoftRadii → _root_.Dyadic
  | .base, rs => rs.baseHi
  | .two, rs => rs.twoHi
  | .four, rs => rs.fourHi

@[simp] private theorem SoftRadiusChoice.lo_square (choice : SoftRadiusChoice)
    (rs : Hex.SoftRadii) :
    choice.lo rs.square = choice.lo rs * choice.lo rs := by
  cases choice <;> rfl

@[simp] private theorem SoftRadiusChoice.hi_square (choice : SoftRadiusChoice)
    (rs : Hex.SoftRadii) :
    choice.hi rs.square = choice.hi rs * choice.hi rs := by
  cases choice <;> rfl

private theorem softPelletThree_at {cs : Array Hex.CoeffBall} {k : Nat}
    {rs : Hex.SoftRadii} (choice : SoftRadiusChoice)
    (h : Hex.softPelletThree cs k rs = true) :
    Hex.softPelletAt cs k (choice.lo rs) (choice.hi rs) = true := by
  cases choice <;> simp_all [Hex.softPelletThree, SoftRadiusChoice.lo,
    SoftRadiusChoice.hi]

/-- One successful coefficient-ball check gives a nonzero exact polynomial
and its Pellet root count. -/
private theorem softPelletAt_rootsInDisc {cs : Array Hex.CoeffBall}
    {q : ℂ[X]} {k : Nat} {rlo rhi : _root_.Dyadic} {r : ℝ}
    (henclose : BallsEnclose cs q)
    (h : Hex.softPelletAt cs k rlo rhi = true)
    (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hlo : Dyadic.toReal rlo ≤ r)
    (hhi : r ≤ Dyadic.toReal rhi) :
    q ≠ 0 ∧ rootsInDisc q 0 r = k := by
  have hdom := softPelletAt_dominates henclose h hrlo hlo hhi
  have hq : q ≠ 0 := by
    intro hzero
    subst q
    simp at hdom
  have hk := softPelletAt_size h
  exact ⟨hq, pellet henclose.degree_lt hk (hrlo.trans hlo) hdom⟩

/-- A successful transported Graeffe loop is sound at any one of its three
original radius intervals. -/
private theorem softGraeffeLoop_rootsInDisc {cs : Array Hex.CoeffBall}
    {q : ℂ[X]} {bits k rounds : Nat} {rs : Hex.SoftRadii}
    (choice : SoftRadiusChoice) {r : ℝ}
    (henclose : BallsEnclose cs q)
    (h : Hex.softGraeffeLoop bits k rounds cs rs = true)
    (hrlo : 0 ≤ Dyadic.toReal (choice.lo rs))
    (hlo : Dyadic.toReal (choice.lo rs) ≤ r)
    (hhi : r ≤ Dyadic.toReal (choice.hi rs)) :
    q ≠ 0 ∧ rootsInDisc q 0 r = k := by
  induction rounds generalizing cs q rs r with
  | zero =>
      exact softPelletAt_rootsInDisc henclose
        (softPelletThree_at choice h) hrlo hlo hhi
  | succ rounds ih =>
      simp only [Hex.softGraeffeLoop, Bool.or_eq_true] at h
      rcases h with hnow | hlater
      · exact softPelletAt_rootsInDisc henclose
          (softPelletThree_at choice hnow) hrlo hlo hhi
      · have hr : 0 ≤ r := hrlo.trans hlo
        have hhi0 : 0 ≤ Dyadic.toReal (choice.hi rs) := hr.trans hhi
        have hsquareLo :
            0 ≤ Dyadic.toReal (choice.lo rs.square) := by
          simp only [SoftRadiusChoice.lo_square, Dyadic.toReal_mul]
          positivity
        have hsquareLo_le :
            Dyadic.toReal (choice.lo rs.square) ≤ r ^ 2 := by
          simp only [SoftRadiusChoice.lo_square, Dyadic.toReal_mul, pow_two]
          nlinarith
        have hsquare_le_hi :
            r ^ 2 ≤ Dyadic.toReal (choice.hi rs.square) := by
          simp only [SoftRadiusChoice.hi_square, Dyadic.toReal_mul, pow_two]
          nlinarith
        have hrec := ih (graeffe_enclosePoly henclose bits) hlater
          hsquareLo hsquareLo_le hsquare_le_hi
        have hq : q ≠ 0 := by
          intro hzero
          subst q
          exact hrec.1 graeffePoly_zero
        refine ⟨hq, ?_⟩
        rw [← rootsInDisc_graeffePoly hq r hr]
        exact hrec.2

/-- Strict soft Pellet dominance also excludes roots from the transported
boundary circle, and this property pulls back through every Graeffe step. -/
private theorem softGraeffeLoop_boundary {cs : Array Hex.CoeffBall}
    {q : ℂ[X]} {bits k rounds : Nat} {rs : Hex.SoftRadii}
    (choice : SoftRadiusChoice) {r : ℝ}
    (henclose : BallsEnclose cs q)
    (h : Hex.softGraeffeLoop bits k rounds cs rs = true)
    (hrlo : 0 ≤ Dyadic.toReal (choice.lo rs))
    (hlo : Dyadic.toReal (choice.lo rs) ≤ r)
    (hhi : r ≤ Dyadic.toReal (choice.hi rs))
    {z : ℂ} (hz : z ∈ sphere 0 r) : q.eval z ≠ 0 := by
  induction rounds generalizing cs q rs r z with
  | zero =>
      have hcheck := softPelletThree_at choice h
      exact pellet_ne_zero henclose.degree_lt (softPelletAt_size hcheck)
        (softPelletAt_dominates henclose hcheck hrlo hlo hhi) hz
  | succ rounds ih =>
      simp only [Hex.softGraeffeLoop, Bool.or_eq_true] at h
      rcases h with hnow | hlater
      · have hcheck := softPelletThree_at choice hnow
        exact pellet_ne_zero henclose.degree_lt (softPelletAt_size hcheck)
          (softPelletAt_dominates henclose hcheck hrlo hlo hhi) hz
      · have hr : 0 ≤ r := hrlo.trans hlo
        have hhi0 : 0 ≤ Dyadic.toReal (choice.hi rs) := hr.trans hhi
        have hsquareLo :
            0 ≤ Dyadic.toReal (choice.lo rs.square) := by
          simp only [SoftRadiusChoice.lo_square, Dyadic.toReal_mul]
          positivity
        have hsquareLo_le :
            Dyadic.toReal (choice.lo rs.square) ≤ r ^ 2 := by
          simp only [SoftRadiusChoice.lo_square, Dyadic.toReal_mul, pow_two]
          nlinarith
        have hsquare_le_hi :
            r ^ 2 ≤ Dyadic.toReal (choice.hi rs.square) := by
          simp only [SoftRadiusChoice.hi_square, Dyadic.toReal_mul, pow_two]
          nlinarith
        have hzsq : z ^ 2 ∈ sphere 0 (r ^ 2) := by
          simp only [mem_sphere, dist_zero_right, norm_pow]
          have hzNorm : ‖z‖ = r := by
            simpa only [mem_sphere, dist_zero_right] using hz
          rw [hzNorm]
        have hnext := ih (graeffe_enclosePoly henclose bits) hlater
          hsquareLo hsquareLo_le hsquare_le_hi hzsq
        intro hzq
        apply hnext
        have hid := congrArg (fun p : ℂ[X] => p.eval z) (expand_graeffePoly q)
        simpa only [expand_eval, eval_mul, eval_comp, eval_neg, eval_X, hzq,
          zero_mul] using hid

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

/-- Scaling to square-local coordinates scales the counted disc radius by
the square half-width. -/
theorem rootsInDisc_localPoly (p : Hex.ZPoly) (s : Hex.DyadicSquare) (r : ℝ) :
    rootsInDisc (localPoly p s) 0 r =
      rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
        (Dyadic.toReal (.ofIntWithPrec 1 s.prec) * r) := by
  classical
  let h : ℝ := Dyadic.toReal (.ofIntWithPrec 1 s.prec)
  let c : ℂ := DyadicSquare.center s
  have hh : 0 < h := by
    simp only [h, Dyadic.toReal_ofIntWithPrec]
    positivity
  have hunit : IsUnit (h : ℂ) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hh.ne'
  have hroots := roots_comp_C_mul_X_add_C (toPolyℂ p) (h : ℂ) c hunit
  have hlocal : localPoly p s =
      (toPolyℂ p).comp (C (h : ℂ) * X + C c) := by
    simp only [localPoly, h, c, DyadicSquare.center_eq]
  rw [hlocal]
  unfold rootsInDisc
  rw [hroots]
  change Multiset.countP (fun z : ℂ => z ∈ ball 0 r)
      ((toPolyℂ p).roots.map fun x => Ring.inverse (h : ℂ) * (x - c)) =
    Multiset.countP (fun z : ℂ => z ∈ ball c (h * r)) (toPolyℂ p).roots
  generalize (toPolyℂ p).roots = roots
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons z roots ih =>
      rw [Multiset.map_cons, Multiset.countP_cons, Multiset.countP_cons, ih]
      congr 1
      simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_mul]
      have hinvnorm : ‖Ring.inverse (h : ℂ)‖ = h⁻¹ := by
        rw [Ring.inverse_eq_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hh]
      rw [hinvnorm]
      have hsub : ‖z - c‖ = dist z c := by rw [Complex.dist_eq]
      rw [hsub]
      have hequiv : h⁻¹ * dist z c < r ↔ dist z c < h * r :=
        inv_mul_lt_iff₀ hh
      by_cases hz : dist z c < h * r
      · simp [hz, hequiv.mpr hz]
      · have hz' : ¬h⁻¹ * dist z c < r := fun h' => hz (hequiv.mp h')
        rw [if_neg hz', if_neg hz]

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

private theorem softWitnessAt_local {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k bits : Nat} (choice : SoftRadiusChoice) {r : ℝ}
    (h : Hex.softWitnessAt p s k bits = true)
    (hrlo : 0 ≤ Dyadic.toReal (choice.lo Hex.SoftRadii.initial))
    (hlo : Dyadic.toReal (choice.lo Hex.SoftRadii.initial) ≤ r)
    (hhi : r ≤ Dyadic.toReal (choice.hi Hex.SoftRadii.initial)) :
    rootsInDisc (localPoly p s) 0 r = k := by
  have hloop : Hex.softGraeffeLoop bits k
      (Hex.graeffeRounds (p.degree?.getD 0))
      (Hex.taylorBalls p s bits) Hex.SoftRadii.initial = true := by
    simpa [Hex.softWitnessAt] using h
  have hk := softGraeffeLoop_size hloop
  have hp : 0 < p.size := by
    have hsize : (Hex.taylorBalls p s bits).size = p.size := by
      simp [Hex.taylorBalls]
    rw [hsize] at hk
    omega
  exact (softGraeffeLoop_rootsInDisc choice
    (taylorBalls_enclosePoly p s bits hp) hloop hrlo hlo hhi).2

private theorem softSeededWitness_local {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat} (choice : SoftRadiusChoice) {r : ℝ}
    (h : Hex.softSeededWitness p s k bits = true)
    (hrlo : 0 ≤ Dyadic.toReal (choice.lo Hex.SoftRadii.initial))
    (hlo : Dyadic.toReal (choice.lo Hex.SoftRadii.initial) ≤ r)
    (hhi : r ≤ Dyadic.toReal (choice.hi Hex.SoftRadii.initial)) :
    rootsInDisc (localPoly p s) 0 r = k := by
  have hloop : Hex.softGraeffeLoop bits k
      (Hex.graeffeRounds (p.degree?.getD 0))
      (Hex.exactTaylorBalls p s bits) Hex.SoftRadii.initial = true := by
    simpa [Hex.softSeededWitness] using h
  have hk := softGraeffeLoop_size hloop
  have hp : 0 < p.size := by
    have hsize : (Hex.exactTaylorBalls p s bits).size = p.size := by
      simp [Hex.exactTaylorBalls, Hex.seededTaylorBalls, Hex.taylor_size]
    rw [hsize] at hk
    omega
  exact (softGraeffeLoop_rootsInDisc choice
    (exactTaylorBalls_enclosePoly p s bits hp) hloop hrlo hlo hhi).2

private theorem softWitnessAt_local_base {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softWitnessAt p s k bits = true) :
    rootsInDisc (localPoly p s) 0 √2 = k := by
  apply softWitnessAt_local SoftRadiusChoice.base h
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal Hex.sqrt2Lo ≤ √2
    exact sqrt2Lo_lt_sqrt_two.le
  · change √2 ≤ Dyadic.toReal Hex.sqrt2Hi
    exact sqrt_two_lt_sqrt2Hi.le

private theorem softWitnessAt_local_two {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softWitnessAt p s k bits = true) :
    rootsInDisc (localPoly p s) 0 (2 * √2) = k := by
  apply softWitnessAt_local SoftRadiusChoice.two h
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (1 : Int)) ≤ 2 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 2 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (1 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softWitnessAt_local_four {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softWitnessAt p s k bits = true) :
    rootsInDisc (localPoly p s) 0 (4 * √2) = k := by
  apply softWitnessAt_local SoftRadiusChoice.four h
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (2 : Int)) ≤ 4 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 4 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (2 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softSeededWitness_local_base {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softSeededWitness p s k bits = true) :
    rootsInDisc (localPoly p s) 0 √2 = k := by
  apply softSeededWitness_local SoftRadiusChoice.base h
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal Hex.sqrt2Lo ≤ √2
    exact sqrt2Lo_lt_sqrt_two.le
  · change √2 ≤ Dyadic.toReal Hex.sqrt2Hi
    exact sqrt_two_lt_sqrt2Hi.le

private theorem softSeededWitness_local_two {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softSeededWitness p s k bits = true) :
    rootsInDisc (localPoly p s) 0 (2 * √2) = k := by
  apply softSeededWitness_local SoftRadiusChoice.two h
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (1 : Int)) ≤ 2 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 2 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (1 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softSeededWitness_local_four {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softSeededWitness p s k bits = true) :
    rootsInDisc (localPoly p s) 0 (4 * √2) = k := by
  apply softSeededWitness_local SoftRadiusChoice.four h
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (2 : Int)) ≤ 4 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 4 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (2 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softWitnessAt_local_boundary {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat} (choice : SoftRadiusChoice) {r : ℝ}
    (h : Hex.softWitnessAt p s k bits = true)
    (hrlo : 0 ≤ Dyadic.toReal (choice.lo Hex.SoftRadii.initial))
    (hlo : Dyadic.toReal (choice.lo Hex.SoftRadii.initial) ≤ r)
    (hhi : r ≤ Dyadic.toReal (choice.hi Hex.SoftRadii.initial))
    {z : ℂ} (hz : z ∈ sphere 0 r) : (localPoly p s).eval z ≠ 0 := by
  have hloop : Hex.softGraeffeLoop bits k
      (Hex.graeffeRounds (p.degree?.getD 0))
      (Hex.taylorBalls p s bits) Hex.SoftRadii.initial = true := by
    simpa [Hex.softWitnessAt] using h
  have hk := softGraeffeLoop_size hloop
  have hp : 0 < p.size := by
    have hsize : (Hex.taylorBalls p s bits).size = p.size := by
      simp [Hex.taylorBalls]
    rw [hsize] at hk
    omega
  exact softGraeffeLoop_boundary choice
    (taylorBalls_enclosePoly p s bits hp) hloop hrlo hlo hhi hz

private theorem softSeededWitness_local_boundary {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat} (choice : SoftRadiusChoice) {r : ℝ}
    (h : Hex.softSeededWitness p s k bits = true)
    (hrlo : 0 ≤ Dyadic.toReal (choice.lo Hex.SoftRadii.initial))
    (hlo : Dyadic.toReal (choice.lo Hex.SoftRadii.initial) ≤ r)
    (hhi : r ≤ Dyadic.toReal (choice.hi Hex.SoftRadii.initial))
    {z : ℂ} (hz : z ∈ sphere 0 r) : (localPoly p s).eval z ≠ 0 := by
  have hloop : Hex.softGraeffeLoop bits k
      (Hex.graeffeRounds (p.degree?.getD 0))
      (Hex.exactTaylorBalls p s bits) Hex.SoftRadii.initial = true := by
    simpa [Hex.softSeededWitness] using h
  have hk := softGraeffeLoop_size hloop
  have hp : 0 < p.size := by
    have hsize : (Hex.exactTaylorBalls p s bits).size = p.size := by
      simp [Hex.exactTaylorBalls, Hex.seededTaylorBalls, Hex.taylor_size]
    rw [hsize] at hk
    omega
  exact softGraeffeLoop_boundary choice
    (exactTaylorBalls_enclosePoly p s bits hp) hloop hrlo hlo hhi hz

private theorem softWitnessAt_boundary_base {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softWitnessAt p s k bits = true)
    {z : ℂ} (hz : z ∈ sphere 0 √2) : (localPoly p s).eval z ≠ 0 := by
  apply softWitnessAt_local_boundary SoftRadiusChoice.base h _ _ _ hz
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal Hex.sqrt2Lo ≤ √2
    exact sqrt2Lo_lt_sqrt_two.le
  · change √2 ≤ Dyadic.toReal Hex.sqrt2Hi
    exact sqrt_two_lt_sqrt2Hi.le

private theorem softWitnessAt_boundary_two {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softWitnessAt p s k bits = true)
    {z : ℂ} (hz : z ∈ sphere 0 (2 * √2)) : (localPoly p s).eval z ≠ 0 := by
  apply softWitnessAt_local_boundary SoftRadiusChoice.two h _ _ _ hz
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (1 : Int)) ≤ 2 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 2 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (1 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softWitnessAt_boundary_four {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softWitnessAt p s k bits = true)
    {z : ℂ} (hz : z ∈ sphere 0 (4 * √2)) : (localPoly p s).eval z ≠ 0 := by
  apply softWitnessAt_local_boundary SoftRadiusChoice.four h _ _ _ hz
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (2 : Int)) ≤ 4 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 4 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (2 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softSeededWitness_boundary_base {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softSeededWitness p s k bits = true)
    {z : ℂ} (hz : z ∈ sphere 0 √2) : (localPoly p s).eval z ≠ 0 := by
  apply softSeededWitness_local_boundary SoftRadiusChoice.base h _ _ _ hz
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal Hex.sqrt2Lo ≤ √2
    exact sqrt2Lo_lt_sqrt_two.le
  · change √2 ≤ Dyadic.toReal Hex.sqrt2Hi
    exact sqrt_two_lt_sqrt2Hi.le

private theorem softSeededWitness_boundary_two {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softSeededWitness p s k bits = true)
    {z : ℂ} (hz : z ∈ sphere 0 (2 * √2)) : (localPoly p s).eval z ≠ 0 := by
  apply softSeededWitness_local_boundary SoftRadiusChoice.two h _ _ _ hz
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (1 : Int)) ≤ 2 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 2 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (1 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

private theorem softSeededWitness_boundary_four {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} {k bits : Nat}
    (h : Hex.softSeededWitness p s k bits = true)
    {z : ℂ} (hz : z ∈ sphere 0 (4 * √2)) : (localPoly p s).eval z ≠ 0 := by
  apply softSeededWitness_local_boundary SoftRadiusChoice.four h _ _ _ hz
  · simp [SoftRadiusChoice.lo, Hex.SoftRadii.initial, Hex.softSqrt2Lo,
      Dyadic.toReal_shiftLeft, Dyadic.toReal_ofIntWithPrec]
    positivity
  · change Dyadic.toReal (Hex.sqrt2Lo <<< (2 : Int)) ≤ 4 * √2
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt2Lo_lt_sqrt_two]
  · change 4 * √2 ≤ Dyadic.toReal (Hex.sqrt2Hi <<< (2 : Int))
    rw [Dyadic.toReal_shiftLeft]
    norm_num
    nlinarith [sqrt_two_lt_sqrt2Hi]

/-- Boundary nonvanishing in local coordinates pulls back through the affine
square normalization. -/
private theorem localPoly_boundary_center {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {r : ℝ} (hlocal : ∀ {w : ℂ}, w ∈ sphere 0 r → (localPoly p s).eval w ≠ 0)
    {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s)
      (Dyadic.toReal (.ofIntWithPrec 1 s.prec) * r)) :
    (toPolyℂ p).eval z ≠ 0 := by
  let h : ℝ := Dyadic.toReal (.ofIntWithPrec 1 s.prec)
  let c : ℂ := DyadicSquare.center s
  have hh : 0 < h := by
    simp only [h, Dyadic.toReal_ofIntWithPrec]
    positivity
  have hhℂ : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  let w : ℂ := (h : ℂ)⁻¹ * (z - c)
  have hw : w ∈ sphere 0 r := by
    simp only [mem_sphere, dist_zero_right, w, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    have hzdist : dist z c = h * r := by
      simpa only [mem_sphere, c, h] using hz
    rw [show ‖z - c‖ = dist z c by rw [Complex.dist_eq], hzdist]
    field_simp
  have hwarg : (h : ℂ) * w + c = z := by
    dsimp only [w]
    rw [← mul_assoc, mul_inv_cancel₀ hhℂ, one_mul]
    ring
  have heval : (localPoly p s).eval w = (toPolyℂ p).eval z := by
    unfold localPoly
    rw [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_C]
    simpa only [h, c, DyadicSquare.center_eq] using
      congrArg (toPolyℂ p).eval hwarg
  intro hpz
  exact hlocal hw (heval.trans hpz)

namespace PelletWitness

/-- The public witness is either the bounded-precision Graeffe path or the
exact Taylor fallback. -/
theorem witness_cases {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.witness p s k) :
    Hex.softWitnessCheck p s k = true ∨
      Hex.TaylorShift.witnessCheck s
        (Hex.TaylorShift.compute p s.center) k = true := by
  unfold Hex.witness Hex.witnessCheck Hex.TaylorShift.combinedWitnessCheck at h
  by_cases hprec : s.prec < 32
  · rw [if_pos hprec] at h
    rw [Hex.TaylorShift.softWitnessCheck_eq] at h
    have hor : Hex.TaylorShift.witnessCheck s
        (Hex.TaylorShift.compute p s.center) k = true ∨
        Hex.softWitnessCheck p s k = true := by
      simpa only [Bool.or_eq_true] using h
    rcases hor with hexact | hsoft
    · exact Or.inr hexact
    · exact Or.inl hsoft
  · rw [if_neg hprec] at h
    rw [Hex.TaylorShift.softWitnessCheck_eq] at h
    simpa only [Bool.or_eq_true] using h

private theorem softWitnessCheck_cases {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true) :
    (Hex.softWitnessAt p s k 64 = true ∨
      Hex.softWitnessAt p s k 128 = true ∨
      Hex.softWitnessAt p s k 256 = true) ∨
      Hex.softSeededWitness p s k 64 = true := by
  by_cases hprec : s.prec < 32
  · have hor : Hex.softSeededWitness p s k 64 = true ∨
        Hex.softWitnessAt p s k 64 = true ∨
        Hex.softWitnessAt p s k 128 = true ∨
        Hex.softWitnessAt p s k 256 = true := by
      simpa [Hex.softWitnessCheck, Hex.TaylorShift.softWitnessCheck,
        Hex.TaylorShift.softSeededWitness_eq, Hex.softPrecisions, hprec] using h
    rcases hor with hseeded | hsoft
    · exact Or.inr hseeded
    · exact Or.inl hsoft
  · simpa [Hex.softWitnessCheck, Hex.TaylorShift.softWitnessCheck,
      Hex.TaylorShift.softSeededWitness_eq, Hex.softPrecisions, hprec] using h

private theorem soft_local_base {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true) :
    rootsInDisc (localPoly p s) 0 √2 = k := by
  rcases softWitnessCheck_cases h with (h | h | h) | h
  · exact softWitnessAt_local_base h
  · exact softWitnessAt_local_base h
  · exact softWitnessAt_local_base h
  · exact softSeededWitness_local_base h

private theorem soft_local_two {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true) :
    rootsInDisc (localPoly p s) 0 (2 * √2) = k := by
  rcases softWitnessCheck_cases h with (h | h | h) | h
  · exact softWitnessAt_local_two h
  · exact softWitnessAt_local_two h
  · exact softWitnessAt_local_two h
  · exact softSeededWitness_local_two h

private theorem soft_local_four {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true) :
    rootsInDisc (localPoly p s) 0 (4 * √2) = k := by
  rcases softWitnessCheck_cases h with (h | h | h) | h
  · exact softWitnessAt_local_four h
  · exact softWitnessAt_local_four h
  · exact softWitnessAt_local_four h
  · exact softSeededWitness_local_four h

private theorem soft_local_boundary_base {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true)
    {z : ℂ} (hz : z ∈ sphere 0 √2) : (localPoly p s).eval z ≠ 0 := by
  rcases softWitnessCheck_cases h with (h | h | h) | h
  · exact softWitnessAt_boundary_base h hz
  · exact softWitnessAt_boundary_base h hz
  · exact softWitnessAt_boundary_base h hz
  · exact softSeededWitness_boundary_base h hz

private theorem soft_local_boundary_two {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true)
    {z : ℂ} (hz : z ∈ sphere 0 (2 * √2)) : (localPoly p s).eval z ≠ 0 := by
  rcases softWitnessCheck_cases h with (h | h | h) | h
  · exact softWitnessAt_boundary_two h hz
  · exact softWitnessAt_boundary_two h hz
  · exact softWitnessAt_boundary_two h hz
  · exact softSeededWitness_boundary_two h hz

private theorem soft_local_boundary_four {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (h : Hex.softWitnessCheck p s k = true)
    {z : ℂ} (hz : z ∈ sphere 0 (4 * √2)) : (localPoly p s).eval z ≠ 0 := by
  rcases softWitnessCheck_cases h with (h | h | h) | h
  · exact softWitnessAt_boundary_four h hz
  · exact softWitnessAt_boundary_four h hz
  · exact softWitnessAt_boundary_four h hz
  · exact softSeededWitness_boundary_four h hz

/-- A successful soft Graeffe check certifies the base circumscribed disc. -/
theorem soft_roots {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.softWitnessCheck p s k = true) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (DyadicSquare.radius s) = k := by
  have hlocal := soft_local_base h
  rw [rootsInDisc_localPoly] at hlocal
  convert hlocal using 1
  simp only [DyadicSquare.radius_eq, Dyadic.toReal_ofIntWithPrec]
  ring_nf

/-- A successful soft Graeffe check certifies the doubled disc. -/
theorem soft_roots_two {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.softWitnessCheck p s k = true) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (2 * DyadicSquare.radius s) = k := by
  have hlocal := soft_local_two h
  rw [rootsInDisc_localPoly] at hlocal
  convert hlocal using 1
  simp only [DyadicSquare.radius_eq, Dyadic.toReal_ofIntWithPrec]
  ring_nf

/-- A successful soft Graeffe check certifies the quadrupled disc. -/
theorem soft_roots_four {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.softWitnessCheck p s k = true) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (4 * DyadicSquare.radius s) = k := by
  have hlocal := soft_local_four h
  rw [rootsInDisc_localPoly] at hlocal
  convert hlocal using 1
  simp only [DyadicSquare.radius_eq, Dyadic.toReal_ofIntWithPrec]
  ring_nf

private theorem soft_boundary {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.softWitnessCheck p s k = true) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply localPoly_boundary_center (fun hz' => soft_local_boundary_base h hz')
  convert hz using 1
  simp only [DyadicSquare.radius_eq, Dyadic.toReal_ofIntWithPrec]
  ring_nf

private theorem soft_boundary_two {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.softWitnessCheck p s k = true) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (2 * DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply localPoly_boundary_center (fun hz' => soft_local_boundary_two h hz')
  convert hz using 1
  simp only [DyadicSquare.radius_eq, Dyadic.toReal_ofIntWithPrec]
  ring_nf

private theorem soft_boundary_four {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : Nat}
    (h : Hex.softWitnessCheck p s k = true) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (4 * DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  apply localPoly_boundary_center (fun hz' => soft_local_boundary_four h hz')
  convert hz using 1
  simp only [DyadicSquare.radius_eq, Dyadic.toReal_ofIntWithPrec]
  ring_nf

/-- The three Boolean checks contained in an executable witness. -/
theorem checks {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.TaylorShift.witnessCheck s
      (Hex.TaylorShift.compute p s.center) k = true) :
    (Hex.pelletAt (Hex.taylor p s.center) k s.radiusLo s.radiusHi = true ∧
      Hex.pelletAt (Hex.taylor p s.center) k
        (s.radiusLo <<< (1 : Int)) (s.radiusHi <<< (1 : Int)) = true) ∧
      Hex.pelletAt (Hex.taylor p s.center) k
        (s.radiusLo <<< (2 : Int)) (s.radiusHi <<< (2 : Int)) = true := by
  unfold Hex.TaylorShift.witnessCheck Hex.TaylorShift.compute at h
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
  rcases witness_cases h with hsoft | hexact
  · exact soft_roots hsoft
  · have hs := pelletAt_rootsInDisc (checks hexact).1.1 (radiusLo_nonneg s)
      (DyadicSquare.radiusLo_lt_radius s).le
      (DyadicSquare.radius_lt_radiusHi s).le
    simpa only [DyadicSquare.center_eq, rootsInDisc_comp_X_add_C] using hs

/-- The second check certifies the same root count in the doubled disc. -/
theorem roots_two {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (2 * DyadicSquare.radius s) = k := by
  rcases witness_cases h with hsoft | hexact
  · exact soft_roots_two hsoft
  · have hs := pelletAt_rootsInDisc (checks hexact).1.2 (radiusLo_two_nonneg s)
      (radiusLo_two_le s) (radius_two_le_hi s)
    simpa only [DyadicSquare.center_eq, rootsInDisc_comp_X_add_C] using hs

/-- The third check certifies the same root count in the quadrupled disc. -/
theorem roots_four {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) :
    rootsInDisc (toPolyℂ p) (DyadicSquare.center s)
      (4 * DyadicSquare.radius s) = k := by
  rcases witness_cases h with hsoft | hexact
  · exact soft_roots_four hsoft
  · have hs := pelletAt_rootsInDisc (checks hexact).2 (radiusLo_four_nonneg s)
      (radiusLo_four_le s) (radius_four_le_hi s)
    simpa only [DyadicSquare.center_eq, rootsInDisc_comp_X_add_C] using hs

/-- The strict base-radius inequality excludes boundary roots. -/
theorem boundary {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  rcases witness_cases h with hsoft | hexact
  · exact soft_boundary hsoft hz
  · apply pelletAt_ne_zero_center (checks hexact).1.1 (radiusLo_nonneg s)
      (DyadicSquare.radiusLo_lt_radius s).le
      (DyadicSquare.radius_lt_radiusHi s).le
    simpa only [DyadicSquare.center_eq] using hz

/-- The doubled-radius inequality excludes boundary roots. -/
theorem boundary_two {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (2 * DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  rcases witness_cases h with hsoft | hexact
  · exact soft_boundary_two hsoft hz
  · apply pelletAt_ne_zero_center (checks hexact).1.2 (radiusLo_two_nonneg s)
      (radiusLo_two_le s) (radius_two_le_hi s)
    simpa only [DyadicSquare.center_eq] using hz

/-- The quadrupled-radius inequality excludes boundary roots. -/
theorem boundary_four {p : Hex.ZPoly} {s : Hex.DyadicSquare} {k : ℕ}
    (h : Hex.witness p s k) {z : ℂ}
    (hz : z ∈ sphere (DyadicSquare.center s) (4 * DyadicSquare.radius s)) :
    (toPolyℂ p).eval z ≠ 0 := by
  rcases witness_cases h with hsoft | hexact
  · exact soft_boundary_four hsoft hz
  · apply pelletAt_ne_zero_center (checks hexact).2 (radiusLo_four_nonneg s)
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
