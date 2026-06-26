module

public import HexPolyZ.Basic

public section

/-!
Executable Mignotte-bound helpers for `hex-poly-z`.

This module packages the integer computations that appear in the classical
Mignotte coefficient bound: binomial coefficients together with the Euclidean
norm upper bound of the ambient polynomial's coefficient vector. The
mathematical proof that these quantities bound factors lives in
`HexPolyZMathlib`.
-/
namespace Hex

namespace ZPoly

/-- Executable binomial coefficients for the Mignotte bound. -/
@[expose]
def binom (n k : Nat) : Nat :=
  if n < k then
    0
  else
    let kk := min k (n - k)
    (List.range kk).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- One Newton step for the natural-number square-root iteration. -/
@[expose]
def sqrtStep (n x : Nat) : Nat :=
  (x + n / x) / 2

/-- A fuel-bounded Newton iteration for the natural floor square root. -/
@[expose]
def sqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
      let next := sqrtStep n x
      if next ≥ x then
        x
      else
        sqrtAux n fuel next

/-- The floor of the square root of `n`. -/
@[expose]
def floorSqrt (n : Nat) : Nat :=
  if n = 0 then
    0
  else
    sqrtAux n (2 * n.log2 + 1) n

/-- The least natural number whose square is at least `n`. -/
@[expose]
def ceilSqrt (n : Nat) : Nat :=
  let r := floorSqrt n
  if r * r = n then
    r
  else
    r + 1

/-- The arithmetic-mean/geometric-mean inequality `4 * (a * b) ≤ (a + b) ^ 2`
for natural numbers. -/
private theorem four_mul_le_square_add (a b : Nat) :
    4 * (a * b) ≤ (a + b) ^ 2 := by
  by_cases h : a ≤ b
  · rcases Nat.exists_eq_add_of_le h with ⟨d, rfl⟩
    simp [Nat.pow_two]
    grind
  · have hba : b ≤ a := by omega
    rcases Nat.exists_eq_add_of_le hba with ⟨d, rfl⟩
    simp [Nat.pow_two]
    grind

/-- The midpoint square bound `x * (q + 1) ≤ ((x + q) / 2 + 1) ^ 2` that drives
the Newton upper envelope. -/
private theorem mul_succ_le_midpoint_succ_sq (x q : Nat) :
    x * (q + 1) ≤ ((x + q) / 2 + 1) ^ 2 := by
  let a := (x + q) / 2 + 1
  have hmid : x + q + 1 ≤ 2 * a := by
    dsimp [a]
    omega
  have hamgm : 4 * (x * (q + 1)) ≤ (x + q + 1) ^ 2 := by
    simpa [Nat.add_assoc] using four_mul_le_square_add x (q + 1)
  have hsquare : (x + q + 1) ^ 2 ≤ (2 * a) ^ 2 := by
    exact Nat.pow_le_pow_left hmid 2
  have h4 : 4 * (x * (q + 1)) ≤ 4 * (a ^ 2) := by
    calc
      4 * (x * (q + 1)) ≤ (x + q + 1) ^ 2 := hamgm
      _ ≤ (2 * a) ^ 2 := hsquare
      _ = 4 * (a ^ 2) := by
          simp [Nat.pow_two]
          grind
  have hcancel := Nat.le_of_mul_le_mul_left h4 (by decide : 0 < 4)
  simpa [a] using hcancel

/-- One Newton step preserves the upper envelope: `n ≤ (sqrtStep n x + 1) ^ 2`
whenever `n ≤ (x + 1) ^ 2`. -/
private theorem sqrtStep_upper_succ
    (n x : Nat) (hx : 0 < x) (_h : n ≤ (x + 1) ^ 2) :
    n ≤ (sqrtStep n x + 1) ^ 2 := by
  let q := n / x
  have hn_le : n ≤ x * (q + 1) := by
    calc
      n = x * q + n % x := by
        simpa [q] using (Nat.div_add_mod n x).symm
      _ ≤ x * q + x := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hx)) (x * q)
      _ = x * (q + 1) := by grind
  exact Nat.le_trans hn_le
    (by simpa [sqrtStep, q] using mul_succ_le_midpoint_succ_sq x q)

/-- Inductive core: the iterate `sqrtAux n fuel x` stays in the upper envelope
`n ≤ (sqrtAux n fuel x + 1) ^ 2` for any starting `x` already in it. -/
private theorem sqrtAux_upper_succ_core
    (n fuel x : Nat) (h : n ≤ (x + 1) ^ 2) :
    n ≤ (sqrtAux n fuel x + 1) ^ 2 := by
  induction fuel generalizing x with
  | zero =>
      simpa [sqrtAux] using h
  | succ fuel ih =>
      by_cases hx : 0 < x
      · unfold sqrtAux
        let next := sqrtStep n x
        by_cases hnext : next ≥ x
        · simp [next, hnext]
          exact h
        · simp [next, hnext]
          exact ih next (sqrtStep_upper_succ n x hx h)
      · have hxzero : x = 0 := by omega
        subst x
        simp [sqrtAux, sqrtStep]
        exact h

/-- The iterate `sqrtAux n fuel x` keeps the upper envelope
`n ≤ (sqrtAux n fuel x + 1) ^ 2`. -/
private theorem sqrtAux_upper_succ
    (n fuel x : Nat) (_hx : 0 < x) (h : n ≤ (x + 1) ^ 2) :
    n ≤ (sqrtAux n fuel x + 1) ^ 2 :=
  sqrtAux_upper_succ_core n fuel x h

/--
Stop-condition lemma for the Newton iteration: when `sqrtStep n x ≥ x`
and `x > 0`, the current `x` satisfies the lower-square bound
`x * x ≤ n`.

From `(x + n / x) / 2 ≥ x` we get `n / x ≥ x` via the Nat-division iff,
and then `x * x ≤ x * (n / x) ≤ n` closes via `Nat.div_mul_le_self`.
-/
private theorem sqrtStep_ge_imp_sq_le {n x : Nat} (_hx : 0 < x)
    (hstop : x ≤ sqrtStep n x) : x * x ≤ n := by
  have hdiv : x ≤ n / x := by
    have h1 : 2 * x ≤ x + n / x := by
      have := hstop
      unfold sqrtStep at this
      omega
    omega
  calc x * x
      ≤ x * (n / x) := Nat.mul_le_mul_left x hdiv
    _ = (n / x) * x := Nat.mul_comm _ _
    _ ≤ n := Nat.div_mul_le_self n x

/-- Once the iterate undershoots with `x * x ≤ n`, the Newton step no longer
decreases it: `x ≤ sqrtStep n x`. -/
private theorem sqrtStep_ge_of_sq_le
    {n x : Nat} (hsq : x * x ≤ n) :
    x ≤ sqrtStep n x := by
  by_cases hx : 0 < x
  · have hdiv : x ≤ n / x := by
      exact (Nat.le_div_iff_mul_le hx).mpr hsq
    unfold sqrtStep
    omega
  · have hx0 : x = 0 := by omega
    subst x
    simp [sqrtStep]

/-- The iteration is fixed at any `x` with `x * x ≤ n`: `sqrtAux n fuel x = x`. -/
private theorem sqrtAux_eq_self_of_sq_le
    (n fuel x : Nat) (hsq : x * x ≤ n) :
    sqrtAux n fuel x = x := by
  induction fuel with
  | zero =>
      simp [sqrtAux]
  | succ fuel ih =>
      unfold sqrtAux
      let next := sqrtStep n x
      have hstop : next ≥ x := sqrtStep_ge_of_sq_le hsq
      simp [next, hstop]

/-- The Newton iteration gap `x - n / x`, measuring how far the iterate sits
above its quotient. -/
private def sqrtGap (n x : Nat) : Nat :=
  x - n / x

/-- The gap `sqrtGap n x` is positive while `x` overshoots the root
(`¬ x * x ≤ n`). -/
private theorem sqrtGap_pos_of_not_sq
    {n x : Nat} (hx : 0 < x) (hnot_sq : ¬ x * x ≤ n) :
    0 < sqrtGap n x := by
  unfold sqrtGap
  have hdiv_lt : n / x < x := by
    by_cases hlt : n / x < x
    · exact hlt
    · have hx_le : x ≤ n / x := by omega
      exact False.elim (hnot_sq ((Nat.le_div_iff_mul_le hx).mp hx_le))
  omega

/-- One Newton step at least halves the gap:
`2 * sqrtGap n (sqrtStep n x) ≤ sqrtGap n x`. -/
private theorem sqrtStep_gap_halves
    (n x : Nat) (hx : 0 < x) (hnot_sq : ¬ x * x ≤ n) :
    2 * sqrtGap n (sqrtStep n x) ≤ sqrtGap n x := by
  let q := n / x
  let next := sqrtStep n x
  have hq_lt_x : q < x := by
    by_cases hlt : q < x
    · exact hlt
    · have hx_le : x ≤ q := by omega
      exact False.elim (hnot_sq (by
        unfold q at hx_le
        exact (Nat.le_div_iff_mul_le hx).mp hx_le))
  have hq_le_x : q ≤ x := Nat.le_of_lt hq_lt_x
  by_cases hqnext : q ≤ next
  · have hnext_le : 2 * next ≤ x + q := by
      unfold next sqrtStep
      exact Nat.mul_div_le (x + q) 2
    have hq_le_div_next : q ≤ n / next := by
      by_cases hnext_pos : 0 < next
      · have hnext_le_x : next ≤ x := by omega
        simpa [q] using Nat.div_le_div_left hnext_le_x hnext_pos
      · have hnext_zero : next = 0 := by omega
        simpa [hnext_zero] using hqnext
    calc
      2 * sqrtGap n next
          = 2 * (next - n / next) := rfl
      _ ≤ 2 * (next - q) := by
          exact Nat.mul_le_mul_left 2 (Nat.sub_le_sub_left hq_le_div_next next)
      _ ≤ x - q := by omega
      _ = sqrtGap n x := rfl
  · have hnext_lt_q : next < q := Nat.lt_of_not_ge hqnext
    have hnext_le_div : next ≤ n / next := by
      by_cases hnext_pos : 0 < next
      · have hnext_le_x : next ≤ x := by
          unfold next sqrtStep
          have hmul : 2 * ((x + q) / 2) ≤ x + q := Nat.mul_div_le (x + q) 2
          omega
        have hq_le_div_next : q ≤ n / next :=
          by simpa [q] using Nat.div_le_div_left hnext_le_x hnext_pos
        omega
      · have hnext_zero : next = 0 := by omega
        simp [hnext_zero]
    unfold sqrtGap
    have hzero : next - n / next = 0 := Nat.sub_eq_zero_of_le hnext_le_div
    rw [hzero]
    simp

/-- While the iterate has not yet undershot, `fuel` Newton steps shrink the gap
by a factor `2 ^ fuel`: `2 ^ fuel * sqrtGap n (sqrtAux n fuel x) ≤ sqrtGap n x`.
This geometric gap contraction drives phase-one convergence. -/
private theorem sqrtAux_gap_contract_of_not_done
    (n fuel x : Nat) (hx : 0 < x)
    (hnot_sq :
      ¬ (sqrtAux n fuel x) * (sqrtAux n fuel x) ≤ n) :
    2 ^ fuel * sqrtGap n (sqrtAux n fuel x) ≤ sqrtGap n x := by
  induction fuel generalizing x with
  | zero =>
      simp [sqrtAux]
  | succ fuel ih =>
      unfold sqrtAux
      let next := sqrtStep n x
      by_cases hstop : next ≥ x
      · have hsq : x * x ≤ n := sqrtStep_ge_imp_sq_le hx hstop
        have haux : sqrtAux n (fuel + 1) x = x := by
          simp [sqrtAux, next, hstop]
        exact False.elim (hnot_sq (by simpa [haux] using hsq))
      · have hnext_lt : next < x := Nat.lt_of_not_ge hstop
        have hnot_sq_current : ¬ x * x ≤ n := by
          intro hsq
          have hself : sqrtAux n (fuel + 1) x = x :=
            sqrtAux_eq_self_of_sq_le n (fuel + 1) x hsq
          exact hnot_sq (by simpa [hself] using hsq)
        have hnot_sq_tail :
            ¬ (sqrtAux n fuel next) * (sqrtAux n fuel next) ≤ n := by
          intro hsq
          have haux : sqrtAux n (fuel + 1) x = sqrtAux n fuel next := by
            simp [sqrtAux, next, hstop]
          exact hnot_sq (by simpa [haux] using hsq)
        have hnext_pos : 0 < next := by
          by_cases hnext_pos : 0 < next
          · exact hnext_pos
          · have hnext_zero : next = 0 := by omega
            exact False.elim (hnot_sq_tail (by simp [hnext_zero, sqrtAux_eq_self_of_sq_le]))
        have htail :
            2 ^ fuel * sqrtGap n (sqrtAux n fuel next) ≤ sqrtGap n next :=
          ih next hnext_pos hnot_sq_tail
        have hstep : 2 * sqrtGap n next ≤ sqrtGap n x :=
          sqrtStep_gap_halves n x hx hnot_sq_current
        calc
          2 ^ (fuel + 1) * sqrtGap n (sqrtAux n (fuel + 1) x)
              = 2 * (2 ^ fuel * sqrtGap n (sqrtAux n fuel next)) := by
                  simp [sqrtAux, next, hstop, Nat.pow_succ]
                  grind
          _ ≤ 2 * sqrtGap n next := Nat.mul_le_mul_left 2 htail
          _ ≤ sqrtGap n x := hstep

/-- After `n.log2 + 1` Newton steps from `x = n`, the iterate undershoots
(`(sqrtAux n (n.log2 + 1) n) ^ 2 ≤ n`), since the gap cannot survive that many
halvings while staying below `2 ^ (n.log2 + 1)`. -/
private theorem sqrtAux_phase_one_sq_le
    (n : Nat) (hn : 0 < n) :
    (sqrtAux n (n.log2 + 1) n) * (sqrtAux n (n.log2 + 1) n) ≤ n := by
  by_cases hsq :
      (sqrtAux n (n.log2 + 1) n) * (sqrtAux n (n.log2 + 1) n) ≤ n
  · exact hsq
  · have hcontract :
        2 ^ (n.log2 + 1) * sqrtGap n (sqrtAux n (n.log2 + 1) n) ≤ sqrtGap n n :=
      sqrtAux_gap_contract_of_not_done n (n.log2 + 1) n hn hsq
    have hgap_pos :
        0 < sqrtGap n (sqrtAux n (n.log2 + 1) n) := by
      have hpos : 0 < sqrtAux n (n.log2 + 1) n := by
        by_cases hpos : 0 < sqrtAux n (n.log2 + 1) n
        · exact hpos
        · have hzero : sqrtAux n (n.log2 + 1) n = 0 := by omega
          exact False.elim (hsq (by simp [hzero]))
      exact sqrtGap_pos_of_not_sq hpos hsq
    have hpow_le :
        2 ^ (n.log2 + 1) ≤ sqrtGap n n := by
      calc
        2 ^ (n.log2 + 1) ≤
            2 ^ (n.log2 + 1) * sqrtGap n (sqrtAux n (n.log2 + 1) n) := by
              exact Nat.le_mul_of_pos_right _ hgap_pos
        _ ≤ sqrtGap n n := hcontract
    have hgap_lt : sqrtGap n n < 2 ^ (n.log2 + 1) := by
      unfold sqrtGap
      have hdiv : n / n = 1 := Nat.div_self hn
      rw [hdiv]
      have hlt : n < 2 ^ (n.log2 + 1) := by
        simpa using (Nat.lt_log2_self : n < 2 ^ (n.log2 + 1))
      omega
    exact False.elim (Nat.not_lt_of_ge hpow_le hgap_lt)

/-- The iteration composes over fuel:
`sqrtAux n (fuel₁ + fuel₂) x = sqrtAux n fuel₂ (sqrtAux n fuel₁ x)`, letting a
full-fuel run split into a phase-one prefix and a refinement tail. -/
private theorem sqrtAux_append
    (n fuel₁ fuel₂ x : Nat) :
    sqrtAux n (fuel₁ + fuel₂) x =
      sqrtAux n fuel₂ (sqrtAux n fuel₁ x) := by
  induction fuel₁ generalizing x with
  | zero =>
      simp [sqrtAux]
  | succ fuel₁ ih =>
      have hfuel : fuel₁ + 1 + fuel₂ = (fuel₁ + fuel₂) + 1 := by omega
      let next := sqrtStep n x
      by_cases hstop : next ≥ x
      · have hsq : x * x ≤ n := by
          by_cases hx : 0 < x
          · exact sqrtStep_ge_imp_sq_le hx hstop
          · have hx0 : x = 0 := by omega
            subst x
            simp
        have hself : sqrtAux n fuel₂ x = x :=
          sqrtAux_eq_self_of_sq_le n fuel₂ x hsq
        have hfirst : sqrtAux n (fuel₁ + 1) x = x := by
          simp [sqrtAux, next, hstop]
        have hleft : sqrtAux n (fuel₁ + 1 + fuel₂) x = x := by
          rw [hfuel]
          simp [sqrtAux, next, hstop]
        rw [hleft, hfirst]
        exact hself.symm
      · have hfirst : sqrtAux n (fuel₁ + 1) x = sqrtAux n fuel₁ next := by
          simp [sqrtAux, next, hstop]
        have hleft :
            sqrtAux n (fuel₁ + 1 + fuel₂) x =
              sqrtAux n (fuel₁ + fuel₂) next := by
          rw [hfuel]
          simp [sqrtAux, next, hstop]
        rw [hleft, hfirst]
        exact ih next

/-- With full fuel `2 * n.log2 + 1` and `0 < n`, the iterate undershoots
(`(sqrtAux n (2 * n.log2 + 1) n) ^ 2 ≤ n`); the floor-square-root soundness fact
`floorSqrt_sq_le` rests on this. -/
private theorem sqrtAux_full_fuel_sq_le
    (n : Nat) (hn : 0 < n) :
    (sqrtAux n (2 * n.log2 + 1) n) *
      (sqrtAux n (2 * n.log2 + 1) n) ≤ n := by
  have hfuel : 2 * n.log2 + 1 = (n.log2 + 1) + n.log2 := by omega
  rw [hfuel, sqrtAux_append]
  have hsq : (sqrtAux n (n.log2 + 1) n) *
      (sqrtAux n (n.log2 + 1) n) ≤ n :=
    sqrtAux_phase_one_sq_le n hn
  have hself :
      sqrtAux n n.log2 (sqrtAux n (n.log2 + 1) n) =
        sqrtAux n (n.log2 + 1) n :=
    sqrtAux_eq_self_of_sq_le n n.log2 (sqrtAux n (n.log2 + 1) n) hsq
  simpa [hself] using hsq

/-- The squared Euclidean norm of the coefficient vector of `f`. -/
@[expose]
def coeffNormSq (f : ZPoly) : Nat :=
  (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0

/-- A conservative natural-number upper bound on the Euclidean norm of the
coefficient vector of `f`. -/
@[expose]
def coeffL2NormBound (f : ZPoly) : Nat :=
  ceilSqrt (coeffNormSq f)

/-- The executable Mignotte bound for the `j`-th coefficient of a degree-`k`
factor of `f`, using the conservative `coeffL2NormBound`. -/
@[expose]
def mignotteCoeffBound (f : ZPoly) (k j : Nat) : Nat :=
  binom k j * coeffL2NormBound f

/--
Uniform executable coefficient bound used by the default integer
factorization entry point.

It takes the maximum of the executable Mignotte coefficient bounds over every
candidate factor degree up to `f.degree?.getD 0` and every coefficient index up
to that degree.
-/
@[expose]
def defaultFactorCoeffBound (f : ZPoly) : Nat :=
  let degreeBound := f.degree?.getD 0
  (List.range (degreeBound + 1)).foldl
    (fun acc k =>
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        acc)
    0

/-- Base case of `binom`: choosing `0` elements always gives `1`, so the empty
`foldl` over `List.range 0` normalizes `binom n 0` to `1`. -/
@[simp, grind =] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  simp [binom]

/-- Base case of `binom`: choosing `k + 1` elements from `0` is impossible, so
the `n < k` guard fires and normalizes `binom 0 (k + 1)` to `0`. -/
@[simp, grind =] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := by
  simp [binom]

/-- The executable binomial coefficient `binom n k` vanishes when `n < k`. -/
theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) : binom n k = 0 := by
  simp [binom, h]

/-- Base case of `floorSqrt`: the `n = 0` guard fires before the Newton
iteration, so `floorSqrt 0` normalizes to `0`. -/
@[simp, grind =] theorem floorSqrt_zero : floorSqrt 0 = 0 := by
  simp [floorSqrt]

/-- The square of `floorSqrt n` is at most `n`: it is a lower square root. -/
theorem floorSqrt_sq_le (n : Nat) : floorSqrt n * floorSqrt n ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    unfold floorSqrt
    rw [if_neg hn]
    exact sqrtAux_full_fuel_sq_le n hn_pos

/-- Base case of `ceilSqrt`: since `floorSqrt 0 = 0` is a perfect square,
`ceilSqrt` returns its floor branch, normalizing `ceilSqrt 0` to `0`. -/
@[simp, grind =] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

/--
The square of `ceilSqrt n` is at least `n`.  This is the executable upper-square
bound used by the Mignotte coefficient norm chain: in the perfect-square branch
of `ceilSqrt`, equality holds; in the non-perfect-square branch, the bound
follows from the Newton iterator invariant `sqrtAux_upper_succ`.
-/
theorem le_ceilSqrt_sq (n : Nat) : n ≤ (ceilSqrt n) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hfloor : floorSqrt n = sqrtAux n (2 * n.log2 + 1) n := by
      unfold floorSqrt
      rw [if_neg hn]
    have hinit : n ≤ (n + 1) ^ 2 := by
      simp [Nat.pow_two]
      grind
    have hub : n ≤ (floorSqrt n + 1) ^ 2 := by
      rw [hfloor]
      exact sqrtAux_upper_succ n (2 * n.log2 + 1) n hn_pos hinit
    unfold ceilSqrt
    by_cases hsq : floorSqrt n * floorSqrt n = n
    · rw [if_pos hsq, Nat.pow_two]
      omega
    · rw [if_neg hsq]
      exact hub

/-- Restates `coeffNormSq f` as the explicit `foldl` summing `(f.coeff i).natAbs ^ 2`
over the stored coefficient indices `i < f.size`. -/
theorem coeffNormSq_eq_sum (f : ZPoly) :
    coeffNormSq f =
      (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0 := rfl

/-- `coeffL2NormBound f` equals the ceiling square root of the squared coefficient
norm `coeffNormSq f`. -/
theorem coeffL2NormBound_eq_ceilSqrt_coeffNormSq (f : ZPoly) :
    coeffL2NormBound f = ceilSqrt (coeffNormSq f) := rfl

/-- The executable Euclidean-norm bound has square at most twice the exact
squared coefficient norm. -/
theorem coeffL2NormBound_sq_le_two_mul_coeffNormSq (f : ZPoly) :
    (coeffL2NormBound f) ^ 2 ≤ 2 * coeffNormSq f := by
  unfold coeffL2NormBound ceilSqrt
  let r := floorSqrt (coeffNormSq f)
  have hr_sq : r * r ≤ coeffNormSq f := by
    dsimp [r]
    exact floorSqrt_sq_le (coeffNormSq f)
  by_cases hsq : r * r = coeffNormSq f
  · rw [if_pos hsq]
    rw [Nat.pow_two]
    have hsq_floor :
        floorSqrt (coeffNormSq f) * floorSqrt (coeffNormSq f) = coeffNormSq f := by
      simpa [r] using hsq
    omega
  · rw [if_neg hsq]
    rw [Nat.pow_two]
    have hr_lt : r * r < coeffNormSq f := Nat.lt_of_le_of_ne hr_sq hsq
    have hsucc_le : r * r + 1 ≤ coeffNormSq f := by omega
    have htwo_r : 2 * r ≤ r * r + 1 := by
      rcases r with _ | _ | r
      · simp
      · simp
      · have htwo_le : 2 ≤ r + 2 := by omega
        have hmul := Nat.mul_le_mul_right (r + 2) htwo_le
        exact Nat.le_trans hmul (Nat.le_succ _)
    have hmain : r * r + 2 * r + 1 ≤ 2 * coeffNormSq f := by omega
    have hsquare : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by grind
    simpa [r, hsquare] using hmain

/-- `mignotteCoeffBound f k j` equals the product `binom k j * coeffL2NormBound f`
of the binomial coefficient and the conservative coefficient-norm bound. -/
theorem mignotteCoeffBound_eq (f : ZPoly) (k j : Nat) :
    mignotteCoeffBound f k j = binom k j * coeffL2NormBound f := rfl

/-- Restates `defaultFactorCoeffBound f` as the nested `foldl` taking the maximum of
`mignotteCoeffBound f k j` over factor degrees `k` up to `f.degree?.getD 0` and
coefficient indices `j` up to `k`. -/
theorem defaultFactorCoeffBound_eq (f : ZPoly) :
    defaultFactorCoeffBound f =
      let degreeBound := f.degree?.getD 0
      (List.range (degreeBound + 1)).foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        0 := rfl

/-- The zero polynomial has no stored coefficients, so the empty `foldl`
defining `coeffNormSq` normalizes `coeffNormSq 0` to `0`. -/
@[simp, grind =] theorem coeffNormSq_zero : coeffNormSq (0 : ZPoly) = 0 := by
  rfl

/-- Base case of the coefficient-norm bound: `coeffNormSq 0 = 0` and
`ceilSqrt 0 = 0`, so `coeffL2NormBound 0` normalizes to `0`. -/
@[simp, grind =] theorem coeffL2NormBound_zero : coeffL2NormBound (0 : ZPoly) = 0 := by
  simp [coeffL2NormBound]

/-- Base case of the Mignotte coefficient bound: the conservative norm factor
`coeffL2NormBound 0 = 0` annihilates the product, so `mignotteCoeffBound 0 k j`
normalizes to `0` for every degree `k` and index `j`. -/
@[simp, grind =] theorem mignotteCoeffBound_zero (k j : Nat) :
    mignotteCoeffBound (0 : ZPoly) k j = 0 := by
  simp [mignotteCoeffBound]

/-- Base case of the default factor coefficient bound: every entry of the nested
maximum is `mignotteCoeffBound 0 k j = 0`, so `defaultFactorCoeffBound 0`
normalizes to `0`. -/
@[simp, grind =] theorem defaultFactorCoeffBound_zero :
    defaultFactorCoeffBound (0 : ZPoly) = 0 := by
  unfold defaultFactorCoeffBound
  have hignore :
      ∀ (xs : List Nat) (init : Nat),
        xs.foldl (fun acc _ => acc) init = init := by
    intro xs
    induction xs with
    | nil =>
        intro init
        rfl
    | cons _ xs ih =>
        intro init
        simp [ih]
  have hfold :
      ∀ (ks : List Nat) (init : Nat),
        ks.foldl
          (fun acc k =>
            (List.range (k + 1)).foldl
              (fun acc j => max acc (mignotteCoeffBound (0 : ZPoly) k j))
              acc)
          init = init := by
    intro ks
    induction ks with
    | nil =>
        intro init
        rfl
    | cons k ks ih =>
        intro init
        simp [mignotteCoeffBound_zero, hignore]
  exact hfold (List.range (((0 : ZPoly).degree?).getD 0 + 1)) 0

/-- The executable Mignotte coefficient bound `mignotteCoeffBound f k j` vanishes when
the coefficient index `j` exceeds the factor degree `k`. -/
theorem mignotteCoeffBound_eq_zero_of_lt (f : ZPoly) (k j : Nat) (h : k < j) :
    mignotteCoeffBound f k j = 0 := by
  simp [mignotteCoeffBound, binom_eq_zero_of_lt h]

/-- A maximizing natural-number `foldl` only increases (or preserves) its
accumulator, so the initial value bounds the fold result. -/
private theorem le_foldl_max_left {α : Type} (xs : List α) (g : α → Nat) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (g x)) init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left init (g x)) (ih (max init (g x)))

/-- For a maximizing natural-number `foldl`, the value `g x` at any member index
`x ∈ xs` is bounded by the fold result. -/
private theorem le_foldl_max_of_mem {α : Type} (xs : List α) (g : α → Nat)
    {x : α} {init : Nat} (hx : x ∈ xs) :
    g x ≤ xs.foldl (fun acc y => max acc (g y)) init := by
  induction xs generalizing init with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      cases hx with
      | inl h =>
          rw [h]
          exact Nat.le_trans (Nat.le_max_right init (g y))
            (le_foldl_max_left ys g (max init (g y)))
      | inr h =>
          exact ih h

/-- The inner `max`-fold over `j ∈ range (k+1)` dominates each
`mignotteCoeffBound f k j` at an in-range index, by `le_foldl_max_of_mem`. -/
private theorem mignotteCoeffBound_le_degree_innerFold
    (f : ZPoly) (k : Nat) {j init : Nat} (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        init := by
  exact le_foldl_max_of_mem (List.range (k + 1))
    (fun j => mignotteCoeffBound f k j)
    (List.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- The outer degree `max`-fold (each step running the inner `j`-fold) only
increases (or preserves) its accumulator, so the initial value bounds the
result. -/
private theorem defaultFactorCoeffBound_outerFold_preserves
    (f : ZPoly) (ks : List Nat) (init : Nat) :
    init ≤
      ks.foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        init := by
  induction ks generalizing init with
  | nil =>
      simp
  | cons k ks ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans
        (le_foldl_max_left (List.range (k + 1))
          (fun j => mignotteCoeffBound f k j) init)
        (ih ((List.range (k + 1)).foldl
          (fun acc j => max acc (mignotteCoeffBound f k j)) init))

/-- For any degree `k ∈ ks` and in-range index `j ≤ k`, `mignotteCoeffBound f k j`
is bounded by the full nested degree/index `max`-fold, combining the inner-fold
and outer-fold monotonicity lemmas. -/
private theorem mignotteCoeffBound_le_defaultFactorCoeffBound_fold
    (f : ZPoly) (ks : List Nat) {k j init : Nat} (hk : k ∈ ks) (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤
      ks.foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        init := by
  induction ks generalizing init with
  | nil =>
      cases hk
  | cons k' ks ih =>
      simp only [List.mem_cons] at hk
      simp only [List.foldl_cons]
      cases hk with
      | inl h =>
          subst h
          exact Nat.le_trans
            (mignotteCoeffBound_le_degree_innerFold f k (j := j) (init := init) hj)
            (defaultFactorCoeffBound_outerFold_preserves f ks
              ((List.range (k + 1)).foldl
                (fun acc j => max acc (mignotteCoeffBound f k j)) init))
      | inr h =>
          exact ih h

/--
Every executable Mignotte coefficient bound within the ambient degree range is
bounded by the default uniform factorization bound.
-/
theorem mignotteCoeffBound_le_defaultFactorCoeffBound
    (f : ZPoly) {k j : Nat} (hk : k ≤ f.degree?.getD 0) (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤ defaultFactorCoeffBound f := by
  unfold defaultFactorCoeffBound
  exact mignotteCoeffBound_le_defaultFactorCoeffBound_fold f
    (List.range (f.degree?.getD 0 + 1))
    (List.mem_range.mpr (Nat.lt_succ_of_le hk)) hj

/-- The conservative coefficient-norm bound `coeffL2NormBound f` is at most the default
uniform factor coefficient bound `defaultFactorCoeffBound f`. -/
theorem coeffL2NormBound_le_defaultFactorCoeffBound (f : ZPoly) :
    coeffL2NormBound f ≤ defaultFactorCoeffBound f := by
  simpa [mignotteCoeffBound] using
    (mignotteCoeffBound_le_defaultFactorCoeffBound f
      (k := 0) (j := 0) (Nat.zero_le _) (Nat.zero_le _))

/-- A maximizing natural-number `foldl` is bounded above by any value `B` that
dominates the seed and every `g x` at a member index. -/
private theorem foldl_max_le_of_forall {α : Type} (g : α → Nat) (B : Nat) :
    ∀ (xs : List α) (init : Nat), init ≤ B → (∀ x ∈ xs, g x ≤ B) →
      xs.foldl (fun acc x => max acc (g x)) init ≤ B := by
  intro xs
  induction xs with
  | nil => intro init hinit _; exact hinit
  | cons x xs ih =>
      intro init hinit hall
      simp only [List.foldl_cons]
      exact ih (max init (g x))
        (Nat.max_le.mpr ⟨hinit, hall x (List.mem_cons.mpr (Or.inl rfl))⟩)
        (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))

/-- Upper-bound companion of `mignotteCoeffBound_le_defaultFactorCoeffBound`: if
every executable Mignotte coefficient bound within the ambient degree range is at
most `B`, then so is the default uniform factor coefficient bound. -/
theorem defaultFactorCoeffBound_le (f : ZPoly) {B : Nat}
    (h : ∀ k, k ≤ f.degree?.getD 0 → ∀ j, j ≤ k → mignotteCoeffBound f k j ≤ B) :
    defaultFactorCoeffBound f ≤ B := by
  unfold defaultFactorCoeffBound
  have outer : ∀ (ks : List Nat) (init : Nat), init ≤ B →
      (∀ k ∈ ks, ∀ j, j ≤ k → mignotteCoeffBound f k j ≤ B) →
      ks.foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j)) acc)
        init ≤ B := by
    intro ks
    induction ks with
    | nil => intro init hinit _; exact hinit
    | cons k ks ih =>
        intro init hinit hall
        simp only [List.foldl_cons]
        refine ih _ ?_ (fun k' hk' j hj => hall k' (List.mem_cons.mpr (Or.inr hk')) j hj)
        exact foldl_max_le_of_forall (fun j => mignotteCoeffBound f k j) B
          (List.range (k + 1)) init hinit
          (fun j hj => hall k (List.mem_cons.mpr (Or.inl rfl)) j
            (Nat.lt_succ_iff.mp (List.mem_range.mp hj)))
  exact outer (List.range (f.degree?.getD 0 + 1)) 0 (Nat.zero_le _)
    (fun k hk j hj => h k (Nat.lt_succ_iff.mp (List.mem_range.mp hk)) j hj)

/-- An additive natural-number `foldl` only increases (or preserves) its
accumulator. -/
private theorem le_foldl_add_self {α : Type} (xs : List α) (g : α → Nat)
    (init : Nat) :
    init ≤ xs.foldl (fun acc y => acc + g y) init := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_add_right init (g y)) (ih (init + g y))

/-- For an additive natural-number `foldl`, each summand at a member index is
bounded by the result. -/
private theorem le_foldl_add_of_mem {α : Type} (xs : List α) (g : α → Nat)
    {x : α} {init : Nat} (hx : x ∈ xs) :
    g x ≤ xs.foldl (fun acc y => acc + g y) init := by
  induction xs generalizing init with
  | nil => cases hx
  | cons head tail ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      cases hx with
      | inl h =>
          subst h
          exact Nat.le_trans (Nat.le_add_left (g x) init)
            (le_foldl_add_self tail g (init + g x))
      | inr h => exact ih h

/-- The ceiling square root is positive on positive inputs. -/
private theorem ceilSqrt_pos_of_pos {n : Nat} (hn : 0 < n) :
    0 < ceilSqrt n := by
  have h : n ≤ (ceilSqrt n) ^ 2 := le_ceilSqrt_sq n
  by_cases hpos : 0 < ceilSqrt n
  · exact hpos
  · exfalso
    have hsq : ceilSqrt n = 0 := by omega
    rw [hsq, Nat.pow_two, Nat.zero_mul] at h
    omega

/-- A nonzero integer polynomial has positive squared Euclidean coefficient
norm: the last stored coefficient is nonzero and contributes a positive
summand to the fold. -/
theorem coeffNormSq_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < coeffNormSq f := by
  have hsize : 0 < f.size := size_pos_of_ne_zero f hf
  have hi_lt : f.size - 1 < f.size := by omega
  have hi_mem : f.size - 1 ∈ List.range f.size := List.mem_range.mpr hi_lt
  have hcoeff_ne : f.coeff (f.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size f hsize
  have hnatabs : 0 < (f.coeff (f.size - 1)).natAbs :=
    Nat.pos_of_ne_zero (fun h => hcoeff_ne (Int.natAbs_eq_zero.mp h))
  have hsq_pos : 0 < (f.coeff (f.size - 1)).natAbs ^ 2 := by
    rw [Nat.pow_two]; exact Nat.mul_pos hnatabs hnatabs
  unfold coeffNormSq
  exact Nat.lt_of_lt_of_le hsq_pos
    (le_foldl_add_of_mem (List.range f.size)
      (fun i => (f.coeff i).natAbs ^ 2) hi_mem)

/-- A nonzero integer polynomial has positive conservative Euclidean
coefficient-norm upper bound. -/
theorem coeffL2NormBound_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < coeffL2NormBound f := by
  unfold coeffL2NormBound
  exact ceilSqrt_pos_of_pos (coeffNormSq_pos_of_ne_zero hf)

/--
A nonzero integer polynomial has positive uniform default factor coefficient
bound.

This is the Mignotte-side fact downstream callers need to derive
`B ≠ 0` and the precision-modulus invariant `2 ≤ p ^ precisionForCoeffBound B p`
from `f ≠ 0` alone (combined with the standard `p ≥ 2` provenance from
the selected-prime primality lemma and `precisionForCoeffBound_spec`).
-/
theorem defaultFactorCoeffBound_pos_of_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    0 < defaultFactorCoeffBound f :=
  Nat.lt_of_lt_of_le (coeffL2NormBound_pos_of_ne_zero hf)
    (coeffL2NormBound_le_defaultFactorCoeffBound f)

end ZPoly
end Hex
