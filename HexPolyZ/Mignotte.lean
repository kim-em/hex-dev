import HexPolyZ.Basic

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
def binom (n k : Nat) : Nat :=
  if n < k then
    0
  else
    let kk := min k (n - k)
    (List.range kk).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- One Newton step for the natural-number square-root iteration. -/
private def sqrtStep (n x : Nat) : Nat :=
  (x + n / x) / 2

/-- A fuel-bounded Newton iteration for the natural floor square root. -/
private def sqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
      let next := sqrtStep n x
      if next ≥ x then
        x
      else
        sqrtAux n fuel next

/-- The floor of the square root of `n`. -/
def floorSqrt (n : Nat) : Nat :=
  if n = 0 then
    0
  else
    sqrtAux n (2 * n.log2 + 1) n

/-- The least natural number whose square is at least `n`. -/
def ceilSqrt (n : Nat) : Nat :=
  let r := floorSqrt n
  if r * r = n then
    r
  else
    r + 1

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

private theorem sqrtStep_far_contracts
    (n x : Nat) (hx : 0 < x) (hfar : 4 * n ≤ x * x) :
    8 * sqrtStep n x ≤ 5 * x := by
  have hq_mul : 4 * ((n / x) * x) ≤ x * x := by
    exact Nat.le_trans (Nat.mul_le_mul_left 4 (Nat.div_mul_le_self n x)) hfar
  have hq : 4 * (n / x) ≤ x := by
    have hcancel := Nat.le_of_mul_le_mul_right
      (by
        calc
          (4 * (n / x)) * x = 4 * ((n / x) * x) := by grind
          _ ≤ x * x := hq_mul)
      hx
    simpa using hcancel
  have hnext : 2 * sqrtStep n x ≤ x + n / x := by
    unfold sqrtStep
    exact Nat.mul_div_le (x + n / x) 2
  calc
    8 * sqrtStep n x = 4 * (2 * sqrtStep n x) := by grind
    _ ≤ 4 * (x + n / x) := Nat.mul_le_mul_left 4 hnext
    _ = 4 * x + 4 * (n / x) := by grind
    _ ≤ 4 * x + x := Nat.add_le_add_left hq (4 * x)
    _ = 5 * x := by grind

private theorem sqrtStep_far_lt_self
    (n x : Nat) (hx : 0 < x) (hfar : 4 * n ≤ x * x) :
    sqrtStep n x < x := by
  have hcontract := sqrtStep_far_contracts n x hx hfar
  have hlt : 5 * x < 8 * x := by omega
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hcontract hlt)

/--
Near-root envelope used by the two-phase Newton convergence proof: the current
state is no longer in the very-far region where `x^2` is at least `16 * n`.
-/
private def sqrtNearEnvelope (n x : Nat) : Prop :=
  x * x < 16 * n

private theorem sqrtNearEnvelope_of_not_very_far
    {n x : Nat} (h : ¬ 16 * n ≤ x * x) :
    sqrtNearEnvelope n x := by
  unfold sqrtNearEnvelope
  omega

private theorem sqrtAux_near_or_sq_le
    (n fuel x : Nat) (hnear : sqrtNearEnvelope n x) :
    let y := sqrtAux n fuel x
    y * y ≤ n ∨ sqrtNearEnvelope n y := by
  induction fuel generalizing x with
  | zero =>
      simp [sqrtAux, hnear]
  | succ fuel ih =>
      unfold sqrtAux
      let next := sqrtStep n x
      by_cases hstop : next ≥ x
      · simp [next, hstop]
        by_cases hx : 0 < x
        · exact Or.inl (sqrtStep_ge_imp_sq_le hx hstop)
        · have hx0 : x = 0 := by omega
          subst x
          exact Or.inl (by simp)
      · simp [next, hstop]
        have hnext_le : next ≤ x := Nat.le_of_lt (Nat.lt_of_not_ge hstop)
        have hsq_next : next * next ≤ x * x :=
          Nat.mul_le_mul hnext_le hnext_le
        have hnear_next : sqrtNearEnvelope n next := by
          unfold sqrtNearEnvelope at hnear ⊢
          exact Nat.lt_of_le_of_lt hsq_next hnear
        exact ih next hnear_next

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

private theorem sqrtAux_preserves_sq_or_near
    (n fuel x : Nat) (h : x * x ≤ n ∨ sqrtNearEnvelope n x) :
    let y := sqrtAux n fuel x
    y * y ≤ n ∨ sqrtNearEnvelope n y := by
  cases h with
  | inl hsq =>
      simp [sqrtAux_eq_self_of_sq_le n fuel x hsq, hsq]
  | inr hnear =>
      exact sqrtAux_near_or_sq_le n fuel x hnear

private theorem sqrtStep_very_far_contracts
    (n x : Nat) (hx : 0 < x) (hfar : 16 * n ≤ x * x) :
    32 * sqrtStep n x ≤ 17 * x := by
  have hq_mul : 16 * ((n / x) * x) ≤ x * x := by
    exact Nat.le_trans (Nat.mul_le_mul_left 16 (Nat.div_mul_le_self n x)) hfar
  have hq : 16 * (n / x) ≤ x := by
    have hcancel := Nat.le_of_mul_le_mul_right
      (by
        calc
          (16 * (n / x)) * x = 16 * ((n / x) * x) := by grind
          _ ≤ x * x := hq_mul)
      hx
    simpa using hcancel
  have hnext : 2 * sqrtStep n x ≤ x + n / x := by
    unfold sqrtStep
    exact Nat.mul_div_le (x + n / x) 2
  calc
    32 * sqrtStep n x = 16 * (2 * sqrtStep n x) := by grind
    _ ≤ 16 * (x + n / x) := Nat.mul_le_mul_left 16 hnext
    _ = 16 * x + 16 * (n / x) := by grind
    _ ≤ 16 * x + x := Nat.add_le_add_left hq (16 * x)
    _ = 17 * x := by grind

private theorem sqrtStep_very_far_lt_self
    (n x : Nat) (hx : 0 < x) (hfar : 16 * n ≤ x * x) :
    sqrtStep n x < x := by
  have hcontract := sqrtStep_very_far_contracts n x hx hfar
  have hlt : 17 * x < 32 * x := by omega
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hcontract hlt)

private theorem sqrtStep_very_far_two_step_halves
    (n x : Nat) (hx : 0 < x)
    (hy : 0 < sqrtStep n x)
    (hfar₁ : 16 * n ≤ x * x)
    (hfar₂ : 16 * n ≤ sqrtStep n x * sqrtStep n x) :
    2 * sqrtStep n (sqrtStep n x) < x := by
  let y := sqrtStep n x
  let z := sqrtStep n y
  have hxy : 32 * y ≤ 17 * x := by
    simpa [y] using sqrtStep_very_far_contracts n x hx hfar₁
  have hyz : 32 * z ≤ 17 * y := by
    simpa [y, z] using sqrtStep_very_far_contracts n y hy hfar₂
  have h1024 : 1024 * z ≤ 289 * x := by
    calc
      1024 * z = 32 * (32 * z) := by grind
      _ ≤ 32 * (17 * y) := Nat.mul_le_mul_left 32 hyz
      _ = 17 * (32 * y) := by grind
      _ ≤ 17 * (17 * x) := Nat.mul_le_mul_left 17 hxy
      _ = 289 * x := by grind
  have hlt : 1024 * z < 512 * x := by
    have h289 : 289 * x < 512 * x := by omega
    exact Nat.lt_of_le_of_lt h1024 h289
  have hcancel : 512 * (2 * z) < 512 * x := by
    calc
      512 * (2 * z) = 1024 * z := by grind
      _ < 512 * x := hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

private theorem log2_lt_of_two_mul_lt
    {z x : Nat} (hz : 0 < z) (h : 2 * z < x) :
    z.log2 < x.log2 := by
  have hz_ne : z ≠ 0 := Nat.ne_of_gt hz
  have hx_pos : 0 < x := by omega
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hx_pos
  have hpow_le_z : 2 ^ z.log2 ≤ z := by
    exact (Nat.le_log2 hz_ne).mp (Nat.le_refl z.log2)
  have hpow_succ_le_x : 2 ^ (z.log2 + 1) ≤ x := by
    have hpow : 2 ^ (z.log2 + 1) ≤ 2 * z := by
      calc
        2 ^ (z.log2 + 1) = 2 * 2 ^ z.log2 := by
          rw [Nat.pow_succ]
          grind
        _ ≤ 2 * z := Nat.mul_le_mul_left 2 hpow_le_z
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hpow h)
  have hle : z.log2 + 1 ≤ x.log2 := by
    exact (Nat.le_log2 hx_ne).mpr hpow_succ_le_x
  omega

private theorem sqrtStep_very_far_two_step_log2_lt
    (n x : Nat) (hx : 0 < x)
    (hy : 0 < sqrtStep n x)
    (hz : 0 < sqrtStep n (sqrtStep n x))
    (hfar₁ : 16 * n ≤ x * x)
    (hfar₂ : 16 * n ≤ sqrtStep n x * sqrtStep n x) :
    (sqrtStep n (sqrtStep n x)).log2 < x.log2 := by
  exact log2_lt_of_two_mul_lt hz
    (sqrtStep_very_far_two_step_halves n x hx hy hfar₁ hfar₂)

private theorem sqrtAux_phase_one_core
    (n x : Nat) (hx : 0 < x) :
    let y := sqrtAux n (2 * x.log2 + 1) x
    y * y ≤ n ∨ sqrtNearEnvelope n y := by
  induction x using Nat.strongRecOn generalizing n with
  | ind x ih =>
      by_cases hfar₁ : 16 * n ≤ x * x
      · unfold sqrtAux
        let y := sqrtStep n x
        by_cases hstop₁ : y ≥ x
        · simp [y, hstop₁]
          exact Or.inl (sqrtStep_ge_imp_sq_le hx hstop₁)
        · simp [y, hstop₁]
          by_cases hy : 0 < y
          · by_cases hnear_y : sqrtNearEnvelope n y
            · exact sqrtAux_near_or_sq_le n (2 * x.log2) y hnear_y
            · have hfar₂ : 16 * n ≤ y * y := by
                unfold sqrtNearEnvelope at hnear_y
                omega
              have hx_log_pos : 0 < x.log2 := by
                have hy_lt_x : y < x := Nat.lt_of_not_ge hstop₁
                have hx_two : 2 ≤ x := by omega
                have hx_ne : x ≠ 0 := Nat.ne_of_gt hx
                have hle_log : 1 ≤ x.log2 := by
                  exact (Nat.le_log2 hx_ne).mpr (by simpa using hx_two)
                omega
              have hfuel_step : 2 * x.log2 = (2 * x.log2 - 1) + 1 := by
                omega
              rw [hfuel_step]
              unfold sqrtAux
              let z := sqrtStep n y
              by_cases hstop₂ : z ≥ y
              · have hstop₂' :
                    sqrtStep n x ≤ sqrtStep n (sqrtStep n x) := by
                    simpa [y, z] using hstop₂
                simp [hstop₂']
                exact Or.inl (sqrtStep_ge_imp_sq_le hy hstop₂)
              · have hstop₂' :
                    ¬ sqrtStep n x ≤ sqrtStep n (sqrtStep n x) := by
                    simpa [y, z] using hstop₂
                simp [hstop₂']
                by_cases hz : 0 < z
                · have hz_lt_x : z < x := by
                    have hhalf : 2 * z < x := by
                      simpa [y, z] using
                        sqrtStep_very_far_two_step_halves n x hx hy hfar₁ hfar₂
                    omega
                  have hz_log_lt : z.log2 < x.log2 := by
                    simpa [y, z] using
                      sqrtStep_very_far_two_step_log2_lt n x hx hy hz hfar₁ hfar₂
                  have hrec :
                      let w := sqrtAux n (2 * z.log2 + 1) z
                      w * w ≤ n ∨ sqrtNearEnvelope n w :=
                    ih z hz_lt_x n hz
                  have hle : 2 * z.log2 + 1 ≤ 2 * x.log2 - 1 := by
                    omega
                  let extra := (2 * x.log2 - 1) - (2 * z.log2 + 1)
                  have hfuel :
                      2 * x.log2 - 1 = (2 * z.log2 + 1) + extra := by
                    dsimp [extra]
                    omega
                  rw [hfuel, sqrtAux_append]
                  exact sqrtAux_preserves_sq_or_near n extra
                    (sqrtAux n (2 * z.log2 + 1) z) hrec
                · have hz0 : z = 0 := by omega
                  simpa [y, z, hz0, hstop₂'] using
                    sqrtAux_preserves_sq_or_near n (2 * x.log2 - 1) 0
                      (Or.inl (by simp))
          · have hy0 : y = 0 := by omega
            simpa [y, hy0] using
              sqrtAux_preserves_sq_or_near n (2 * x.log2) 0
                (Or.inl (by simp))
      · exact sqrtAux_near_or_sq_le n (2 * x.log2 + 1) x
          (sqrtNearEnvelope_of_not_very_far hfar₁)

private theorem sqrtAux_phase_one_near_or_sq_le
    (n : Nat) :
    let y := sqrtAux n (2 * n.log2 + 1) n
    y * y ≤ n ∨ sqrtNearEnvelope n y := by
  by_cases hn : n = 0
  · subst n
    simp [sqrtAux]
  · exact sqrtAux_phase_one_core n n (Nat.pos_of_ne_zero hn)

/-- The squared Euclidean norm of the coefficient vector of `f`. -/
def coeffNormSq (f : ZPoly) : Nat :=
  (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0

/-- A conservative natural-number upper bound on the Euclidean norm of the
coefficient vector of `f`. -/
def coeffL2NormBound (f : ZPoly) : Nat :=
  ceilSqrt (coeffNormSq f)

/-- The executable Mignotte bound for the `j`-th coefficient of a degree-`k`
factor of `f`, using the conservative `coeffL2NormBound`. -/
def mignotteCoeffBound (f : ZPoly) (k j : Nat) : Nat :=
  binom k j * coeffL2NormBound f

/--
Uniform executable coefficient bound used by the default integer
factorization entry point.

It takes the maximum of the executable Mignotte coefficient bounds over every
candidate factor degree up to `f.degree?.getD 0` and every coefficient index up
to that degree.
-/
def defaultFactorCoeffBound (f : ZPoly) : Nat :=
  let degreeBound := f.degree?.getD 0
  (List.range (degreeBound + 1)).foldl
    (fun acc k =>
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        acc)
    0

@[simp] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  simp [binom]

@[simp] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := by
  simp [binom]

theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) : binom n k = 0 := by
  simp [binom, h]

@[simp] theorem floorSqrt_zero : floorSqrt 0 = 0 := by
  simp [floorSqrt]

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
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

theorem coeffNormSq_eq_sum (f : ZPoly) :
    coeffNormSq f =
      (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0 := rfl

theorem coeffL2NormBound_eq_ceilSqrt_coeffNormSq (f : ZPoly) :
    coeffL2NormBound f = ceilSqrt (coeffNormSq f) := rfl

theorem mignotteCoeffBound_eq (f : ZPoly) (k j : Nat) :
    mignotteCoeffBound f k j = binom k j * coeffL2NormBound f := rfl

theorem defaultFactorCoeffBound_eq (f : ZPoly) :
    defaultFactorCoeffBound f =
      let degreeBound := f.degree?.getD 0
      (List.range (degreeBound + 1)).foldl
        (fun acc k =>
          (List.range (k + 1)).foldl
            (fun acc j => max acc (mignotteCoeffBound f k j))
            acc)
        0 := rfl

@[simp] theorem coeffNormSq_zero : coeffNormSq (0 : ZPoly) = 0 := by
  rfl

@[simp] theorem coeffL2NormBound_zero : coeffL2NormBound (0 : ZPoly) = 0 := by
  simp [coeffL2NormBound]

@[simp] theorem mignotteCoeffBound_zero (k j : Nat) :
    mignotteCoeffBound (0 : ZPoly) k j = 0 := by
  simp [mignotteCoeffBound]

@[simp] theorem defaultFactorCoeffBound_zero :
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

theorem mignotteCoeffBound_eq_zero_of_lt (f : ZPoly) (k j : Nat) (h : k < j) :
    mignotteCoeffBound f k j = 0 := by
  simp [mignotteCoeffBound, binom_eq_zero_of_lt h]

private theorem le_foldl_max_left {α : Type} (xs : List α) (g : α → Nat) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (g x)) init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left init (g x)) (ih (max init (g x)))

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

private theorem mignotteCoeffBound_le_degree_innerFold
    (f : ZPoly) (k : Nat) {j init : Nat} (hj : j ≤ k) :
    mignotteCoeffBound f k j ≤
      (List.range (k + 1)).foldl
        (fun acc j => max acc (mignotteCoeffBound f k j))
        init := by
  exact le_foldl_max_of_mem (List.range (k + 1))
    (fun j => mignotteCoeffBound f k j)
    (List.mem_range.mpr (Nat.lt_succ_of_le hj))

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

theorem coeffL2NormBound_le_defaultFactorCoeffBound (f : ZPoly) :
    coeffL2NormBound f ≤ defaultFactorCoeffBound f := by
  simpa [mignotteCoeffBound] using
    (mignotteCoeffBound_le_defaultFactorCoeffBound f
      (k := 0) (j := 0) (Nat.zero_le _) (Nat.zero_le _))

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
