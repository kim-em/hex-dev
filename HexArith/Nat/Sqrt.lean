/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.Prime

public section

/-! Natural floor and ceiling square roots computed by Newton iteration. -/

namespace HexArith.Nat

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

/-- The arithmetic-mean/geometric-mean inequality `4 * (a * b) ≤ (a + b) ^ 2`
for natural numbers. -/
private theorem amgm (a b : Nat) :
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
private theorem midpoint_bound (x q : Nat) :
    x * (q + 1) ≤ ((x + q) / 2 + 1) ^ 2 := by
  let a := (x + q) / 2 + 1
  have hmid : x + q + 1 ≤ 2 * a := by
    dsimp [a]
    omega
  have hamgm : 4 * (x * (q + 1)) ≤ (x + q + 1) ^ 2 := by
    simpa [Nat.add_assoc] using amgm x (q + 1)
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
    (by simpa [sqrtStep, q] using midpoint_bound x q)

/-- Induction step: the iterate `sqrtAux n fuel x` stays in the upper envelope
`n ≤ (sqrtAux n fuel x + 1) ^ 2` for any starting `x` already in it. -/
private theorem sqrtAux_upper
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
  sqrtAux_upper n fuel x h

/--
Stop-condition lemma for the Newton iteration: when `sqrtStep n x ≥ x`
and `x > 0`, the current `x` satisfies the lower-square bound
`x * x ≤ n`.

From `(x + n / x) / 2 ≥ x` we get `n / x ≥ x` via the Nat-division iff,
and then `x * x ≤ x * (n / x) ≤ n` closes via `Nat.div_mul_le_self`.
-/
private theorem sqrtStep_sq_le {n x : Nat} (_hx : 0 < x)
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
private theorem sqrtStep_fixed
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
private theorem sqrtAux_fixed
    (n fuel x : Nat) (hsq : x * x ≤ n) :
    sqrtAux n fuel x = x := by
  induction fuel with
  | zero =>
      simp [sqrtAux]
  | succ fuel ih =>
      unfold sqrtAux
      let next := sqrtStep n x
      have hstop : next ≥ x := sqrtStep_fixed hsq
      simp [next, hstop]

/-- The Newton iteration gap `x - n / x`, measuring how far the iterate sits
above its quotient. -/
private def sqrtGap (n x : Nat) : Nat :=
  x - n / x

/-- The gap `sqrtGap n x` is positive while `x` overshoots the root
(`¬ x * x ≤ n`). -/
private theorem sqrtGap_pos
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
This geometric gap contraction drives the initial convergence bound. -/
private theorem sqrtAux_gap
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
      · have hsq : x * x ≤ n := sqrtStep_sq_le hx hstop
        have haux : sqrtAux n (fuel + 1) x = x := by
          simp [sqrtAux, next, hstop]
        exact False.elim (hnot_sq (by simpa [haux] using hsq))
      · have hnext_lt : next < x := Nat.lt_of_not_ge hstop
        have hnot_sq_current : ¬ x * x ≤ n := by
          intro hsq
          have hself : sqrtAux n (fuel + 1) x = x :=
            sqrtAux_fixed n (fuel + 1) x hsq
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
            exact False.elim (hnot_sq_tail (by simp [hnext_zero, sqrtAux_fixed]))
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
private theorem sqrtAux_log
    (n : Nat) (hn : 0 < n) :
    (sqrtAux n (n.log2 + 1) n) * (sqrtAux n (n.log2 + 1) n) ≤ n := by
  by_cases hsq :
      (sqrtAux n (n.log2 + 1) n) * (sqrtAux n (n.log2 + 1) n) ≤ n
  · exact hsq
  · have hgap_le :
        2 ^ (n.log2 + 1) * sqrtGap n (sqrtAux n (n.log2 + 1) n) ≤ sqrtGap n n :=
      sqrtAux_gap n (n.log2 + 1) n hn hsq
    have hgap_pos :
        0 < sqrtGap n (sqrtAux n (n.log2 + 1) n) := by
      have hpos : 0 < sqrtAux n (n.log2 + 1) n := by
        by_cases hpos : 0 < sqrtAux n (n.log2 + 1) n
        · exact hpos
        · have hzero : sqrtAux n (n.log2 + 1) n = 0 := by omega
          exact False.elim (hsq (by simp [hzero]))
      exact sqrtGap_pos hpos hsq
    have hpow_le :
        2 ^ (n.log2 + 1) ≤ sqrtGap n n := by
      calc
        2 ^ (n.log2 + 1) ≤
            2 ^ (n.log2 + 1) * sqrtGap n (sqrtAux n (n.log2 + 1) n) := by
              exact Nat.le_mul_of_pos_right _ hgap_pos
        _ ≤ sqrtGap n n := hgap_le
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
full-fuel run split into an initial prefix and a refinement tail. -/
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
          · exact sqrtStep_sq_le hx hstop
          · have hx0 : x = 0 := by omega
            subst x
            simp
        have hself : sqrtAux n fuel₂ x = x :=
          sqrtAux_fixed n fuel₂ x hsq
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
private theorem sqrtAux_sq_le
    (n : Nat) (hn : 0 < n) :
    (sqrtAux n (2 * n.log2 + 1) n) *
      (sqrtAux n (2 * n.log2 + 1) n) ≤ n := by
  have hfuel : 2 * n.log2 + 1 = (n.log2 + 1) + n.log2 := by omega
  rw [hfuel, sqrtAux_append]
  have hsq : (sqrtAux n (n.log2 + 1) n) *
      (sqrtAux n (n.log2 + 1) n) ≤ n :=
    sqrtAux_log n hn
  have hself :
      sqrtAux n n.log2 (sqrtAux n (n.log2 + 1) n) =
        sqrtAux n (n.log2 + 1) n :=
    sqrtAux_fixed n n.log2 (sqrtAux n (n.log2 + 1) n) hsq
  simpa [hself] using hsq

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
    rw [ite_eq_right hn]
    exact sqrtAux_sq_le n hn_pos

/-- Base case of `ceilSqrt`: since `floorSqrt 0 = 0` is a perfect square,
`ceilSqrt` returns its floor branch, normalizing `ceilSqrt 0` to `0`. -/
@[simp, grind =] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

/--
The square of {name}`HexArith.Nat.ceilSqrt` applied to `n` is at least `n`. This is the executable upper-square
bound used by the Mignotte coefficient norm chain: in the perfect-square branch
of the ceiling square root, equality holds; in the non-perfect-square branch,
the bound follows from the Newton iterator invariant.
-/
theorem le_ceilSqrt_sq (n : Nat) : n ≤ (ceilSqrt n) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hfloor : floorSqrt n = sqrtAux n (2 * n.log2 + 1) n := by
      unfold floorSqrt
      rw [ite_eq_right hn]
    have hinit : n ≤ (n + 1) ^ 2 := by
      simp [Nat.pow_two]
      grind
    have hub : n ≤ (floorSqrt n + 1) ^ 2 := by
      rw [hfloor]
      exact sqrtAux_upper_succ n (2 * n.log2 + 1) n hn_pos hinit
    unfold ceilSqrt
    by_cases hsq : floorSqrt n * floorSqrt n = n
    · rw [ite_eq_left hsq, Nat.pow_two]
      omega
    · rw [ite_eq_right hsq]
      exact hub

/-- A natural square upper bound also bounds the ceiling square root. -/
theorem ceilSqrt_le {n b : Nat} (h : n ≤ b ^ 2) : ceilSqrt n ≤ b := by
  have hf := floorSqrt_sq_le n
  have hb : floorSqrt n ≤ b := Nat.mul_self_le_mul_self_iff.mp
    (Nat.le_trans hf (by simpa only [Nat.pow_two] using h))
  unfold ceilSqrt
  dsimp only
  split
  · exact hb
  · rename_i hs
    have hne : floorSqrt n ≠ b := by
      intro heq
      apply hs
      rw [heq] at hf ⊢
      exact Nat.le_antisymm hf (by simpa only [Nat.pow_two] using h)
    omega

end HexArith.Nat
