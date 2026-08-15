/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe

/-- Ceiling division for the positive denominators used by the logarithm
certificate. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The power-of-two reduction data for an integer logarithm. -/
structure LogData where
  exponent : Nat
  power : Nat
  offset : Nat
  sum : Nat
  numerator : Nat
  denominator : Nat
  upperTenth : Nat
  deriving DecidableEq, Repr

/-- Two atanh terms, an exact geometric remainder, and the checked bound
`log 2 < 7/10`, rounded once to a common tenths denominator. -/
def logData (p : Nat) : LogData :=
  let k := Nat.log 2 p
  let q := 2 ^ k
  let a := p - q
  let b := p + q
  let d := 3 * b ^ 3 * (b ^ 2 - a ^ 2)
  let n := 3 * a * b ^ 2 * (b ^ 2 - a ^ 2) + a ^ 3 * (b ^ 2 - a ^ 2) + 3 * a ^ 5
  { exponent := k
    power := q
    offset := a
    sum := b
    numerator := n
    denominator := d
    upperTenth := ceilDiv (7 * k * d + 20 * n) d }

private theorem logTwoUpper : Real.log 2 < (7 / 10 : Real) := by
  have bound := Real.log_div_le_sum_range_add
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at bound
  linarith

/-- Semantic theorem for a checked positive-integer logarithm record.  The
record contains only natural-number equalities and one final cross-product
comparison; the transcendental proof is shared by every input. -/
theorem log_le_tenth
    (p k q a b numerator denominator upper : Nat)
    (hp : 2 ≤ p)
    (hq : q = 2 ^ k)
    (hqle : q ≤ p)
    (hpq : p < 2 * q)
    (ha : a = p - q)
    (hb : b = p + q)
    (hn : numerator =
      3 * a * b ^ 2 * (b ^ 2 - a ^ 2) +
        a ^ 3 * (b ^ 2 - a ^ 2) + 3 * a ^ 5)
    (hd : denominator = 3 * b ^ 3 * (b ^ 2 - a ^ 2))
    (hupper : 7 * k * denominator + 20 * numerator ≤ upper * denominator) :
    Real.log p ≤ upper / 10 := by
  have hp0 : (0 : Real) < p := by exact_mod_cast (show 0 < p by omega)
  have hq0Nat : 0 < q := by simp [hq]
  have hq0 : (0 : Real) < q := by exact_mod_cast hq0Nat
  have hb0Nat : 0 < b := by omega
  have hb0 : (0 : Real) < b := by exact_mod_cast hb0Nat
  have haCast : (a : Real) = p - q := by
    rw [ha, Nat.cast_sub hqle]
  have hbCast : (b : Real) = p + q := by simp [hb]
  let x : Real := (a : Real) / b
  have hx0 : 0 ≤ x := by positivity
  have hab : a < b := by omega
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_one hb0).2 (by exact_mod_cast hab)
  have series := Real.log_div_le_sum_range_add hx0 hx1 2
  have ratio : (1 + x) / (1 - x) = (p : Real) / q := by
    dsimp [x]
    rw [haCast, hbCast]
    field_simp [ne_of_gt hq0]
    ring
  rw [ratio] at series
  have logRatio : Real.log ((p : Real) / q) ≤
      2 * ((a : Real) / b + ((a : Real) / b) ^ 3 / 3 +
        ((a : Real) / b) ^ 5 / (1 - ((a : Real) / b) ^ 2)) := by
    norm_num [Finset.sum_range_succ, x] at series
    linarith
  have hba : a < b := hab
  have squares : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hba (by omega)
  have diff0Nat : 0 < b ^ 2 - a ^ 2 := Nat.sub_pos_of_lt squares
  have diff0 : (0 : Real) < (b : Real) ^ 2 - (a : Real) ^ 2 := by
    exact sub_pos.mpr (by exact_mod_cast squares)
  have denominator0Nat : 0 < denominator := by
    rw [hd]
    positivity
  have denominator0 : (0 : Real) < denominator := by exact_mod_cast denominator0Nat
  have formula :
      2 * ((a : Real) / b + ((a : Real) / b) ^ 3 / 3 +
        ((a : Real) / b) ^ 5 / (1 - ((a : Real) / b) ^ 2)) =
      2 * numerator / denominator := by
    rw [hn, hd]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Nat.cast_sub (Nat.le_of_lt squares)]
    field_simp [ne_of_gt hb0, ne_of_gt diff0]
  rw [formula] at logRatio
  have logQ : Real.log q = k * Real.log 2 := by
    rw [hq]
    push_cast
    rw [Real.log_pow]
  have splitLog : Real.log p = Real.log q + Real.log ((p : Real) / q) := by
    rw [Real.log_div hp0.ne' hq0.ne', add_sub_cancel]
  have upperCast : (7 : Real) * k * denominator + 20 * numerator ≤
      upper * denominator := by exact_mod_cast hupper
  rw [splitLog, logQ]
  have log2Bound : (k : Real) * Real.log 2 ≤ k * (7 / 10 : Real) := by
    gcongr
    exact logTwoUpper.le
  calc
    (k : Real) * Real.log 2 + Real.log ((p : Real) / q)
        ≤ k * (7 / 10 : Real) + 2 * numerator / denominator :=
          add_le_add log2Bound logRatio
    _ ≤ upper / 10 := by
      field_simp [ne_of_gt denominator0]
      nlinarith

/-- The generated reduction record is a valid checked logarithm certificate
for every positive integer input. -/
theorem logData_log_le (p : Nat) (hp : 2 ≤ p) :
    Real.log p ≤ (logData p).upperTenth / 10 := by
  let k := Nat.log 2 p
  let q := 2 ^ k
  let a := p - q
  let b := p + q
  let d := 3 * b ^ 3 * (b ^ 2 - a ^ 2)
  let n := 3 * a * b ^ 2 * (b ^ 2 - a ^ 2) +
    a ^ 3 * (b ^ 2 - a ^ 2) + 3 * a ^ 5
  have qle : q ≤ p := Nat.pow_log_le_self 2 (by omega)
  have plt : p < 2 * q := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by omega) p
    simpa [q, pow_succ, mul_comm] using this
  have alt : a < b := by simp [a, b]; omega
  have dpos : 0 < d := by
    have hsq : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left alt (by omega)
    have hbpos : 0 < b := by dsimp [b]; omega
    dsimp [d]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hbpos 3))
      (Nat.sub_pos_of_lt hsq)
  have rounded : 7 * k * d + 20 * n ≤ ceilDiv (7 * k * d + 20 * n) d * d := by
    have h := (ceilDiv_le_iff_le_mul dpos).1
      (show (7 * k * d + 20 * n) ⌈/⌉ d ≤
        (7 * k * d + 20 * n) ⌈/⌉ d from le_rfl)
    simpa [ceilDiv, Nat.ceilDiv_eq_add_pred_div, mul_comm] using h
  have result := log_le_tenth p k q a b n d
    (ceilDiv (7 * k * d + 20 * n) d) hp rfl qle plt rfl rfl rfl rfl rounded
  simpa [logData, k, q, a, b, d, n] using result

/-- Trial division through the square root of every input in the pinned range.
The fixed upper divisor is part of the bounded `11723` certificate. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range 107).all fun i =>
    let m := i + 2
    decide (n < m * m) || decide (¬m ∣ n)

/-- The bounded trial-division classifier agrees with Mathlib primality on the
whole pinned source range. -/
theorem primeB_iff {n : Nat} (hn : n ≤ 11723) : primeB n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · intro h
    have parts := Bool.and_eq_true_iff.mp h
    refine ⟨of_decide_eq_true parts.1, ?_⟩
    intro m hm2 hmsqrt
    have sqrtBound : Nat.sqrt n ≤ 108 := by
      calc
        Nat.sqrt n ≤ Nat.sqrt 11723 := Nat.sqrt_le_sqrt hn
        _ = 108 := by
          symm
          rw [Nat.eq_sqrt]
          norm_num
    have hi : m - 2 < 107 := by omega
    have checked := (List.all_eq_true.mp parts.2) (m - 2)
      (List.mem_range.mpr hi)
    have restore : m - 2 + 2 = m := by omega
    simp only [restore, Bool.or_eq_true, decide_eq_true_eq] at checked
    exact checked.resolve_left (not_lt_of_ge (Nat.le_sqrt.mp hmsqrt))
  · rintro ⟨hn2, hprime⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true hn2, List.all_eq_true.mpr ?_⟩
    intro i hi
    have hi' : i < 107 := List.mem_range.mp hi
    let m := i + 2
    by_cases hmn : n < m * m
    · exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hmn))
    · apply Bool.or_eq_true_iff.mpr
      right
      apply decide_eq_true
      apply hprime m (by omega)
      exact Nat.le_sqrt.mpr (Nat.le_of_not_gt hmn)

/-- The base of each non-prime prime power through `11723`. -/
def powerBase : Nat → Nat
  | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 | 8192 => 2
  | 9 | 27 | 81 | 243 | 729 | 2187 | 6561 => 3
  | 25 | 125 | 625 | 3125 => 5
  | 49 | 343 | 2401 => 7
  | 121 | 1331 => 11
  | 169 | 2197 => 13
  | 289 | 4913 => 17
  | 361 | 6859 => 19
  | 529 => 23
  | 841 => 29
  | 961 => 31
  | 1369 => 37
  | 1681 => 41
  | 1849 => 43
  | 2209 => 47
  | 2809 => 53
  | 3481 => 59
  | 3721 => 61
  | 4489 => 67
  | 5041 => 71
  | 5329 => 73
  | 6241 => 79
  | 6889 => 83
  | 7921 => 89
  | 9409 => 97
  | 10201 => 101
  | 10609 => 103
  | 11449 => 107
  | _ => 0

private def smallPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107]

private theorem prime_mem_small {p : Nat} (hp : p.Prime) (ple : p ≤ 108) :
    p ∈ smallPrimes := by
  interval_cases p <;> (norm_num at hp <;> norm_num [smallPrimes])

set_option maxHeartbeats 3000000 in
/-- The bounded non-prime-power table contains every `p ^ k` in the source
range with prime base and exponent at least two. -/
theorem powerBase_pow {p k : Nat} (hp : p.Prime) (hk : 2 ≤ k)
    (hpk : p ^ k ≤ 11723) : powerBase (p ^ k) = p := by
  have psquare : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have ple : p ≤ 108 := by
    have : p ≤ Nat.sqrt 11723 := Nat.le_sqrt'.mpr (psquare.trans hpk)
    calc
      p ≤ Nat.sqrt 11723 := this
      _ = 108 := by
        symm
        rw [Nat.eq_sqrt]
        norm_num
  have twoPow : 2 ^ k ≤ 11723 :=
    (Nat.pow_le_pow_left hp.two_le k).trans hpk
  have kle : k ≤ 13 := by
    have hlog := Nat.le_log_of_pow_le (by omega : 1 < 2) twoPow
    have : Nat.log 2 11723 = 13 := by decide
    omega
  have pmem := prime_mem_small hp ple
  simp [smallPrimes] at pmem
  rcases pmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases k <;> (norm_num at hpk <;> norm_num [powerBase])

/-- Tenths-scaled upper bound contributed at a prime-power coordinate. -/
def contribution (n : Nat) : Nat :=
  if primeB n then (logData n).upperTenth
  else let p := powerBase n; if p = 0 then 0 else (logData p).upperTenth

/-- Every von Mangoldt summand in the pinned range is bounded by the
tenths-scaled package contribution. -/
theorem vonMangoldt_le_contribution {n : Nat} (hn : n ≤ 11723) :
    (ArithmeticFunction.vonMangoldt n : Real) ≤ contribution n / 10 := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  by_cases hpp : IsPrimePow n
  · rw [if_pos hpp]
    obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff n).mp hpp
    subst n
    rw [hp.pow_minFac hk.ne']
    by_cases checked : primeB (p ^ k)
    · have ple : p ≤ p ^ k := Nat.le_pow hk
      have logMono : Real.log p ≤ Real.log (p ^ k) :=
        Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast ple)
      have logDataBound := logData_log_le (p ^ k) hpp.two_le
      push_cast at logDataBound
      simpa [contribution, checked] using logMono.trans logDataBound
    · have hk2 : 2 ≤ k := by
        by_contra h
        have hk1 : k = 1 := by omega
        subst k
        have primeChecked : primeB p = true :=
          (primeB_iff (by simpa using hn)).2 hp
        simp only [pow_one] at checked
        exact checked primeChecked
      have base := powerBase_pow hp hk2 hn
      simpa [contribution, checked, base, hp.ne_zero] using
        logData_log_le p hp.two_le
  · rw [if_neg hpp]
    positivity

/-- Incremental all-coordinate checker state with a natural-number
accumulator. -/
def checkState : Nat → Nat × Bool
  | 0 => (0, true)
  | n + 1 =>
      let previous := checkState n
      let acc := previous.1 + contribution (n + 1)
      (acc, previous.2 && decide (100 * acc ≤ 111 * 10 * (n + 1)))

/-- Check every coordinate through `bound`. -/
def checkAll (bound : Nat) : Bool := (checkState bound).2

/-- Replay a bounded chunk starting after `start`. -/
def checkChunk : Nat → Nat → Nat → Nat × Bool
  | _, 0, acc => (acc, true)
  | start, count + 1, acc =>
      let previous := checkChunk start count acc
      let n := start + count + 1
      let acc' := previous.1 + contribution n
      (acc', previous.2 && decide (100 * acc' ≤ 111 * 10 * n))

/-- A checked chunk extends the exact prefix state; no runtime result is used as
kernel evidence until this structural replay theorem is applied. -/
theorem checkState_add (start count acc : Nat)
    (hstart : checkState start = (acc, true)) :
    checkState (start + count) = checkChunk start count acc := by
  induction count with
  | zero => simpa [checkChunk] using hstart
  | succ count ih =>
      have ih' : checkState (Nat.add start count) = checkChunk start count acc := ih
      simp only [Nat.add_succ, checkState, checkChunk]
      rw [ih']
      simp only [Nat.add_eq]

/-- A true prefix state contains every individual slope comparison in that
prefix. -/
theorem checkState_bound {bound : Nat} (hcheck : (checkState bound).2 = true)
    {n : Nat} (hn : n ≤ bound) :
    100 * (checkState n).1 ≤ 111 * 10 * n := by
  induction bound with
  | zero =>
      have : n = 0 := by omega
      subst n
      simp [checkState]
  | succ bound ih =>
      simp only [checkState, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      by_cases hlast : n = bound + 1
      · subst n
        exact hcheck.2
      · exact ih hcheck.1 (by omega)

/-- The prefix state's accumulator bounds the Mathlib Chebyshev sum. -/
theorem psi_le_state (bound : Nat) (hbound : bound ≤ 11723) :
    Chebyshev.psi (bound : Real) ≤ (checkState bound).1 / 10 := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  induction bound with
  | zero => simp [checkState]
  | succ bound ih =>
      rw [show Finset.Ioc 0 (bound + 1) =
          insert (bound + 1) (Finset.Ioc 0 bound) from by
        ext x
        simp [Finset.mem_Ioc]
        omega]
      rw [Finset.sum_insert (by simp [Finset.mem_Ioc])]
      have previous := ih (by omega)
      have current := vonMangoldt_le_contribution (n := bound + 1) (by omega)
      simp only [checkState]
      push_cast
      linarith

/-- Any fully checked state through `11723` yields the exact natural-number
form needed by the pinned PNT+ theorem. -/
theorem psi_nat_of_state
    (full : checkState 11723 = (118671, true))
    (n : Nat) (hn : n ≤ 11723) :
    Chebyshev.psi (n : Real) ≤ (111 / 100 : Real) * n := by
  have fullBool : (checkState 11723).2 = true := by rw [full]
  have arithmetic := checkState_bound fullBool hn
  have semantic := psi_le_state n hn
  have arithmeticReal : (100 : Real) * (checkState n).1 ≤ 1110 * n := by
    exact_mod_cast arithmetic
  norm_num at arithmetic ⊢
  nlinarith [arithmeticReal]

set_option maxRecDepth 100000 in
example : checkChunk 0 256 0 = (2574, true) := by decide
set_option maxRecDepth 100000 in
example : checkChunk 11520 203 116961 = (118671, true) := by decide

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe

end
