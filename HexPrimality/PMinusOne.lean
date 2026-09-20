/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Table
public import HexPrimality.Sieve
public import HexPrimality.Order
public import HexArith.Montgomery.Context
public import HexBasic.Rand

public section

/-! Pollard `p - 1` search, shared with integer factorization. Stage 2 retains
stage 1's residue, uses a complete prime interval and a baby/giant schedule,
and recovers whole-product batches from their retained terms. Search remains
untrusted: every factor exit checks range and divisibility. -/

namespace Hex

namespace Nat

/-- The three semantically distinct stage-1 gcd outcomes. -/
inductive PMinusOneResult where
  | noFactor
  | factor (value : Nat)
  | whole
deriving Repr, DecidableEq, Inhabited

/-- The result of one counted deterministic stage-1 call. A call is one
attempt on every terminal gcd outcome. Pollard `p - 1` draws no randomness,
so the returned generator is exactly the supplied state; carrying it here
lets randomized callers resume through the same boundary as rho. -/
structure PMinusOneAttempt where
  /-- The terminal gcd outcome. -/
  result : PMinusOneResult
  /-- Semantic stage-1 calls executed; always one at this boundary. -/
  attempts : Nat
  /-- The unchanged generator state. -/
  rand : Rand
deriving Repr, DecidableEq

/-- Maximum supported stage-one bound. Stage primes come from the verified
runtime sieve, independently of the committed table. Ordinary search policies
may select smaller bounds. -/
def smoothBoundCap : Nat := 524288

/-- Clamp a requested stage-1 bound to the supported runtime range. -/
def smoothBound (bound : Nat) : Nat := min bound smoothBoundCap

@[simp]
theorem smoothBound_idem (bound : Nat) :
    smoothBound (smoothBound bound) = smoothBound bound := by
  simp [smoothBound, Nat.min_assoc]

private def largestPower (q bound : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc ≤ bound / q then largestPower q bound fuel (acc * q) else acc

private def stageExponent (q bound : Nat) : Nat :=
  largestPower q bound (bound.log2 + 1) q

private def raiseSmooth (n bound : Nat) : List Nat → Nat → Nat
  | [], x => x
  | q :: qs, x =>
      if q ≤ bound then
        raiseSmooth n bound qs
          (HexArith.powModNat x (stageExponent q bound) n)
      else x

private def pMinusOneStage1Core (n base bound : Nat) : PMinusOneResult :=
  if n < 4 ∨ base ≤ 1 ∨ n ≤ base then .noFactor
  else
    let initial := Nat.gcd base n
    if 1 < initial then
      if initial < n ∧ n % initial = 0 then .factor initial else .whole
    else
      let x := raiseSmooth n bound (primesBelow (bound + 1)) (base % n)
      let g := Nat.gcd ((x + n - 1) % n) n
      if g = 1 then .noFactor
      else if 1 < g ∧ g < n ∧ n % g = 0 then .factor g
      else .whole

/-- One deterministic Pollard `p - 1` stage-1 attempt. Invalid bases or
moduli return `noFactor`; a gcd equal to the modulus is reported separately
as `whole`. The effective smoothness bound is `smoothBound bound`, with every prime up to that bound included by the runtime sieve. -/
def pMinusOneStage1 (n base bound : Nat) : PMinusOneResult :=
  pMinusOneStage1Core n base (smoothBound bound)

/-- One counted, resumable Pollard `p - 1` stage-1 attempt. The deterministic
primitive consumes no generator words, but every call costs exactly one search
attempt whether it returns `noFactor`, a proper factor, or `whole`. -/
def pMinusOneStage1Counted (n base bound : Nat) (r : Rand) :
    PMinusOneAttempt :=
  ⟨pMinusOneStage1 n base bound, 1, r⟩

/-- Requests beyond the supported runtime range are exactly capped. -/
theorem pMinusOneStage1_bound (n base bound : Nat) :
    pMinusOneStage1 n base bound =
      pMinusOneStage1 n base (smoothBound bound) := by
  simp [pMinusOneStage1]

/-- Every reported factor is a dynamically checked proper divisor. -/
theorem pMinusOneStage1_spec {n base bound d : Nat}
    (h : pMinusOneStage1 n base bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold pMinusOneStage1 pMinusOneStage1Core at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · split at h
      · rename_i _ hvalid
        injection h with heq
        subst d
        exact ⟨by assumption, hvalid.1,
          Nat.dvd_of_mod_eq_zero hvalid.2⟩
      · cases h
    · split at h
      · cases h
      · split at h
        · rename_i _ hg hvalid
          injection h with heq
          subst d
          exact ⟨hvalid.1, hvalid.2.1,
            Nat.dvd_of_mod_eq_zero hvalid.2.2⟩
        · cases h

/-- A proper factor returned through the counted boundary satisfies the same
dynamically checked contract as the compatibility result. -/
theorem pMinusOneStage1Counted_spec {n base bound d : Nat} {r : Rand}
    (h : (pMinusOneStage1Counted n base bound r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  exact pMinusOneStage1_spec h

namespace PMinusOne

/-- Independent ceiling for the continuation's prime enumeration. -/
def stage2BoundCap : Nat := 4194304

/-- Never increase the requested continuation bound. -/
def stage2Bound (bound : Nat) : Nat := min bound stage2BoundCap

@[simp] theorem stage2Bound_idem (bound : Nat) :
    stage2Bound (stage2Bound bound) = stage2Bound bound := by
  simp [stage2Bound, Nat.min_assoc]

/-- One flushed product and the recovery gcds actually executed. -/
structure Batch where
  firstPrime : Nat
  lastPrime : Nat
  length : Nat
  gcd : Nat
  recovery : List Nat := []
deriving Repr, DecidableEq

/-- Untrusted diagnostics produced by one execution, including zero-attempt
policy skips. Reasons distinguish invalid inputs, empty intervals, setup
factors, stage factors, whole gcds, and ready residues. -/
structure Event where
  subject : Nat
  base : Option Nat := none
  requestedB1 : Nat
  effectiveB1 : Nat
  requestedB2 : Option Nat := none
  effectiveB2 : Option Nat := none
  outcome : PMinusOneResult := .noFactor
  reason : String := ""
  candidates : Nat := 0
  giantAdvances : Nat := 0
  multiplications : Nat := 0
  setupGcds : Nat := 0
  batchGcds : Nat := 0
  recoveryGcds : Nat := 0
  batches : List Batch := []
deriving Repr, DecidableEq, Inhabited

/-- The stage boundary retains its residue only after both gcds equal one. -/
structure Stage1 where
  result : PMinusOneResult
  residue : Option Nat
  event : Event
deriving Repr, DecidableEq

private def startCore (n a bound : Nat) : Stage1 := Id.run do
  let event : Event := { subject := n, base := some a, requestedB1 := bound, effectiveB1 := bound }
  if n < 4 ∨ a ≤ 1 ∨ n ≤ a then
    return ⟨.noFactor, none, { event with reason := "invalid-input" }⟩
  let initial := Nat.gcd a n
  let event := { event with setupGcds := 1 }
  if 1 < initial then
    if initial < n ∧ n % initial = 0 then
      return ⟨.factor initial, none,
        { event with outcome := .factor initial, reason := "setup-factor" }⟩
    else
      return ⟨.whole, none, { event with outcome := .whole, reason := "setup-whole" }⟩
  let x := raiseSmooth n bound (primesBelow (bound + 1)) (a % n)
  let g := Nat.gcd ((x + n - 1) % n) n
  if g = 1 then
    return ⟨.noFactor, some x, { event with reason := "ready-residue" }⟩
  else if 1 < g ∧ g < n ∧ n % g = 0 then
    return ⟨.factor g, none,
      { event with outcome := .factor g, reason := "stage-factor" }⟩
  else
    return ⟨.whole, none, { event with outcome := .whole, reason := "stage-whole" }⟩

/-- Execute stage 1 once, retaining the ready residue and its diagnostics. -/
def start (n a B₁ : Nat) : Stage1 :=
  let s := startCore n a (smoothBound B₁)
  { s with event := { s.event with requestedB1 := B₁ } }

@[simp] theorem start_result (n a B₁ : Nat) :
    (start n a B₁).result = pMinusOneStage1 n a B₁ := by
  unfold start startCore pMinusOneStage1 pMinusOneStage1Core
  simp only [Id.run, pure]
  split <;> rename_i h
  · rfl
  · split
    · split <;> rfl
    · split
      · rfl
      · split <;> rfl

private theorem largestPower_spec {q bound : Nat} (hq : 0 < q) :
    ∀ fuel acc, 0 < acc → acc ≤ bound → bound < acc * q ^ fuel →
      let d := largestPower q bound fuel acc
      d ≤ bound ∧ bound < d * q ∧ ∃ e, d = acc * q ^ e := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc _ hle hlt
    simp only [Nat.pow_zero, Nat.mul_one] at hlt
    omega
  | succ fuel ih =>
    intro acc hpos hle hlt
    dsimp only [largestPower]
    split
    · rename_i h
      have hle' := (Nat.le_div_iff_mul_le hq).mp h
      have hlt' : bound < (acc * q) * q ^ fuel := by
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlt
      obtain ⟨hd, hb, e, he⟩ := ih (acc * q) (Nat.mul_pos hpos hq) hle' hlt'
      refine ⟨hd, hb, e + 1, ?_⟩
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
    · rename_i h
      exact ⟨hle, Nat.lt_mul_of_div_lt (by omega) hq, 0, by simp⟩

/-- Largest power of the supplied prime within the effective first bound. -/
def primePower (q B₁ : Nat) : Nat := stageExponent q (smoothBound B₁)

/-- The loop computes the maximal prime power, including its full exponent,
not just the product of small distinct primes. -/
theorem primePower_spec {q B₁ : Nat} (hq : Prime q) (hb : q ≤ smoothBound B₁) :
    ∃ e, primePower q B₁ = q ^ e ∧ q ^ e ≤ smoothBound B₁ ∧
      ∀ j, q ^ j ≤ smoothBound B₁ → j ≤ e := by
  have hlog : smoothBound B₁ < q * q ^ ((smoothBound B₁).log2 + 1) :=
    Nat.lt_of_lt_of_le Nat.lt_log2_self
      (Nat.le_trans (Nat.pow_le_pow_left hq.two_le _)
        (Nat.le_mul_of_pos_left _ hq.pos))
  obtain ⟨hle, hlt, e, he⟩ := largestPower_spec hq.pos
    ((smoothBound B₁).log2 + 1) q hq.pos hb hlog
  have heq : primePower q B₁ = q ^ (e + 1) := by
    simpa [primePower, stageExponent, Nat.pow_succ, Nat.mul_comm] using he
  refine ⟨e + 1, heq, ?_, ?_⟩
  · simpa [primePower, stageExponent] using heq ▸ hle
  · intro j hj
    by_cases h : j ≤ e + 1
    · exact h
    apply False.elim
    have hm : q ^ (e + 1) * q ≤ q ^ j := by
      rw [← Nat.pow_succ]
      exact Nat.pow_le_pow_right hq.pos (by omega)
    have hd : smoothBound B₁ < q ^ (e + 1) * q := by
      simpa only [← heq, primePower, stageExponent] using hlt
    omega

/-- The stage-1 exponent, used in statements only. Execution applies each
prime power successively and never constructs this product. -/
def exponent (B₁ : Nat) : Nat :=
  ((primesBelow (smoothBound B₁ + 1)).map (primePower · B₁)).prod

private theorem raiseSmooth_eq (n bound : Nat) (hn : 0 < n) (qs : List Nat)
    (hq : ∀ q ∈ qs, q ≤ bound) (a : Nat) :
    raiseSmooth n bound qs (a % n) =
      a ^ (qs.map (stageExponent · bound)).prod % n := by
  induction qs generalizing a with
  | nil => simp [raiseSmooth]
  | cons q qs ih =>
    have hq' := hq q (by simp)
    simp only [raiseSmooth, ite_eq_left hq', HexArith.powModNat_eq _ _ _ hn]
    rw [← Nat.pow_mod, ih (by intro q h; exact hq q (by simp [h]))]
    simp [Nat.pow_mul, List.prod_cons, List.map_cons]

/-- A ready residue is exactly the reduced power computed by stage 1, on
valid coprime input after its final gcd equals one. -/
theorem start_residue {n a B₁ x : Nat} (h : (start n a B₁).residue = some x) :
    4 ≤ n ∧ 1 < a ∧ a < n ∧ Nat.Coprime a n ∧
      x = a ^ exponent B₁ % n ∧ Nat.gcd ((x + n - 1) % n) n = 1 := by
  unfold start startCore at h
  simp only [Id.run, pure] at h
  split at h
  · cases h
  · rename_i hv
    have hn : 0 < n := by omega
    split at h
    · split at h <;> cases h
    · rename_i hg
      have hcop : Nat.Coprime a n := by
        have := Nat.gcd_pos_of_pos_right a hn
        unfold Nat.Coprime
        omega
      split at h
      · rename_i hx
        simp only [Option.some.injEq] at h
        subst x
        refine ⟨by omega, by omega, by omega, hcop, ?_, hx⟩
        exact raiseSmooth_eq n _ hn _
          (by intro q hq; have := (mem_primesBelow.mp hq).1; omega) a
      · split at h <;> cases h

/-- Conversely, valid input and the two unit gcds always expose the residue. -/
theorem start_residue_of {n a B₁ : Nat} (hn : 4 ≤ n) (ha : 1 < a) (han : a < n)
    (hc : Nat.Coprime a n)
    (hg : Nat.gcd ((a ^ exponent B₁ % n + n - 1) % n) n = 1) :
    (start n a B₁).residue = some (a ^ exponent B₁ % n) := by
  have hv : ¬ (n < 4 ∨ a ≤ 1 ∨ n ≤ a) := by omega
  have hpow : raiseSmooth n (smoothBound B₁) (primesBelow (smoothBound B₁ + 1))
      (a % n) = a ^ exponent B₁ % n :=
    raiseSmooth_eq n _ (by omega) _
      (by intro q hq; have := (mem_primesBelow.mp hq).1; omega) a
  have hc' : Nat.gcd a n = 1 := hc
  simp [start, startCore, hv, hc', hpow, hg]

/-- Ready residues lie in range and are units; the adjacent residue also
has gcd one, which is precisely the continuation boundary. -/
theorem start_ready {n a B₁ x : Nat} (h : (start n a B₁).residue = some x) :
    x < n ∧ Nat.gcd x n = 1 ∧ Nat.gcd ((x + n - 1) % n) n = 1 := by
  obtain ⟨hn, _, _, hc, hx, hg⟩ := start_residue h
  refine ⟨hx ▸ Nat.mod_lt _ (by omega), ?_, hg⟩
  rw [hx, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hc.pow_left _

/-- Complete ascending interval, including the small primes dividing 210. -/
def primes (B₁ B₂ : Nat) : List Nat :=
  if stage2Bound B₂ ≤ smoothBound B₁ then []
  else (primesBelow (stage2Bound B₂ + 1)).filter (smoothBound B₁ < ·)

@[simp] theorem mem_primes {q B₁ B₂ : Nat} :
    q ∈ primes B₁ B₂ ↔ Prime q ∧ smoothBound B₁ < q ∧ q ≤ stage2Bound B₂ := by
  unfold primes
  split
  · simp only [List.not_mem_nil, false_iff, not_and]
    omega
  · simp only [List.mem_filter, mem_primesBelow, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h, hp⟩, hb⟩
      exact ⟨hp, hb, by omega⟩
    · rintro ⟨hp, hb, h⟩
      exact ⟨⟨by omega, hp⟩, hb⟩

theorem primes_pairwise (B₁ B₂ : Nat) : (primes B₁ B₂).Pairwise (· < ·) := by
  unfold primes
  split
  · exact .nil
  · exact (primesBelow_pairwise_lt _).filter _

theorem primes_nodup (B₁ B₂ : Nat) : (primes B₁ B₂).Nodup :=
  (primes_pairwise B₁ B₂).imp Nat.ne_of_lt

/-- Factor validation is attached to the actual exit, with no extra check
when projecting the public result. The proof is erased by compilation. -/
private structure Checked (n : Nat) where
  result : PMinusOneResult
  valid : ∀ d, result = .factor d → 1 < d ∧ d < n ∧ d ∣ n

private def miss (n : Nat) : Checked n := ⟨.noFactor, by intro d h; cases h⟩
private def whole (n : Nat) : Checked n := ⟨.whole, by intro d h; cases h⟩

private def checkGcd (n g : Nat) : Checked n :=
  if g = 1 then miss n
  else if h : 1 < g ∧ g < n ∧ n % g = 0 then
    ⟨.factor g, by
      intro d hd
      cases hd
      exact ⟨h.1, h.2.1, Nat.dvd_of_mod_eq_zero h.2.2⟩⟩
  else whole n

private def recoverCore (n : Nat) : List (Nat × Nat) → Checked n × List Nat
  | [] => (whole n, [])
  | (_, t) :: rest =>
    let g := Nat.gcd t n
    let c := checkGcd n g
    match c.result with
    | .factor _ => (c, [g])
    | _ =>
      let tail := recoverCore n rest
      (tail.1, g :: tail.2)

/-- Recover from retained terms in their original order. A whole leaf does
not hide a proper divisor in a later leaf. Returns only executed gcds. -/
def recover (n : Nat) (terms : List (Nat × Nat)) : PMinusOneResult × List Nat :=
  let r := recoverCore n terms
  (r.1.result, r.2)

theorem recover_spec {n d : Nat} {terms : List (Nat × Nat)}
    (h : (recover n terms).1 = .factor d) : 1 < d ∧ d < n ∧ d ∣ n :=
  (recoverCore n terms).1.valid d h

private def babyPowers (n x : Nat) : Nat → Array Nat × Nat
  | 0 => (#[], 1 % n)
  | k + 1 =>
    let (u, v) := babyPowers n x k
    (u.push v, v * x % n)

private theorem babyPowers_size (n x k : Nat) : (babyPowers n x k).1.size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [babyPowers, ih]

private theorem babyPowers_step (n x k : Nat) : (babyPowers n x k).2 = x ^ k % n := by
  induction k with
  | zero => simp [babyPowers]
  | succ k ih => simp [babyPowers, ih, Nat.pow_succ, Nat.mod_mul_mod]

private theorem babyPowers_get (n x k j : Nat) (hj : j < k) :
    (babyPowers n x k).1[j]'(by rw [babyPowers_size]; exact hj) = x ^ j % n := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : j < k
    · simp only [babyPowers]
      rw [Array.getElem_push_lt (by rw [babyPowers_size]; exact h)]
      exact ih h
    · have heq : j = k := by omega
      subst j
      simpa only [babyPowers, babyPowers_size, babyPowers_step] using
        (Array.getElem_push_eq (xs := (babyPowers n x k).1)
          (x := (babyPowers n x k).2))

/-- All 210 babies and the next power, built by successive multiplication. -/
def babies (n x : Nat) : Array Nat × Nat := babyPowers n x 210

@[simp] theorem babies_size (n x : Nat) : (babies n x).1.size = 210 :=
  babyPowers_size ..

theorem babies_step (n x : Nat) : (babies n x).2 = x ^ 210 % n :=
  babyPowers_step ..

theorem babies_get (n x j : Nat) (hj : j < 210) :
    (babies n x).1[j]'(by rw [babies_size]; exact hj) = x ^ j % n :=
  babyPowers_get n x 210 j hj

/-- Exact multiply count of the direct binary power used for the initial
 giant: one square per bit plus one multiply per set bit. -/
def powerCost (i : Nat) : Nat :=
  HexArith.bitLength i + ((List.range (HexArith.bitLength i)).filter i.testBit).length

/-- Advance the giant through every intervening block. -/
def advance (n h : Nat) : Nat → Nat → Nat
  | 0, v => v
  | k + 1, v => advance n h k (v * h % n)

/-- Each giant advance is exactly multiplication by another step power. -/
theorem advance_eq (n h k v : Nat) :
    advance n h k (v % n) = v * h ^ k % n := by
  induction k generalizing v with
  | zero => simp [advance]
  | succ k ih =>
    simp only [advance, Nat.mod_mul_mod]
    rw [ih]
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The division/remainder index map reconstructs every candidate power. -/
theorem giant_mul_baby (n x q : Nat) (hn : 0 < n) :
    (HexArith.powModBits (babies n x).2 (q / 210) n *
      (babies n x).1[q % 210]'(by rw [babies_size]; omega)) % n = x ^ q % n := by
  rw [HexArith.powModBits_eq _ _ _ hn, babies_step,
      babies_get n x (q % 210) (by omega), ← Nat.pow_mod, ← Nat.mul_mod,
      ← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]

/-- Candidate subtraction after one baby/giant multiplication. -/
def term (n v u : Nat) : Nat := ((v * u) % n + n - 1) % n

private theorem dvd_sub_one {n p z : Nat} (hn : 0 < n) (hp : 1 < p)
    (hd : p ∣ n) : p ∣ (z + n - 1) % n ↔ z % p = 1 := by
  rw [Nat.dvd_mod_iff hd]
  have hnmod := Nat.mod_eq_zero_of_dvd hd
  have hpmod : 1 % p = 1 := Nat.mod_eq_of_lt hp
  constructor
  · intro h
    have hw := Nat.mod_eq_zero_of_dvd h
    have heq : z + n = (z + n - 1) + 1 := by omega
    have heqmod := congrArg (· % p) heq
    simpa [Nat.add_mod, hnmod, hw, hpmod] using heqmod
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.sub_mod_eq_zero_of_mod_eq
    simpa [Nat.add_mod, hnmod, hpmod] using h

/-- A candidate captures a prime divisor exactly when the base order divides
its exponent. The hypothesis identifies the actual baby/giant product. -/
theorem term_dvd_iff {n p a M x q v u : Nat} (hn : 0 < n) (hp : Prime p)
    (hd : p ∣ n) (hc : Nat.Coprime a n) (hx : x = a ^ M % n)
    (ht : v * u % n = x ^ q % n) :
    p ∣ term n v u ↔ orderOf a p ∣ M * q := by
  have hc' := Nat.Coprime.coprime_dvd_right hd hc
  have hpos := orderOf_pos hp.one_lt hc'
  rw [term, dvd_sub_one hn hp.one_lt hd, ht, hx,
    ← Nat.pow_mod, Nat.mod_mod_of_dvd _ hd, ← Nat.pow_mul]
  constructor
  · intro h
    by_cases hz : M * q = 0
    · simp [hz]
    · exact orderOf_dvd_of_pow_eq_one hp.one_lt (by omega)
        (by simpa [Nat.mod_eq_of_lt hp.one_lt] using h)
  · intro h
    simpa [Nat.mod_eq_of_lt hp.one_lt] using pow_eq_one_of_orderOf_dvd hpos h

/-- A stage-1 gcd of one rules out the order already dividing its exponent. -/
theorem start_order_not_dvd {n p a B₁ x : Nat} (hp : Prime p) (hd : p ∣ n)
    (hx : (start n a B₁).residue = some x) : ¬ orderOf a p ∣ exponent B₁ := by
  obtain ⟨hn, _, _, hc, heq, hg⟩ := start_residue hx
  intro h
  have hc' := Nat.Coprime.coprime_dvd_right hd hc
  have hpow := pow_eq_one_of_orderOf_dvd (orderOf_pos hp.one_lt hc') h
  have hxmod : x % p = 1 := by
    rw [heq, Nat.mod_mod_of_dvd _ hd]
    simpa [Nat.mod_eq_of_lt hp.one_lt] using hpow
  have hterm := (dvd_sub_one (by omega : 0 < n) hp.one_lt hd).mpr hxmod
  have := Nat.dvd_gcd hterm hd
  rw [hg] at this
  have := Nat.dvd_one.mp this
  have := hp.two_le
  omega

private structure Scan (n : Nat) where
  checked : Checked n
  event : Event

private def flush (n product : Nat) (buffer : Array (Nat × Nat)) :
    Checked n × Batch :=
  let g := Nat.gcd product n
  let batch : Batch := { firstPrime := buffer[0]!.1, lastPrime := buffer[buffer.size - 1]!.1, length := buffer.size, gcd := g }
  if g = n then
    let r := recoverCore n buffer.toList
    (r.1, { batch with recovery := r.2 })
  else (checkGcd n g, batch)

-- Keep recursive scans in tail position: cap-sized intervals must not grow
-- the native call stack with the candidate count.
private def scan (n h : Nat) (u : Array Nat) (keepBatches : Bool) :
    List Nat → Nat → Nat → Nat → Array (Nat × Nat) → Event → Scan n
  | [], _, _, _, _, event => ⟨miss n, event⟩
  | q :: qs, i, v, product, buffer, event => Id.run do
    let steps := q / 210 - i
    let v := advance n h steps v
    let t := term n v u[q % 210]!
    let product := product * t % n
    let buffer := buffer.push (q, t)
    let event := { event with candidates := event.candidates + 1, giantAdvances := event.giantAdvances + steps, multiplications := event.multiplications + steps + 2 }
    if buffer.size = 32 ∨ qs.isEmpty then
      let (c, batch) := flush n product buffer
      let event := { event with
        batchGcds := event.batchGcds + 1
        recoveryGcds := event.recoveryGcds + batch.recovery.length
        batches := if keepBatches then batch :: event.batches else [] }
      match c.result with
      | .noFactor => return scan n h u keepBatches qs (q / 210) v (1 % n) #[] event
      | _ => return ⟨c, event⟩
    else
      return scan n h u keepBatches qs (q / 210) v product buffer event

private theorem scan_result (n h : Nat) (u : Array Nat) (qs : List Nat)
    (i v product : Nat) (buffer : Array (Nat × Nat)) (e₁ e₂ : Event)
    (trace₁ trace₂ : Bool) :
    (scan n h u trace₁ qs i v product buffer e₁).checked.result =
      (scan n h u trace₂ qs i v product buffer e₂).checked.result := by
  induction qs generalizing i v product buffer e₁ e₂ with
  | nil => rfl
  | cons q qs ih =>
    simp only [scan, Id.run, pure]
    split
    · split
      · apply ih
      · rfl
    · apply ih

private def intervalCore (n x : Nat) (qs : List Nat) (event : Event)
    (keepBatches : Bool := true) : Scan n :=
  match qs with
  | [] => ⟨miss n, { event with reason := "no-primes" }⟩
  | q :: _ =>
    let (u, h) := babies n x
    let i := q / 210
    let v := HexArith.powModBits h i n
    let event := { event with multiplications := 210 + powerCost i }
    scan n h u keepBatches qs i v (1 % n) #[] event

set_option maxRecDepth 4096 in
private theorem intervalCore_result (n x : Nat) (qs : List Nat) (e₁ e₂ : Event)
    (trace₁ trace₂ : Bool) :
    (intervalCore n x qs e₁ trace₁).checked.result =
      (intervalCore n x qs e₂ trace₂).checked.result := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    unfold intervalCore
    exact scan_result n (babies n x).2 (babies n x).1 (q :: qs)
      (q / 210) (HexArith.powModBits (babies n x).2 (q / 210) n) (1 % n) #[]
      _ _ trace₁ trace₂

private def stage2Core (n x b₁ b₂ : Nat) (keepBatches : Bool := true) : Scan n := Id.run do
  let event : Event := { subject := n, requestedB1 := b₁, effectiveB1 := b₁, requestedB2 := some b₂, effectiveB2 := some b₂ }
  if n < 4 then
    return ⟨miss n, { event with reason := "invalid-modulus" }⟩
  let x := x % n
  let first := checkGcd n (Nat.gcd x n)
  let event := { event with setupGcds := 1 }
  if first.result ≠ .noFactor then
    return ⟨first, { event with reason := "residue-gcd" }⟩
  let second := checkGcd n (Nat.gcd ((x + n - 1) % n) n)
  let event := { event with setupGcds := 2 }
  if second.result ≠ .noFactor then
    return ⟨second, { event with reason := "residue-minus-one-gcd" }⟩
  if b₂ ≤ b₁ then
    return ⟨miss n, { event with reason := "empty-interval" }⟩
  let qs := primes b₁ b₂
  return intervalCore n x qs event keepBatches

/-- Total raw-residue continuation. Every factor exit validates range and
 divisibility; no provenance of the supplied residue is assumed. -/
def stage2 (n x B₁ B₂ : Nat) : PMinusOneResult :=
  (stage2Core n x (smoothBound B₁) (stage2Bound B₂)).checked.result

theorem stage2_spec {n x B₁ B₂ d : Nat} (h : stage2 n x B₁ B₂ = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n :=
  (stage2Core n x (smoothBound B₁) (stage2Bound B₂)).checked.valid d h

theorem stage2_bound (n x B₁ B₂ : Nat) :
    stage2 n x B₁ B₂ = stage2 n x (smoothBound B₁) (stage2Bound B₂) := by
  simp [stage2]

/-- Standalone search preserves the stage boundary instead of recomputing it. -/
def search (n a B₁ B₂ : Nat) : PMinusOneResult :=
  let s := start n a B₁
  match s.residue with
  | some x => if smoothBound B₁ < stage2Bound B₂ then stage2 n x B₁ B₂ else s.result
  | none => s.result

theorem search_spec {n a B₁ B₂ d : Nat} (h : search n a B₁ B₂ = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold search at h
  dsimp only at h
  split at h
  · split at h
    · exact stage2_spec h
    · rw [start_result] at h
      exact pMinusOneStage1_spec h
  · rw [start_result] at h
    exact pMinusOneStage1_spec h

@[simp] theorem start_residue_bound (n a B₁ : Nat) :
    (start n a (smoothBound B₁)).residue = (start n a B₁).residue := by
  simp [start]

theorem search_bound (n a B₁ B₂ : Nat) :
    search n a B₁ B₂ = search n a (smoothBound B₁) (stage2Bound B₂) := by
  simp only [search, start_residue_bound, smoothBound_idem, stage2Bound_idem,
    start_result, pMinusOneStage1_bound n a B₁]
  split
  · split
    · exact stage2_bound ..
    · rfl
  · rfl

/-- Counted calls preserve deterministic state, including failed calls. -/
structure Run where
  result : PMinusOneResult
  attempts : Nat
  rand : Rand
  events : List Event
deriving Repr, DecidableEq

/-- The stage-1 exponentiation loop on prepared primes and a normalized
base. Used to measure exponentiation separately from enumeration and setup. -/
def smoothPower (n x B₁ : Nat) (ps : List Nat) : Nat :=
  raiseSmooth n (smoothBound B₁) ps x

/-- The continuation on a prepared prime interval and saved residue. This
measurement boundary omits the public raw-residue preflight and enumeration;
callers supply the prepared data. Factor exits are still dynamically checked.
The standalone APIs perform all preparation and remain the general entry points. -/
def fromPrepared (n x B₁ B₂ : Nat) (qs : List Nat) (r : Rand)
    (keepBatches : Bool := true) : Run :=
  let event : Event := {
    subject := n
    requestedB1 := B₁
    effectiveB1 := smoothBound B₁
    requestedB2 := some B₂
    effectiveB2 := some (stage2Bound B₂) }
  let s := intervalCore n x qs event keepBatches
  ⟨s.checked.result, 1, r,
    [{ s.event with outcome := s.checked.result, batches := s.event.batches.reverse }]⟩

theorem fromPrepared_spec {n x B₁ B₂ d : Nat} {qs : List Nat} {r : Rand}
    {keepBatches : Bool}
    (h : (fromPrepared n x B₁ B₂ qs r keepBatches).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n :=
  (intervalCore n x qs _ keepBatches).checked.valid d h

/-- Retaining batch details cannot change the prepared continuation result. -/
theorem fromPrepared_result (n x B₁ B₂ : Nat) (qs : List Nat) (r : Rand)
    (keepBatches : Bool) :
    (fromPrepared n x B₁ B₂ qs r keepBatches).result =
      (fromPrepared n x B₁ B₂ qs r).result := intervalCore_result ..

@[simp] theorem fromPrepared_attempts (n x B₁ B₂ : Nat) (qs : List Nat) (r : Rand)
    (keepBatches : Bool) : (fromPrepared n x B₁ B₂ qs r keepBatches).attempts = 1 := by rfl

@[simp] theorem fromPrepared_rand (n x B₁ B₂ : Nat) (qs : List Nat) (r : Rand)
    (keepBatches : Bool) : (fromPrepared n x B₁ B₂ qs r keepBatches).rand = r := by rfl

/-- One continuation always costs exactly one semantic attempt. -/
def stage2Counted (n x B₁ B₂ : Nat) (r : Rand) : Run :=
  let s := stage2Core n x (smoothBound B₁) (stage2Bound B₂)
  let event := { s.event with requestedB1 := B₁, requestedB2 := some B₂, outcome := s.checked.result, batches := s.event.batches.reverse }
  ⟨s.checked.result, 1, r, [event]⟩

/-- Charge stage 1 once and the continuation only when actually invoked. -/
def searchCounted (n a B₁ B₂ : Nat) (r : Rand) : Run :=
  let s := start n a B₁
  match s.residue with
  | some x =>
    if smoothBound B₁ < stage2Bound B₂ then
      let rest := stage2Counted n x B₁ B₂ r
      { rest with attempts := 1 + rest.attempts, events := s.event :: rest.events }
    else ⟨s.result, 1, r, [s.event]⟩
  | none => ⟨s.result, 1, r, [s.event]⟩

@[simp] theorem stage2Counted_result (n x B₁ B₂ : Nat) (r : Rand) :
    (stage2Counted n x B₁ B₂ r).result = stage2 n x B₁ B₂ := by rfl

@[simp] theorem searchCounted_result (n a B₁ B₂ : Nat) (r : Rand) :
    (searchCounted n a B₁ B₂ r).result = search n a B₁ B₂ := by
  unfold searchCounted search
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem stage2Counted_spec {n x B₁ B₂ d : Nat} {r : Rand}
    (h : (stage2Counted n x B₁ B₂ r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := stage2_spec h

theorem searchCounted_spec {n a B₁ B₂ d : Nat} {r : Rand}
    (h : (searchCounted n a B₁ B₂ r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := search_spec (by simpa using h)

@[simp] theorem stage2Counted_attempts (n x B₁ B₂ : Nat) (r : Rand) :
    (stage2Counted n x B₁ B₂ r).attempts = 1 := by rfl

theorem searchCounted_attempts (n a B₁ B₂ : Nat) (r : Rand) :
    (searchCounted n a B₁ B₂ r).attempts =
      1 + (match (start n a B₁).residue with
        | some _ => if smoothBound B₁ < stage2Bound B₂ then 1 else 0
        | none => 0) := by
  cases hr : (start n a B₁).residue with
  | none => simp [searchCounted, hr]
  | some x =>
    simp only [searchCounted, hr]
    split <;> rfl

@[simp] theorem stage2Counted_rand (n x B₁ B₂ : Nat) (r : Rand) :
    (stage2Counted n x B₁ B₂ r).rand = r := by rfl

@[simp] theorem searchCounted_rand (n a B₁ B₂ : Nat) (r : Rand) :
    (searchCounted n a B₁ B₂ r).rand = r := by
  unfold searchCounted
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem checkGcd_result (n t : Nat) :
    (checkGcd n (Nat.gcd t n)).result =
      if 1 < Nat.gcd t n ∧ Nat.gcd t n < n then .factor (Nat.gcd t n)
      else if Nat.gcd t n = 1 then .noFactor else .whole := by
  have hmod := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right t n)
  by_cases h : Nat.gcd t n = 1
  · simp [checkGcd, h, miss]
  · by_cases hv : 1 < Nat.gcd t n ∧ Nat.gcd t n < n
    · simp [checkGcd, h, hv, hmod]
    · simp [checkGcd, h, hv, hmod, whole]

/-- Recovery succeeds exactly when a retained leaf has a proper gcd. -/
theorem recover_success (n : Nat) (ts : List (Nat × Nat)) :
    (∃ d, (recover n ts).1 = .factor d) ↔
      ∃ qt ∈ ts, 1 < Nat.gcd qt.2 n ∧ Nat.gcd qt.2 n < n := by
  induction ts with
  | nil => simp [recover, recoverCore, whole]
  | cons qt ts ih =>
    by_cases hp : 1 < Nat.gcd qt.2 n ∧ Nat.gcd qt.2 n < n
    · simp only [recover, recoverCore, checkGcd_result, ite_eq_left hp]
      constructor
      · intro _; exact ⟨qt, by simp, hp⟩
      · intro _; exact ⟨_, rfl⟩
    · by_cases h1 : Nat.gcd qt.2 n = 1
      · simpa [recover, recoverCore, checkGcd_result, hp, h1, checkGcd, miss] using ih
      · simpa [recover, recoverCore, checkGcd_result, hp, h1] using ih

/-- Modular batch product, reducing after each multiplication as in the scan. -/
def batchProduct (n : Nat) (ts : List Nat) : Nat :=
  ts.foldl (fun acc t => acc * t % n) (1 % n)

private theorem foldProduct (n : Nat) (ts : List Nat) (a : Nat) :
    ts.foldl (fun acc t => acc * t % n) (a % n) = a * ts.prod % n := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.mod_mul_mod]
    rw [ih]
    simp [List.prod_cons, Nat.mul_assoc]

theorem batchProduct_eq (n : Nat) (ts : List Nat) : batchProduct n ts = ts.prod % n := by
  simpa [batchProduct] using foldProduct n ts 1

private theorem dvd_product {p t : Nat} {ts : List Nat} (ht : t ∈ ts) (hd : p ∣ t) :
    p ∣ ts.prod := by
  induction ts with
  | nil => simp at ht
  | cons a ts ih =>
    simp only [List.mem_cons] at ht
    simp only [List.prod_cons]
    rcases ht with rfl | ht
    · exact Nat.dvd_mul_right_of_dvd hd _
    · exact Nat.dvd_mul_left_of_dvd (ih ht) _

/-- A captured prime divides the gcd at a reached batch flush. -/
theorem batch_divisor {p n t : Nat} {ts : List Nat} (hp : Prime p) (hn : 0 < n)
    (hd : p ∣ n) (ht : t ∈ ts) (hpt : p ∣ t) :
    p ∣ Nat.gcd (batchProduct n ts) n ∧ 1 < Nat.gcd (batchProduct n ts) n := by
  have hprod : p ∣ batchProduct n ts := by
    rw [batchProduct_eq]
    exact (Nat.dvd_mod_iff hd).mpr (dvd_product ht hpt)
  have hg := Nat.dvd_gcd hprod hd
  exact ⟨hg, Nat.lt_of_lt_of_le hp.one_lt
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hn) hg)⟩

/-- Flush a retained batch; the scan calls the same implementation. -/
def flushBatch (n product : Nat) (buffer : Array (Nat × Nat)) : PMinusOneResult × Batch :=
  let r := flush n product buffer
  (r.1.result, r.2)

/-- A reached flush with a proper batch gcd returns that divisor immediately. -/
theorem flush_factor {n product : Nat} {buffer : Array (Nat × Nat)}
    (hg : 1 < Nat.gcd product n ∧ Nat.gcd product n < n) :
    (flushBatch n product buffer).1 = .factor (Nat.gcd product n) := by
  have hne : Nat.gcd product n ≠ n := by omega
  simp [flushBatch, flush, hne, checkGcd_result, hg]

private theorem recover_ne_noFactor (n : Nat) (ts : List (Nat × Nat)) :
    (recover n ts).1 ≠ .noFactor := by
  induction ts with
  | nil => simp [recover, recoverCore, whole]
  | cons qt ts ih =>
    by_cases hp : 1 < Nat.gcd qt.2 n ∧ Nat.gcd qt.2 n < n
    · simp [recover, recoverCore, checkGcd_result, hp]
    · by_cases h1 : Nat.gcd qt.2 n = 1
      · simpa [recover, recoverCore, checkGcd_result, hp, h1, checkGcd, miss] using ih
      · simpa [recover, recoverCore, checkGcd_result, hp, h1] using ih

/-- Without a proper leaf, recovery terminates with whole modulus. -/
theorem recover_whole (n : Nat) (ts : List (Nat × Nat)) :
    (recover n ts).1 = .whole ↔
      ¬ ∃ qt ∈ ts, 1 < Nat.gcd qt.2 n ∧ Nat.gcd qt.2 n < n := by
  rw [← recover_success]
  constructor
  · intro h ⟨d, hd⟩
    rw [h] at hd
    cases hd
  · intro h
    cases hr : (recover n ts).1 with
    | noFactor => exact False.elim (recover_ne_noFactor n ts hr)
    | whole => rfl
    | factor d => exact False.elim (h ⟨d, hr⟩)

private theorem not_dvd_product {r : Nat} (hr : Prime r) (ts : List Nat)
    (ht : ∀ t ∈ ts, ¬ r ∣ t) : ¬ r ∣ ts.prod := by
  induction ts with
  | nil =>
    simp only [List.prod_nil]
    intro h
    have := Nat.dvd_one.mp h
    have := hr.two_le
    omega
  | cons t ts ih =>
    intro h
    rcases hr.dvd_mul.mp h with h | h
    · exact ht t (by simp) h
    · exact ih (by intro t h; exact ht t (by simp [h])) h

/-- On a semiprime, a captured component and exclusion of the other component
from every term force the batch gcd to equal the captured prime. -/
theorem batch_gcd {p r t : Nat} {ts : List Nat}
    (hr : Prime r) (ht : t ∈ ts) (hp : p ∣ t)
    (hs : ∀ s ∈ ts, ¬ r ∣ s) : Nat.gcd (batchProduct (p * r) ts) (p * r) = p := by
  have hpdiv : p ∣ p * r := Nat.dvd_mul_right _ _
  have hrdiv : r ∣ p * r := Nat.dvd_mul_left _ _
  have hprod : p ∣ batchProduct (p * r) ts := by
    rw [batchProduct_eq]
    exact (Nat.dvd_mod_iff hpdiv).mpr (dvd_product ht hp)
  have hnot : ¬ r ∣ batchProduct (p * r) ts := by
    rw [batchProduct_eq, Nat.dvd_mod_iff hrdiv]
    exact not_dvd_product hr ts hs
  have hcop : Nat.Coprime (Nat.gcd (batchProduct (p * r) ts) (p * r)) r :=
    (hr.coprime_of_not_dvd
    (fun h => hnot (Nat.dvd_trans h (Nat.gcd_dvd_left _ _)))).symm
  exact Nat.dvd_antisymm
    (Nat.Coprime.dvd_of_dvd_mul_right hcop (Nat.gcd_dvd_right _ _))
    (Nat.dvd_gcd hprod hpdiv)

/-- Whole-product recovery is precisely the retained-leaf scan. -/
theorem flush_recover {n product : Nat} {buffer : Array (Nat × Nat)}
    (hg : Nat.gcd product n = n) :
    (flushBatch n product buffer).1 = (recover n buffer.toList).1 := by
  simp [flushBatch, flush, hg, recover]

end PMinusOne

end Nat

end Hex
