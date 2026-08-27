/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert
public import HexPrimality.MillerRabin
public import HexPrimality.Table
public import HexBasic.Rand
-- For the `#guard` regression block only.
meta import HexPrimality.Table
meta import HexPrimality.Cert
meta import HexPrimality.MillerRabin
meta import HexArith.Montgomery.Context
meta import HexBasic.Rand

public section

/-!
Untrusted factor search: the shared Brent-rho primitive and the internal
partial factorization behind certificate search.

`rhoFactor?` validates range and divisibility before returning, so its one
theorem (`rhoFactor?_spec`) is free of any claim about the search itself:
randomness and fuel affect only whether a factor is found, never what a
success means. The advanced `Rand` state rides in the failure so callers
resume rather than replay a failed stream. It is public because
hex-int-factor reuses this exact primitive; it does not certify that the
factor is prime and makes no completeness claim.

Each restart uses Brent's power-of-two anchor schedule, accumulates at most
32 differences per routine gcd, and replays a whole-modulus batch to recover
an individual divisor. Restart draws exclude degenerate polynomials and
fixed starting points before entering the bounded loop.

`partialFactor` is internal: trial division by the committed table, then
Brent rho over a worklist, with everything unsplittable multiplied into the
residual. Its one theorem is the product invariant its certificate-search
consumer needs; no primality and no completeness is claimed.
-/

namespace Hex

namespace Nat

/-- Why a proper-factor search stopped without a factor. -/
inductive RhoStop where
  /-- `n < 4`: no proper-factor search is meaningful. -/
  | invalidInput
  /-- The attempt budget ran out. Includes prime inputs and any composite
  for which no proper factor was found; makes no primality claim. -/
  | exhausted
deriving Repr, DecidableEq

/-- A resumable failure, following the tree's randomized-search convention:
the advanced state is returned even on failure, so callers can resume rather
than accidentally reuse the same failed stream. -/
structure RhoFailure where
  /-- Why the search stopped. -/
  stop : RhoStop
  /-- Restart attempts consumed by this failing search alone; callers
  running several searches accumulate their own totals. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- Polynomial step used by one rho restart. -/
private def rhoNext (n c y : Nat) : Nat := (y * y + c) % n

/-- Number of differences accumulated before a routine Brent gcd. -/
private def rhoBatchSize : Nat := 32

private structure BrentResult where
  /-- A candidate divisor found by this restart, if any. -/
  factor : Option Nat
  /-- Polynomial evaluations performed, including recovery replay. -/
  steps : Nat
  /-- Gcd computations performed, including recovery replay. -/
  gcds : Nat
  /-- Whole-modulus batches replayed by this terminating result. -/
  recoveries : Nat

/-- Mutable state of one Brent restart, grouped so call sites cannot silently
transpose the cycle and batch counters. The two small counters intentionally
travel through the production loop: conformance then observes the exact route
rather than a duplicated tracing implementation that can drift from it. -/
private structure BrentState where
  x : Nat
  y : Nat
  r : Nat
  k : Nat
  q : Nat
  batchStart : Nat
  batchCount : Nat
  steps : Nat
  gcds : Nat

private def brentStart (start : Nat) : BrentState :=
  { x := start, y := start, r := 1, k := 0, q := 1,
    batchStart := start, batchCount := 0, steps := 0, gcds := 0 }

/-- Replay one failed batch difference by difference when its accumulated gcd
is the whole modulus. The zero-fuel `none` result is unreachable from
`brentGo`: a whole-modulus product of batch differences guarantees that at
least one replayed difference has nontrivial gcd. -/
private def brentRecover (n c x : Nat) :
    Nat → Nat → Nat → Nat → BrentResult
  | 0, _, steps, gcds => ⟨none, steps, gcds, 1⟩
  | fuel + 1, y, steps, gcds =>
      let y' := rhoNext n c y
      let d := Nat.gcd ((x + n - y') % n) n
      if 1 < d then ⟨some d, steps + 1, gcds + 1, 1⟩
      else brentRecover n c x fuel y' (steps + 1) (gcds + 1)

/-- Brent cycle search inside one restart. Differences are multiplied modulo
`n` and share one gcd per batch. If a batch gcd is `n`, `brentRecover`
replays only that batch to recover the first nontrivial individual gcd. -/
private def brentGo (n c : Nat) : Nat → BrentState → BrentResult
  | 0, state => ⟨none, state.steps, state.gcds, 0⟩
  | fuel + 1, state =>
      let y' := rhoNext n c state.y
      let difference := (state.x + n - y') % n
      let q' := state.q * difference % n
      let k' := state.k + 1
      let batchCount' := state.batchCount + 1
      let cycleDone := state.r ≤ k'
      if rhoBatchSize ≤ batchCount' ∨ cycleDone then
        let d := Nat.gcd q' n
        if d = 1 then
          if cycleDone then
            brentGo n c fuel
              { x := y', y := y', r := state.r * 2,
                k := 0, q := 1, batchStart := y', batchCount := 0,
                steps := state.steps + 1, gcds := state.gcds + 1 }
          else
            brentGo n c fuel
              { x := state.x, y := y', r := state.r, k := k',
                q := 1, batchStart := y', batchCount := 0,
                steps := state.steps + 1, gcds := state.gcds + 1 }
        else if d < n then
          ⟨some d, state.steps + 1, state.gcds + 1, 0⟩
        else
          brentRecover n c state.x batchCount' state.batchStart
            (state.steps + 1) (state.gcds + 1)
      else
        brentGo n c fuel
          { x := state.x, y := y', r := state.r, k := k',
            q := q', batchStart := state.batchStart,
            batchCount := batchCount', steps := state.steps + 1,
            gcds := state.gcds }

/-- Inner iteration budget for one Brent restart: scaled past the expected
`n^(1/4)` cycle length for small `n`, capped at `2^22` so one restart is
bounded wall-clock at every input size. The cap still covers factors to
about `2^44`, past rho's documented remit of roughly `10^12`; beyond it
the honest outcome is a clean `exhausted`, not an inner loop whose budget
outlives the caller. Runtime only, so `Nat.sqrt` is fine here. -/
private def rhoInnerFuel (n : Nat) : Nat :=
  min (16 * (Nat.sqrt (Nat.sqrt n) + 2)) (1 <<< 22)

/-- One accepted restart draw together with its advanced random state. -/
private structure RhoDraw where
  /-- Nonzero, nondegenerate polynomial offset below `n`. -/
  c : Nat
  /-- Starting point below the modulus. -/
  start : Nat
  /-- State after all accepted and rejected pair draws. -/
  rand : Rand
  /-- Fixed-point pairs rejected before accepting this draw. -/
  rejections : Nat

private def rhoDrawGo (n : Nat) : Nat → Nat → Rand → RhoDraw
  | 0, rejections, r => ⟨1, 0, r, rejections⟩
  | fuel + 1, rejections, r =>
      let cDraw := r.next
      let startDraw := cDraw.2.next
      let c := cDraw.1.toNat % (n - 1) + 1
      let start := startDraw.1.toNat % n
      if c + 2 = n ∨ rhoNext n c start = start then
        rhoDrawGo n fuel (rejections + 1) startDraw.2
      else ⟨c, start, startDraw.2, rejections⟩

/-- Draw a nonzero polynomial offset, globally reject the degenerate
`x ↦ x² - 2`, and reject other draws only when the chosen start is a fixed
point. -/
private def rhoDraw (n : Nat) (r : Rand) : RhoDraw :=
  rhoDrawGo n 8 0 r

namespace Internal

/-- Shared maximum rho restart allocation for current worklist consumers. -/
def rhoRestartCap : Nat := 8

/-- A validated rho factor together with the exact number of restarts and
the generator state after those restarts. -/
structure RhoSuccess where
  /-- Dynamically validated proper factor. -/
  factor : Nat
  /-- Restarts executed, including the successful restart. -/
  attempts : Nat
  /-- Generator state after all restart draws. -/
  rand : Rand
deriving Repr

/-- Deterministic Brent instrumentation for route-level conformance tests. -/
structure RhoTrace where
  /-- Candidate divisor returned by the restart, if any. -/
  factor : Option Nat
  /-- Polynomial evaluations, including recovery replay. -/
  steps : Nat
  /-- Batched and recovery gcd computations. -/
  gcds : Nat
  /-- Whole-modulus batches replayed. -/
  recoveries : Nat

/-- Run one explicitly parameterized Brent restart and report its batching
counters. -/
def rhoTrace (n c start fuel : Nat) : RhoTrace :=
  let result := brentGo n c fuel (brentStart start)
  ⟨result.factor, result.steps, result.gcds, result.recoveries⟩

/-- Inspect the rejection count of the deterministic restart draw. -/
def rhoDrawTrace (n : Nat) (r : Rand) : Nat × Nat × Nat :=
  let draw := rhoDraw n r
  (draw.c, draw.start, draw.rejections)

end Internal

private def rhoTry (n : Nat) : Nat → Nat → Rand →
    Except RhoFailure Internal.RhoSuccess
  | 0, attempts, r => .error ⟨.exhausted, attempts, r⟩
  | tries + 1, attempts, r =>
      let draw := rhoDraw n r
      match (brentGo n draw.c (rhoInnerFuel n) (brentStart draw.start)).factor with
      | some d =>
          if 1 < d then
            if d < n then
              if n % d = 0 then .ok ⟨d, attempts + 1, draw.rand⟩
              else rhoTry n tries (attempts + 1) draw.rand
            else rhoTry n tries (attempts + 1) draw.rand
          else rhoTry n tries (attempts + 1) draw.rand
      | none => rhoTry n tries (attempts + 1) draw.rand

namespace Internal

/-- A dynamically validated proper-factor candidate by batched Brent rho,
with its exact restart count. -/
def rhoFactorCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure RhoSuccess :=
  if n < 4 then .error ⟨.invalidInput, 0, r⟩
  else if n % 2 = 0 then .ok ⟨2, 0, r⟩
  else rhoTry n fuel 0 r

end Internal

/-- A dynamically validated proper-factor candidate by batched Brent rho.
`fuel` bounds restart attempts. Each restart draws a fresh polynomial and
starting point, accumulates up to 32 differences per gcd, and replays a
whole-modulus batch difference by difference. Its cycle budget is scaled to
`n^(1/4)` and capped at `2^22` (see `rhoInnerFuel`), so exhaustion arrives
rather than hangs when the smallest factor is out of rho's reach. Every
success is validated (`1 < d < n` and `d ∣ n`) before it is returned, so
randomness and fuel affect only whether a factor is found. -/
def rhoFactor? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure (Nat × Rand) :=
  match Internal.rhoFactorCounted? n r fuel with
  | .error failure => .error failure
  | .ok success => .ok (success.factor, success.rand)

private theorem rhoTry_spec {n : Nat} :
    ∀ (tries attempts : Nat) (r : Rand) {success : Internal.RhoSuccess},
      rhoTry n tries attempts r = .ok success →
        1 < success.factor ∧ success.factor < n ∧ success.factor ∣ n := by
  intro tries
  induction tries with
  | zero =>
      intro attempts r success h
      simp [rhoTry] at h
  | succ tries ih =>
      intro attempts r success h
      unfold rhoTry at h
      dsimp only at h
      split at h
      · split at h
        · split at h
          · split at h
            · rename_i dd h1 h2 h3
              injection h with h
              subst h
              exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3⟩
            · exact ih _ _ h
          · exact ih _ _ h
        · exact ih _ _ h
      · exact ih _ _ h

/-- A counted rho success is a validated proper factor. -/
theorem Internal.rhoFactorCounted?_spec {n : Nat} {r : Rand} {fuel : Nat}
    {success : Internal.RhoSuccess}
    (h : Internal.rhoFactorCounted? n r fuel = .ok success) :
    1 < success.factor ∧ success.factor < n ∧ success.factor ∣ n := by
  unfold Internal.rhoFactorCounted? at h
  by_cases h4 : n < 4
  · rw [if_pos h4] at h
    cases h
  · rw [if_neg h4] at h
    by_cases heven : n % 2 = 0
    · rw [if_pos heven] at h
      injection h with h
      cases h
      change 1 < 2 ∧ 2 < n ∧ 2 ∣ n
      exact ⟨by omega, by omega, Nat.dvd_of_mod_eq_zero heven⟩
    · rw [if_neg heven] at h
      exact rhoTry_spec fuel 0 r h

/-- The one theorem about the rho primitive: a success is a validated
proper factor. -/
theorem rhoFactor?_spec {n d : Nat} {r r' : Rand} {fuel : Nat}
    (h : rhoFactor? n r fuel = .ok (d, r')) : 1 < d ∧ d < n ∧ d ∣ n := by
  unfold rhoFactor? at h
  split at h
  · cases h
  · rename_i success hsuccess
    injection h with h
    injection h with hd hr
    subst hd
    exact Internal.rhoFactorCounted?_spec hsuccess

/-! The internal partial factorization. -/

/-- Candidate partial factorization: bases with positive exponents, and an
unfactored residual. No primality and no completeness is claimed. -/
structure PartialFactors where
  /-- Claimed factor bases with exponents. -/
  factors : List (Nat × Nat)
  /-- The unfactored remainder. -/
  residual : Nat
deriving Repr

/-- The product `∏ pᵢ ^ eᵢ` of a claimed factor list. -/
private def prodPows : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: rest => p ^ e * prodPows rest

private def listProd : List Nat → Nat
  | [] => 1
  | m :: rest => m * listProd rest

/-- Divide out factors of `p` from `m`: the exponent found within fuel and
the cofactor. -/
private def divOut (p : Nat) : Nat → Nat → Nat × Nat
  | 0, m => (0, m)
  | fuel + 1, m =>
      if 1 < p ∧ m % p = 0 then
        ((divOut p fuel (m / p)).1 + 1, (divOut p fuel (m / p)).2)
      else (0, m)

private theorem divOut_prod (p : Nat) :
    ∀ (fuel m : Nat), p ^ (divOut p fuel m).1 * (divOut p fuel m).2 = m := by
  intro fuel
  induction fuel with
  | zero =>
      intro m
      simp [divOut]
  | succ fuel ih =>
      intro m
      unfold divOut
      by_cases hc : 1 < p ∧ m % p = 0
      · rw [if_pos hc]
        dsimp only
        rw [Nat.pow_succ, Nat.mul_right_comm, ih (m / p)]
        exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc.2)
      · rw [if_neg hc]
        simp

/-- Trial division over the committed table entries. -/
private def trialGo : List Nat → List (Nat × Nat) → Nat →
    List (Nat × Nat) × Nat
  | [], acc, m => (acc, m)
  | p :: ps, acc, m =>
      if 1 < p ∧ m % p = 0 then
        trialGo ps ((p, (divOut p (m.log2 + 1) m).1) :: acc)
          (divOut p (m.log2 + 1) m).2
      else trialGo ps acc m

private theorem trialGo_prod :
    ∀ (ps : List Nat) (acc : List (Nat × Nat)) (m : Nat),
      prodPows (trialGo ps acc m).1 * (trialGo ps acc m).2 =
        prodPows acc * m := by
  intro ps
  induction ps with
  | nil =>
      intro acc m
      rfl
  | cons p rest ih =>
      intro acc m
      unfold trialGo
      by_cases hc : 1 < p ∧ m % p = 0
      · rw [if_pos hc, ih]
        simp only [prodPows]
        rw [Nat.mul_right_comm, divOut_prod, Nat.mul_comm]
      · rw [if_neg hc]
        exact ih acc m

/-- Merge one prime occurrence into a claimed factor list. -/
private def insertFactor (p : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(p, 1)]
  | (q, e) :: rest =>
      if q = p then (q, e + 1) :: rest else (q, e) :: insertFactor p rest

private theorem insertFactor_prod (p : Nat) :
    ∀ (l : List (Nat × Nat)),
      prodPows (insertFactor p l) = p * prodPows l := by
  intro l
  induction l with
  | nil =>
      simp [insertFactor, prodPows]
  | cons a rest ih =>
      obtain ⟨q, e⟩ := a
      unfold insertFactor
      by_cases hq : q = p
      · rw [if_pos hq]
        subst hq
        simp only [prodPows, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm]
      · rw [if_neg hq]
        simp only [prodPows, ih]
        simp [Nat.mul_left_comm]

/-- Restart budget for each rho call inside the worklist. -/
private def rhoRestartBudget : Nat := Internal.rhoRestartCap

/-- Internal partial-factor worklist result with exact randomized work. -/
private structure RhoPhaseResult where
  factors : List (Nat × Nat)
  residual : Nat
  rand : Rand
  attempts : Nat

/-- The rho worklist: pop a pending number, drop it if it is `1`, keep it
as a claimed factor if the filter calls it prime, split it if rho finds a
factor, and multiply it into the residual otherwise. Fuel exhaustion dumps
the remaining stack into the residual, preserving the product exactly. -/
private def rhoPhase :
    Nat → List Nat → List (Nat × Nat) → Nat → Rand → Nat → RhoPhaseResult
  | 0, stack, acc, residual, r, attempts =>
      ⟨acc, listProd stack * residual, r, attempts⟩
  | _ + 1, [], acc, residual, r, attempts => ⟨acc, residual, r, attempts⟩
  | fuel + 1, m :: stack, acc, residual, r, attempts =>
      if m = 1 then rhoPhase fuel stack acc residual r attempts
      else if isProbablePrime m then
        rhoPhase fuel stack (insertFactor m acc) residual r attempts
      else
        match Internal.rhoFactorCounted? m r rhoRestartBudget with
        | .ok success =>
            rhoPhase fuel (success.factor :: m / success.factor :: stack) acc
              residual success.rand (attempts + success.attempts)
        | .error f =>
            rhoPhase fuel stack acc (residual * m) f.rand (attempts + f.attempts)

private theorem rhoPhase_prod :
    ∀ (fuel : Nat) (stack : List Nat) (acc : List (Nat × Nat))
      (residual : Nat) (r : Rand),
      ∀ attempts : Nat,
      prodPows (rhoPhase fuel stack acc residual r attempts).factors *
          (rhoPhase fuel stack acc residual r attempts).residual =
        prodPows acc * listProd stack * residual := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack acc residual r attempts
      simp only [rhoPhase]
      rw [Nat.mul_assoc]
  | succ fuel ih =>
      intro stack acc residual r attempts
      match stack with
      | [] =>
          simp [rhoPhase, listProd]
      | m :: stack =>
          unfold rhoPhase
          by_cases h1 : m = 1
          · rw [if_pos h1, ih]
            subst h1
            simp [listProd]
          · rw [if_neg h1]
            by_cases hp : isProbablePrime m
            · rw [if_pos hp, ih, insertFactor_prod]
              simp only [listProd]
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            · rw [if_neg hp]
              split
              · rename_i success hok
                rw [ih]
                obtain ⟨hd1, hdlt, hddvd⟩ :=
                  Internal.rhoFactorCounted?_spec hok
                have hdm : success.factor *
                    (m / success.factor * listProd stack) =
                    m * listProd stack := by
                  rw [← Nat.mul_assoc, Nat.mul_div_cancel' hddvd]
                simp only [listProd]
                rw [hdm]
              · rw [ih]
                simp only [listProd]
                simp [Nat.mul_assoc, Nat.mul_comm]

/-- Internal partial factorization and the search work that produced it. -/
private structure PartialSearch where
  raw : PartialFactors
  rand : Rand
  attempts : Nat

/-- Trial division by the committed table, then Brent rho over a worklist,
with `fuel` bounding the worklist steps. Everything the search cannot split
multiplies into the residual. Internal; certificate search is the only
consumer, and hex-int-factor builds its own assembly over the counted rho
adapter. -/
private def partialFactor (n : Nat) (r : Rand) (fuel : Nat) :
    PartialSearch :=
  let trial := trialGo primeTable.toList [] n
  let phase := rhoPhase fuel [trial.2] trial.1 1 r 0
  ⟨⟨phase.factors, phase.residual⟩, phase.rand, phase.attempts⟩

/-- The product invariant: the claimed powers times the residual recover the
input exactly. This is the one fact certificate search needs. -/
private theorem partialFactor_prod (n : Nat) (r : Rand) (fuel : Nat) :
    prodPows (partialFactor n r fuel).raw.factors *
      (partialFactor n r fuel).raw.residual = n := by
  unfold partialFactor
  dsimp only
  rw [rhoPhase_prod]
  simp only [listProd]
  rw [Nat.mul_one, Nat.mul_one]
  simpa [prodPows] using trialGo_prod primeTable.toList [] n

/-! Regression coverage: the rho primitive on every result shape, and the
partial factorization's product invariant exercised at runtime. -/

#guard (match rhoFactor? 3 (Rand.ofSeed 1) 4 with
        | .error f => f.stop == .invalidInput
        | _ => false)
#guard (match rhoFactor? 8 (Rand.ofSeed 1) 4 with
        | .ok (d, _) => d == 2
        | _ => false)
#guard (match rhoFactor? 91 (Rand.ofSeed 1) 16 with
        | .ok (d, _) => decide (1 < d) && decide (d < 91) && 91 % d == 0
        | _ => false)
#guard (match rhoFactor? 101 (Rand.ofSeed 1) 4 with  -- prime input
        | .error f => f.stop == .exhausted
        | _ => false)
set_option maxRecDepth 10000 in  -- table walks inside partialFactor
#guard (let pf := (partialFactor 720 (Rand.ofSeed 1) 32).raw
        pf.factors.foldl (fun a x => a * x.1 ^ x.2) 1 * pf.residual == 720)
set_option maxRecDepth 10000 in
#guard (let pf := (partialFactor (97 * 101 * 101) (Rand.ofSeed 2) 32).raw
        pf.factors.foldl (fun a x => a * x.1 ^ x.2) 1 * pf.residual ==
          97 * 101 * 101)

/-! Certificate search and the decision API. -/

/-- Why certificate search stopped without a certificate. -/
inductive PrimeCertStop where
  /-- The input is provably composite (trial, table completeness, or a
  Miller-Rabin witness); the failure is a verdict. -/
  | composite
  /-- The search budget ran out; no primality claim either way. -/
  | exhausted
deriving Repr, DecidableEq

/-- A resumable certificate-search failure. -/
structure PrimeCertFailure where
  /-- Why the search stopped. -/
  stop : PrimeCertStop
  /-- Randomized attempts consumed by the complete invocation, including
  successful subsearches completed before this failure. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- A resumable bounded-decision failure. -/
structure PrimeDecisionFailure where
  /-- Attempts consumed by the complete certificate invocation (see
  `PrimeCertFailure.attempts`). -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- A resumable next-prime-search failure. -/
structure NextPrimeFailure where
  /-- Candidates conclusively rejected before the failure; the candidate
  whose decision failed is not counted. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- Default fuel for the bounded decision path: recursion depth scales with
the bit length. A starting point, to be revisited by the bench. -/
def defaultPrimeFuel (n : Nat) : Nat := 2 * n.log2 + 16

/-- A private non-dependent counted result. Public counted shapes remain
specialized so their factor and indexed-certificate fields have stable names. -/
private structure Counted (α : Type) where
  value : α
  attempts : Nat
  rand : Rand

/-- Witness-search budget per factor entry. -/
private def witnessBudget : Nat := 32

/-- Search a base for one factor entry, checking with the same compiled
`checkWitness` the certificate checker replays. -/
private def witnessGo (n q : Nat) :
    Nat → Nat → Rand → Except PrimeCertFailure (Counted Nat)
  | 0, attempts, r => .error ⟨.exhausted, attempts, r⟩
  | t + 1, attempts, r =>
      if checkWitness n q (r.next.1.toNat % (n - 3) + 2) then
        .ok ⟨r.next.1.toNat % (n - 3) + 2, attempts + 1, r.next.2⟩
      else witnessGo n q t (attempts + 1) r.next.2

/-- Assemble the cube-root node for the factored part `F`: the cofactor
decomposition `R = 2Fs + r` and the square-root witness for the
discriminant. Runtime only, so `Nat.sqrt` is fine here (it never enters a
proof term); the public wrapper's `checkPrime` validation decides
acceptance. -/
private def mkPock3 (n F : Nat) (entries : List (Nat × Nat × PrimeCert)) :
    PrimeCert :=
  .pock3 n ((n - 1) / F % (2 * F)) ((n - 1) / F / (2 * F))
    (Nat.sqrt ((n - 1) / F % (2 * F) * ((n - 1) / F % (2 * F)) -
      8 * ((n - 1) / F / (2 * F))))
    entries

mutual

/-- One level of certificate search: verdict tiers first (size, table with
its completeness, a Miller-Rabin witness scan), then `n - 1` is partially
factored and every claimed prime-power entry becomes a certified child with
a searched witness. The assembled node is validated by the public wrapper,
never trusted from here. -/
private def primeCertGo (fuel n : Nat) (r : Rand) :
    Except PrimeCertFailure (Counted PrimeCert) :=
  match fuel with
  | 0 => .error ⟨.exhausted, 0, r⟩
  | fuel + 1 =>
      if n < 2 then .error ⟨.composite, 0, r⟩
      else if n < primeTableBound then
        if isTablePrime n then .ok ⟨.small n, 0, r⟩
        else .error ⟨.composite, 0, r⟩
      else
        match defaultBases.find? (fun a => !(millerRabin n a)) with
        | some _ => .error ⟨.composite, 0, r⟩
        | none =>
            let factored := partialFactor (n - 1) r (2 * n.log2 + 8)
            match assembleGo fuel n factored.raw.factors [] factored.attempts
                factored.rand with
            | .error f => .error f
            | .ok assembled =>
                match certProduct (n - 1) assembled.value with
                | none => .error ⟨.exhausted, assembled.attempts, assembled.rand⟩
                | some F =>
                    if n < F * F then
                      .ok ⟨.pock n assembled.value, assembled.attempts,
                        assembled.rand⟩
                    else .ok ⟨mkPock3 n F assembled.value, assembled.attempts,
                      assembled.rand⟩
termination_by (fuel, 0)

/-- Certify every claimed factor entry: a recursive child certificate and a
witness base per entry. A child failure is reported as exhaustion: the
child's compositeness would only mean the untrusted factorization guessed
wrong, never that `n` is composite. -/
private def assembleGo (fuel n : Nat) :
    List (Nat × Nat) → List (Nat × Nat × PrimeCert) → Nat → Rand →
      Except PrimeCertFailure (Counted (List (Nat × Nat × PrimeCert)))
  | [], acc, attempts, r => .ok ⟨acc.reverse, attempts, r⟩
  | (q, e) :: rest, acc, attempts, r =>
      if e = 0 then assembleGo fuel n rest acc attempts r
      else
        match primeCertGo fuel q r with
        | .error f => .error ⟨.exhausted, attempts + f.attempts, f.rand⟩
        | .ok child =>
            match witnessGo n q witnessBudget 0 child.rand with
            | .error f =>
                .error ⟨f.stop, attempts + child.attempts + f.attempts, f.rand⟩
            | .ok witness =>
                assembleGo fuel n rest
                  ((witness.value, e - 1, child.value) :: acc)
                  (attempts + child.attempts + witness.attempts) witness.rand
termination_by l => (fuel, l.length + 1)

end

namespace Internal

/-- A checked primality certificate together with the exact number of
randomized rho restarts and witness candidates used to construct it. -/
structure PrimeCertSuccess (n : Nat) where
  /-- Kernel-replayable checked certificate. -/
  cert : CheckedPrimeCert n
  /-- Randomized attempts used throughout the recursive construction. -/
  attempts : Nat
  /-- Generator state after those attempts. -/
  rand : Rand

/-- Bounded certificate search retaining exact successful-attempt metering. -/
def primeCertCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (PrimeCertSuccess n) :=
  match primeCertGo fuel n r with
  | .error f => .error f
  | .ok result =>
      if hs : result.value.subject = n then
        if hv : checkPrime result.value = true then
          .ok ⟨⟨result.value, hs, hv⟩, result.attempts, result.rand⟩
        else .error ⟨.exhausted, result.attempts, result.rand⟩
      else .error ⟨.exhausted, result.attempts, result.rand⟩

end Internal

/-- Bounded certificate search. A success is a `CheckedPrimeCert`, so a
certificate for one number can never answer a request about another; a
`.composite` failure is a verdict (see `primeCert?_composite`); an
`.exhausted` failure makes no claim and carries the advanced state. -/
def primeCert? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (CheckedPrimeCert n × Rand) :=
  match Internal.primeCertCounted? n r fuel with
  | .error failure => .error failure
  | .ok success => .ok (success.cert, success.rand)

private theorem witnessGo_error_stop {n q : Nat} :
    ∀ (t attempts : Nat) (r : Rand) {f : PrimeCertFailure},
      witnessGo n q t attempts r = .error f → f.stop = .exhausted := by
  intro t
  induction t with
  | zero =>
      intro attempts r f h
      injection h with h
      subst h
      rfl
  | succ t ih =>
      intro attempts r f h
      unfold witnessGo at h
      split at h
      · cases h
      · exact ih _ _ h

private theorem assembleGo_error_stop {fuel n : Nat} :
    ∀ (l : List (Nat × Nat)) (acc : List (Nat × Nat × PrimeCert))
      (attempts : Nat) (r : Rand) {f : PrimeCertFailure},
      assembleGo fuel n l acc attempts r = .error f → f.stop = .exhausted := by
  intro l
  induction l with
  | nil =>
      intro acc attempts r f h
      simp [assembleGo] at h
  | cons a rest ih =>
      intro acc attempts r f h
      obtain ⟨q, e⟩ := a
      unfold assembleGo at h
      split at h
      · exact ih _ _ _ h
      · split at h
        · injection h with h
          subst h
          rfl
        · split at h
          next f' hwit =>
            have hfstop := witnessGo_error_stop _ _ _ hwit
            injection h with h
            cases h
            exact hfstop
          next => exact ih _ _ _ h

private theorem primeCertGo_composite {fuel n : Nat} {r : Rand}
    {f : PrimeCertFailure} (h : primeCertGo fuel n r = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  match fuel with
  | 0 =>
      unfold primeCertGo at h
      injection h with h
      subst h
      cases hstop
  | fuel + 1 =>
      unfold primeCertGo at h
      by_cases h2 : n < 2
      · rw [if_pos h2] at h
        intro hp
        have := hp.two_le
        omega
      · rw [if_neg h2] at h
        by_cases htab : n < primeTableBound
        · rw [if_pos htab] at h
          by_cases hhit : isTablePrime n = true
          · rw [if_pos hhit] at h
            cases h
          · rw [if_neg hhit] at h
            intro hp
            exact hhit (isTablePrime_iff.mpr (mem_primeTable_of_prime hp htab))
        · rw [if_neg htab] at h
          split at h
          · rename_i a hfind
            intro hp
            have := List.find?_some hfind
            rw [Bool.not_eq_true'] at this
            exact absurd (millerRabin_eq_true_of_prime hp) (by
              rw [this]
              exact Bool.false_ne_true)
          · dsimp only at h
            split at h
            · rename_i f' herr
              injection h with h
              subst h
              rw [assembleGo_error_stop _ _ _ _ herr] at hstop
              cases hstop
            · split at h
              · injection h with h
                subst h
                cases hstop
              · split at h <;> cases h

/-- A counted `.composite` failure is a verdict: the input is not prime. -/
theorem Internal.primeCertCounted?_composite {n : Nat} {r : Rand} {fuel : Nat}
    {f : PrimeCertFailure}
    (hresult : Internal.primeCertCounted? n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  unfold Internal.primeCertCounted? at hresult
  split at hresult
  · rename_i f' herr
    injection hresult with h
    subst h
    exact primeCertGo_composite herr hstop
  · split at hresult
    · split at hresult
      · cases hresult
      · injection hresult with h
        subst h
        cases hstop
    · injection hresult with h
      subst h
      cases hstop

/-- A `.composite` failure is a verdict: the input is not prime. Justified
by size, table completeness, or a failed Miller-Rabin base; never by
anything the untrusted search merely failed to do. -/
theorem primeCert?_composite {n : Nat} {r : Rand} {fuel : Nat}
    {f : PrimeCertFailure} (hresult : primeCert? n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  unfold primeCert? at hresult
  split at hresult
  · rename_i f' herr
    injection hresult with h
    subst h
    exact Internal.primeCertCounted?_composite herr hstop
  · cases hresult

/-- After Miller--Rabin filtering, exact trial division handles inputs from
`primeTableBound` to `6000000`. This round boundary lies between the measured
Cunningham-chain rungs where trial last wins (near `5 · 10^6`) and certificate
search first wins (near `6 · 10^6`). -/
def isPrimeTrialThreshold : Nat := 6000000

/-- The bounded decision: table below `primeTableBound`, Miller--Rabin
composite filtering, exact trial division below `isPrimeTrialThreshold`, then
certificate search. A failed base or a table/trial miss returns a certified
`false`; an accepted certificate returns `true`; an exhausted search is an
error rather than an unbounded computation. -/
def isPrime? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeDecisionFailure (Bool × Rand) :=
  if n < primeTableBound then .ok (isTablePrime n, r)
  else if n < isPrimeTrialThreshold then
    match defaultBases.find? (fun a => !(millerRabin n a)) with
    | some _ => .ok (false, r)
    | none => .ok (isPrimeTrial n, r)
  else
    match primeCert? n r fuel with
    | .ok (_, r') => .ok (true, r')
    | .error f =>
        match f.stop with
        | .composite => .ok (false, f.rand)
        | .exhausted => .error ⟨f.attempts, f.rand⟩

/-- Every successful bounded decision is exact. -/
theorem isPrime?_spec {n : Nat} {r : Rand} {fuel : Nat} {b : Bool}
    {r' : Rand} (h : isPrime? n r fuel = .ok (b, r')) :
    b = true ↔ Prime n := by
  unfold isPrime? at h
  by_cases ht : n < primeTableBound
  · rw [if_pos ht] at h
    injection h with h
    injection h with hb hr
    subst hb
    constructor
    · intro hb'
      exact mem_primeTable_prime (isTablePrime_iff.mp hb')
    · intro hp
      exact isTablePrime_iff.mpr (mem_primeTable_of_prime hp ht)
  · rw [if_neg ht] at h
    by_cases htrial : n < isPrimeTrialThreshold
    · rw [if_pos htrial] at h
      split at h
      · rename_i a hfind
        have ha : millerRabin n a = false := by
          have hnot := List.find?_some hfind
          simpa using hnot
        injection h with h
        injection h with hb hr
        subst hb
        constructor
        · intro hfalse
          cases hfalse
        · exact fun hp => absurd hp (not_prime_of_millerRabin_false ha)
      · injection h with h
        injection h with hb hr
        subst hb
        exact ⟨isPrimeTrial_isPrime, isPrimeTrial_of_prime⟩
    · rw [if_neg htrial] at h
      split at h
      · rename_i cert r2 hok
        injection h with h
        injection h with hb hr
        subst hb
        exact ⟨fun _ => cert.prime, fun _ => rfl⟩
      · rename_i f herr
        split at h
        · rename_i hstop
          injection h with h
          injection h with hb hr
          subst hb
          constructor
          · intro hfalse
            cases hfalse
          · intro hp
            exact absurd hp (primeCert?_composite herr hstop)
        · cases h

/-- The pure total convenience decision: the bounded path from the
reproducible seed, with exact trial division as the fallback if that path
exhausts its fuel, which is what makes the iff unconditional. Callers that
need a real time bound and resumable state use `isPrime?`. -/
def isPrime (n : Nat) : Bool :=
  match isPrime? n (Rand.ofSeed n) (defaultPrimeFuel n) with
  | .ok (b, _) => b
  | .error _ => isPrimeTrial n

/-- The total decision is exact. -/
theorem isPrime_iff {n : Nat} : isPrime n = true ↔ Prime n := by
  unfold isPrime
  split
  · rename_i b r' hok
    exact isPrime?_spec hok
  · exact ⟨isPrimeTrial_isPrime, isPrimeTrial_of_prime⟩

private def nextPrimeGo (certFuel : Nat) :
    Nat → Nat → Nat → Rand → Except NextPrimeFailure (Nat × Rand)
  | 0, _, attempts, r => .error ⟨attempts, r⟩
  | steps + 1, m, attempts, r =>
      match isPrime? m r certFuel with
      | .error f => .error ⟨attempts, f.rand⟩
      | .ok (true, r') => .ok (m, r')
      | .ok (false, r') => nextPrimeGo certFuel steps (m + 1) (attempts + 1) r'

private theorem nextPrimeGo_spec (certFuel : Nat) :
    ∀ (steps m attempts : Nat) (r : Rand) {p : Nat} {r' : Rand},
      nextPrimeGo certFuel steps m attempts r = .ok (p, r') →
      m ≤ p ∧ Prime p ∧ ∀ q, m ≤ q → q < p → ¬ Prime q := by
  intro steps
  induction steps with
  | zero =>
      intro m attempts r p r' h
      simp [nextPrimeGo] at h
  | succ steps ih =>
      intro m attempts r p r' h
      unfold nextPrimeGo at h
      split at h
      · cases h
      · -- the candidate is prime: it is the answer
        rename_i r2 heq
        injection h with h
        injection h with hp hr
        subst hp
        refine ⟨Nat.le_refl _, (isPrime?_spec heq).mp rfl, ?_⟩
        intro q hq1 hq2
        omega
      · -- the candidate is certified composite: extend the window
        rename_i r2 heq
        obtain ⟨hle, hprime, hmin⟩ := ih _ _ _ h
        refine ⟨by omega, hprime, ?_⟩
        intro q hq1 hq2
        rcases Nat.eq_or_lt_of_le hq1 with rfl | hlt
        · intro hp'
          have hb := (isPrime?_spec heq).mpr hp'
          cases hb
        · exact hmin q (by omega) hq2

/-- Fuel-bounded least-prime-above search: a total form needs Euclid's
theorem, which this tree does not carry Mathlib-free, so exhaustion is
reported with the attempt count and advanced state. -/
def nextPrime? (n : Nat) (r : Rand) (fuel : Nat) :
    Except NextPrimeFailure (Nat × Rand) :=
  nextPrimeGo fuel fuel (n + 1) 0 r

/-- A successful search returns the least prime above `n`. -/
theorem nextPrime?_spec {n : Nat} {r : Rand} {fuel : Nat} {p : Nat}
    {r' : Rand} (h : nextPrime? n r fuel = .ok (p, r')) :
    n < p ∧ Prime p ∧ ∀ q, n < q → q < p → ¬ Prime q := by
  obtain ⟨hle, hprime, hmin⟩ := nextPrimeGo_spec fuel fuel (n + 1) 0 r h
  exact ⟨by omega, hprime, fun q h1 h2 => hmin q (by omega) h2⟩

/-! Regression coverage: the decision surface across the table, trial, and
certificate tiers, and the next-prime search. `2^31 - 1` exercises the
certificate tier with a fully table-factorable `n - 1`, so the path is
deterministic. -/

#guard isPrime 0 = false
#guard isPrime 1 = false
#guard isPrime 2 = true
#guard isPrime 9973 = true
#guard isPrime 99991 = true          -- table tier
#guard isPrime 100003 = true         -- trial tier
#guard isPrime 10000019 = true       -- certificate tier
#guard isPrime 2147483647 = true     -- certificate tier (Mersenne 2^31 - 1)
#guard isPrime 2147483649 = false    -- certificate tier, MR verdict
#guard (match nextPrime? 90 (Rand.ofSeed 0) 8 with
        | .ok (p, _) => p == 97
        | .error _ => false)
#guard (match primeCert? 2147483647 (Rand.ofSeed 0) 8 with
        | .ok (c, _) => checkPrime c.raw
        | .error _ => false)
set_option maxRecDepth 10000 in
#guard checkPrime (mkPock3 199 6 [(3, 0, .small 2), (2, 0, .small 3)])

end Nat

end Hex
