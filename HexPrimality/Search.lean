/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert
public import HexPrimality.MillerRabin
public import HexPrimality.PMinusOne
public import HexPrimality.Table
public import HexBasic.Rand
-- For the `#guard` regression block only.
meta import HexPrimality.Table
meta import HexPrimality.Cert
meta import HexPrimality.MillerRabin
meta import HexPrimality.PMinusOne
meta import HexArith.Montgomery.Context
meta import HexBasic.Rand

public section

/-!
Untrusted factor search: the shared stage-1 primitives and the internal
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

`partialFactor` is internal: trial division by the committed table, one
counted deterministic Pollard `p - 1` stage-1 call, then Brent rho over a
worklist, with everything unsplittable multiplied into the residual. Its one
theorem is the product invariant its certificate-search consumer needs; no
primality and no completeness is claimed.
-/

namespace Hex

namespace Nat

/-- Why a proper-factor search stopped without a factor. -/
inductive RhoStop where
  /-- `n < 4`: no proper-factor search is meaningful. -/
  | invalidInput
  /-- A bounded search resource ran out: the restart allocation, a restart's
  bounded sampler or pair-draw allocation, or its Brent cycle budget. Includes
  prime inputs and composites for which no proper factor was found; makes no
  primality claim. -/
  | exhausted
deriving Repr, DecidableEq

/-- A resumable failure, following the tree's randomized-search convention:
the advanced state is returned even on failure, so callers can resume rather
than accidentally reuse the same failed stream. -/
structure RhoFailure where
  /-- Why the search stopped. -/
  stop : RhoStop
  /-- Restart attempts consumed by this failing search alone; callers
  running several searches accumulate their own totals. A draw that exhausts
  its bounded sampler or pair-draw allocation counts as the one restart it was
  trying to construct. -/
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

/-- Absolute Brent cycle-step cap for one restart. It covers factors to about
`2^44`, past rho's documented remit of roughly `10^12`. -/
private def rhoInnerFuelCap : Nat := 1 <<< 22

/-- Inner iteration budget for one Brent restart: scaled past the expected
`n^(1/4)` cycle length for small `n`, capped so one restart is bounded
wall-clock at every input size. Beyond the cap the honest outcome is a clean
`exhausted`, not an inner loop whose budget outlives the caller. Runtime only,
so `Nat.sqrt` is fine here. -/
private def rhoInnerFuel (n : Nat) : Nat :=
  min (16 * (Nat.sqrt (Nat.sqrt n) + 2)) rhoInnerFuelCap

/-- One accepted restart draw together with its advanced random state. -/
private structure RhoDraw where
  /-- Nonzero, nondegenerate polynomial offset below `n`. -/
  c : Nat
  /-- Starting point below the modulus. -/
  start : Nat
  /-- State after all accepted, sampler-rejected, and pair-rejected draws. -/
  rand : Rand
  /-- Fixed-point pairs rejected before accepting this draw. -/
  rejections : Nat

namespace Internal

/-- Why construction of one rho restart draw stopped. -/
inductive RhoDrawStop where
  /-- One coordinate's bounded natural-number sampler exhausted. -/
  | sample (error : RandError)
  /-- Every admitted pair draw was fixed-point or globally degenerate. -/
  | pairs
deriving Repr

/-- Bounded retries for one rejection-sampled natural number. -/
def sampleFuel : Nat := 64

/-- Bounded pair draws within one semantic rho restart. -/
def rhoPairFuel : Nat := 8

end Internal

private structure RhoDrawFailure where
  /-- Which bounded draw resource exhausted. -/
  stop : Internal.RhoDrawStop
  /-- State after every bounded-sampler and pair-rejection draw. -/
  rand : Rand
  /-- Fixed-point or degenerate pair draws rejected before exhaustion. -/
  rejections : Nat

private def randErrorState (initial : Rand) : RandError → Rand
  | .zeroBound => initial
  | .exhausted _ r => r

private def rhoDrawGo (n drawFuel : Nat) :
    Nat → Nat → Rand → Except RhoDrawFailure RhoDraw
  | 0, rejections, r => .error ⟨.pairs, r, rejections⟩
  | fuel + 1, rejections, r =>
      match r.nat (n - 1) drawFuel with
      | .error e => .error ⟨.sample e, randErrorState r e, rejections⟩
      | .ok cDraw =>
          match cDraw.2.nat n drawFuel with
          | .error e =>
              .error ⟨.sample e, randErrorState cDraw.2 e, rejections⟩
          | .ok startDraw =>
              let c := cDraw.1 + 1
              let start := startDraw.1
              if c + 2 = n ∨ rhoNext n c start = start then
                rhoDrawGo n drawFuel fuel (rejections + 1) startDraw.2
              else .ok ⟨c, start, startDraw.2, rejections⟩

/-- Draw a nonzero polynomial offset, globally reject the degenerate
`x ↦ x² - 2`, and reject other draws only when the chosen start is a fixed
point. -/
private def rhoDraw (n : Nat) (r : Rand) : Except RhoDrawFailure RhoDraw :=
  rhoDrawGo n Internal.sampleFuel Internal.rhoPairFuel 0 r

namespace Internal

/-- Shared maximum rho restart allocation for current worklist consumers. -/
def rhoRestartCap : Nat := 8

/-- Effective Brent cycle budget for each restart: the caller's allocation
capped by the input-scaled production budget. -/
def rhoRestartFuel (n innerFuel : Nat) : Nat :=
  min (rhoInnerFuel n) innerFuel

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

/-- Inspect an exact bounded restart draw. The error distinguishes sampler and
pair-draw exhaustion and carries the pair-rejection count and exact state;
sampler-internal rejections do not increment that count. -/
def rhoDrawTrace (n : Nat) (r : Rand) (drawFuel : Nat := sampleFuel)
    (pairFuel : Nat := rhoPairFuel) :
    Except (RhoDrawStop × Nat × Rand) (Nat × Nat × Nat × Rand) :=
  match rhoDrawGo n drawFuel pairFuel 0 r with
  | .error failure => .error (failure.stop, failure.rejections, failure.rand)
  | .ok draw => .ok (draw.c, draw.start, draw.rejections, draw.rand)

end Internal

private def rhoTry (n innerFuel : Nat) : Nat → Nat → Rand →
    Except RhoFailure Internal.RhoSuccess
  | 0, attempts, r => .error ⟨.exhausted, attempts, r⟩
  | tries + 1, attempts, r =>
      match rhoDraw n r with
      | .error failure =>
          rhoTry n innerFuel tries (attempts + 1) failure.rand
      | .ok draw =>
          match (brentGo n draw.c innerFuel (brentStart draw.start)).factor with
          | some d =>
              if 1 < d then
                if d < n then
                  if n % d = 0 then .ok ⟨d, attempts + 1, draw.rand⟩
                  else rhoTry n innerFuel tries (attempts + 1) draw.rand
                else rhoTry n innerFuel tries (attempts + 1) draw.rand
              else rhoTry n innerFuel tries (attempts + 1) draw.rand
          | none => rhoTry n innerFuel tries (attempts + 1) draw.rand

namespace Internal

/-- A dynamically validated proper-factor candidate by batched Brent rho,
with its exact restart count. -/
def rhoFactorCountedWith? (n : Nat) (r : Rand) (restarts innerFuel : Nat) :
    Except RhoFailure RhoSuccess :=
  if n < 4 then .error ⟨.invalidInput, 0, r⟩
  else if n % 2 = 0 then .ok ⟨2, 0, r⟩
  else
    let restartFuel := rhoRestartFuel n innerFuel
    rhoTry n restartFuel restarts 0 r

/-- A counted rho search with the production per-restart cycle budget. -/
def rhoFactorCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure RhoSuccess :=
  rhoFactorCountedWith? n r fuel rhoInnerFuelCap

end Internal

/-- A dynamically validated proper-factor candidate by batched Brent rho.
`fuel` bounds restart attempts. Each restart draws a fresh polynomial and
starting point through bounded unbiased sampling, accumulates up to 32
differences per gcd, and replays a
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

private theorem rhoTry_spec {n innerFuel : Nat} :
    ∀ (tries attempts : Nat) (r : Rand) {success : Internal.RhoSuccess},
      rhoTry n innerFuel tries attempts r = .ok success →
        1 < success.factor ∧ success.factor < n ∧ success.factor ∣ n := by
  intro tries
  induction tries with
  | zero =>
      intro attempts r success h
      simp [rhoTry] at h
  | succ tries ih =>
      intro attempts r success h
      unfold rhoTry at h
      split at h
      · exact ih _ _ h
      · split at h
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

/-- A rho success under explicit restart and cycle budgets is a validated
proper factor. -/
theorem Internal.rhoFactorCountedWith?_spec {n : Nat} {r : Rand}
    {restarts innerFuel : Nat}
    {success : Internal.RhoSuccess}
    (h : Internal.rhoFactorCountedWith? n r restarts innerFuel = .ok success) :
    1 < success.factor ∧ success.factor < n ∧ success.factor ∣ n := by
  unfold Internal.rhoFactorCountedWith? at h
  by_cases h4 : n < 4
  · rw [ite_eq_left h4] at h
    cases h
  · rw [ite_eq_right h4] at h
    by_cases heven : n % 2 = 0
    · rw [ite_eq_left heven] at h
      injection h with h
      cases h
      change 1 < 2 ∧ 2 < n ∧ 2 ∣ n
      exact ⟨by omega, by omega, Nat.dvd_of_mod_eq_zero heven⟩
    · rw [ite_eq_right heven] at h
      exact rhoTry_spec restarts 0 r h

/-- A counted rho success is a validated proper factor. -/
theorem Internal.rhoFactorCounted?_spec {n : Nat} {r : Rand} {fuel : Nat}
    {success : Internal.RhoSuccess}
    (h : Internal.rhoFactorCounted? n r fuel = .ok success) :
    1 < success.factor ∧ success.factor < n ∧ success.factor ∣ n := by
  exact Internal.rhoFactorCountedWith?_spec h

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

/-- Output of an untrusted partial-factor search used during certificate
construction. The caller validates only the final `PrimeCert`; these fields
carry search candidates and resumable resource accounting, not evidence. -/
structure FactorSearchResult where
  /-- Claimed factors and the unfactored residual. -/
  raw : PartialFactors
  /-- Generator state after every randomized attempt made by the search. -/
  rand : Rand
  /-- Semantic search attempts made by this invocation. -/
  attempts : Nat
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
        let divided := divOut p fuel (m / p)
        (divided.1 + 1, divided.2)
      else (0, m)

namespace Internal

/-- Exercise one trial-division extraction directly. Used by conformance to
guard the high-valuation route independently of the full prime-table walk. -/
def trialExtractTrace (p m : Nat) : Nat × Nat :=
  divOut p (m.log2 + 1) m

end Internal

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
      · rw [ite_eq_left hc]
        dsimp only
        rw [Nat.pow_succ, Nat.mul_right_comm, ih (m / p)]
        exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc.2)
      · rw [ite_eq_right hc]
        simp

/-- Trial division over the committed table entries. -/
private def trialGo : List Nat → List (Nat × Nat) → Nat →
    List (Nat × Nat) × Nat
  | [], acc, m => (acc, m)
  | p :: ps, acc, m =>
      if 1 < p ∧ m % p = 0 then
        let divided := divOut p (m.log2 + 1) m
        trialGo ps ((p, divided.1) :: acc) divided.2
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
      · rw [ite_eq_left hc, ih]
        simp only [prodPows]
        rw [Nat.mul_right_comm, divOut_prod, Nat.mul_comm]
      · rw [ite_eq_right hc]
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
      · rw [ite_eq_left hq]
        subst hq
        simp only [prodPows, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm]
      · rw [ite_eq_right hq]
        simp only [prodPows, ih]
        simp [Nat.mul_left_comm]

/-- The certificate path spends at most one cheap stage-1 call per partial
factorization, after table division and before rho. -/
private def pMinusOneBase : Nat := 2
private def pMinusOneBound : Nat := 64

private structure PMinusOnePhase where
  factors : List (Nat × Nat)
  stack : List Nat
  rand : Rand
  attempts : Nat

/-- Try the shared deterministic stage-1 primitive once on a composite table
cofactor. Zero worklist fuel skips the call. Trivial cofactors go to the rho
worklist, while probable primes enter the factor list directly so rho does not
repeat the same screen. Every actual call is charged once through the shared
counted boundary, while its random state is unchanged. Both failure outcomes
retain the original cofactor unsplit. -/
private def pMinusOnePhase (acc : List (Nat × Nat)) (m : Nat) (r : Rand) :
    Nat → PMinusOnePhase
  | 0 => ⟨acc, [m], r, 0⟩
  | _ + 1 =>
      if m < 4 then ⟨acc, [m], r, 0⟩
      else if isProbablePrime m then ⟨insertFactor m acc, [], r, 0⟩
      else
        let attempt := pMinusOneStage1Counted m pMinusOneBase
          pMinusOneBound r
        match attempt.result with
        | .factor d =>
            ⟨acc, [d, m / d], attempt.rand, attempt.attempts⟩
        | .noFactor | .whole =>
            ⟨acc, [m], attempt.rand, attempt.attempts⟩

private theorem pMinusOnePhase_prod (acc : List (Nat × Nat)) (m : Nat)
    (r : Rand) (fuel : Nat) :
    prodPows (pMinusOnePhase acc m r fuel).factors *
        listProd (pMinusOnePhase acc m r fuel).stack =
      prodPows acc * m := by
  cases fuel with
  | zero => simp [pMinusOnePhase, listProd]
  | succ fuel =>
      simp only [pMinusOnePhase]
      by_cases hsmall : m < 4
      · rw [ite_eq_left hsmall]
        simp [listProd]
      · rw [ite_eq_right hsmall]
        by_cases hprime : isProbablePrime m
        · rw [ite_eq_left hprime, insertFactor_prod]
          simp [listProd, Nat.mul_comm]
        · rw [ite_eq_right hprime]
          split
          · rename_i d hfactor
            have hproper : 1 < d ∧ d < m ∧ d ∣ m := by
              exact pMinusOneStage1Counted_spec hfactor
            simp only [listProd]
            rw [Nat.mul_one, Nat.mul_div_cancel' hproper.2.2]
          · simp [listProd]
          · simp [listProd]

/-- Restart budget for each rho call inside the worklist. -/
private def rhoRestartBudget : Nat := Internal.rhoRestartCap

/-- Pollard-rho work admitted at each partial-factor worklist entry during
certificate search. This controls search resources only; every reported
factor is still validated dynamically and every emitted certificate is
checker-replayed. -/
structure PrimeCertBudget where
  /-- Maximum Brent restarts at one worklist entry. -/
  rhoRestarts : Nat
  /-- Maximum Brent cycle steps per restart. -/
  rhoSteps : Nat
deriving Repr, DecidableEq

/-- Complete resource allocation for one untrusted partial-factor invocation.
Nested primality checks receive `primeFuel` and `primeBudget`; the producer's
own worklist receives `factorFuel`. -/
structure FactorSearchBudget where
  /-- Rho allocation available to each nested primality-certificate search. -/
  primeBudget : PrimeCertBudget
  /-- Attempt budget available to each nested primality-certificate search. -/
  primeFuel : Nat
  /-- Worklist-entry budget available to the partial-factor producer. -/
  factorFuel : Nat
deriving Repr, DecidableEq

/-- A bounded, resumable, untrusted partial-factor producer. -/
abbrev FactorSearch := FactorSearchBudget → Nat → Rand → FactorSearchResult

/-- The production certificate-search rho allocation used by the public API. -/
def defaultPrimeCertBudget : PrimeCertBudget :=
  ⟨rhoRestartBudget, 1 <<< 22⟩

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
private def rhoPhase (budget : PrimeCertBudget) :
    Nat → List Nat → List (Nat × Nat) → Nat → Rand → Nat → RhoPhaseResult
  | 0, stack, acc, residual, r, attempts =>
      ⟨acc, listProd stack * residual, r, attempts⟩
  | _ + 1, [], acc, residual, r, attempts => ⟨acc, residual, r, attempts⟩
  | fuel + 1, m :: stack, acc, residual, r, attempts =>
      if m = 1 then rhoPhase budget fuel stack acc residual r attempts
      else if isProbablePrime m then
        rhoPhase budget fuel stack (insertFactor m acc) residual r attempts
      else
        match Internal.rhoFactorCountedWith? m r budget.rhoRestarts
            budget.rhoSteps with
        | .ok success =>
            rhoPhase budget fuel
              (success.factor :: m / success.factor :: stack) acc residual
              success.rand (attempts + success.attempts)
        | .error f =>
            rhoPhase budget fuel stack acc (residual * m) f.rand
              (attempts + f.attempts)

private theorem rhoPhase_prod :
    ∀ (budget : PrimeCertBudget) (fuel : Nat) (stack : List Nat)
      (acc : List (Nat × Nat))
      (residual : Nat) (r : Rand),
      ∀ attempts : Nat,
      prodPows (rhoPhase budget fuel stack acc residual r attempts).factors *
          (rhoPhase budget fuel stack acc residual r attempts).residual =
        prodPows acc * listProd stack * residual := by
  intro budget
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
          · rw [ite_eq_left h1, ih]
            subst h1
            simp [listProd]
          · rw [ite_eq_right h1]
            by_cases hp : isProbablePrime m
            · rw [ite_eq_left hp, ih, insertFactor_prod]
              simp only [listProd]
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            · rw [ite_eq_right hp]
              split
              · rename_i success hok
                rw [ih]
                obtain ⟨hd1, hdlt, hddvd⟩ :=
                  Internal.rhoFactorCountedWith?_spec hok
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

/-- Trial division by the committed table, one base-2 stage-1 attempt at bound
64 when fuel is positive and the cofactor is composite, then Brent rho over a
worklist, with `fuel` bounding the worklist steps. Everything the search cannot
split multiplies into the residual. Internal; certificate search is the only
consumer, and hex-int-factor builds its own assembly over the counted search
adapters. -/
private def partialFactor (budget : PrimeCertBudget) (n : Nat) (r : Rand)
    (fuel : Nat) :
    PartialSearch :=
  let trial := trialGo primeTable.toList [] n
  let smooth := pMinusOnePhase trial.1 trial.2 r fuel
  let phase := rhoPhase budget fuel smooth.stack smooth.factors 1 smooth.rand
    smooth.attempts
  ⟨⟨phase.factors, phase.residual⟩, phase.rand, phase.attempts⟩

/-- The built-in partial-factor producer used by `primeCert?`. -/
def defaultFactorSearch : FactorSearch :=
  fun allocation n r =>
    let result := partialFactor allocation.primeBudget n r allocation.factorFuel
    ⟨result.raw, result.rand, result.attempts⟩

/-- The product invariant: the claimed powers times the residual recover the
input exactly. This is the one fact certificate search needs. -/
private theorem partialFactor_prod (budget : PrimeCertBudget) (n : Nat)
    (r : Rand) (fuel : Nat) :
    prodPows (partialFactor budget n r fuel).raw.factors *
      (partialFactor budget n r fuel).raw.residual = n := by
  unfold partialFactor
  dsimp only
  rw [rhoPhase_prod]
  rw [pMinusOnePhase_prod]
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
#guard (let pf := (partialFactor defaultPrimeCertBudget 720 (Rand.ofSeed 1) 32).raw
        pf.factors.foldl (fun a x => a * x.1 ^ x.2) 1 * pf.residual == 720)
set_option maxRecDepth 10000 in
#guard (let pf := (partialFactor defaultPrimeCertBudget (97 * 101 * 101)
    (Rand.ofSeed 2) 32).raw
        pf.factors.foldl (fun a x => a * x.1 ^ x.2) 1 * pf.residual ==
          97 * 101 * 101)

-- With rho disabled, the bounded p−1 phase splits this table-coprime
-- cofactor into probable-prime worklist entries. The deterministic call is
-- charged once and leaves the generator unchanged.
private def pMinusOnePartial : PartialSearch :=
  partialFactor ⟨0, 0⟩ (100549 * 100049) (Rand.ofSeed 17) 8

#guard pMinusOnePartial.raw.residual == 1
#guard pMinusOnePartial.attempts == 1
#guard pMinusOnePartial.rand == Rand.ofSeed 17

-- Gcd one and whole-modulus outcomes both fall through to the bounded rho
-- worklist; with zero rho restarts they retain the original cofactor unsplit.
private def pMinusOneMissPartial : PartialSearch :=
  partialFactor ⟨0, 0⟩ (100049 * 100057) (Rand.ofSeed 18) 4
private def pMinusOneWholePartial : PartialSearch :=
  partialFactor ⟨0, 0⟩ (100549 * 100801) (Rand.ofSeed 19) 4

#guard pMinusOneMissPartial.raw.residual == 100049 * 100057
#guard pMinusOneMissPartial.attempts == 1
#guard pMinusOneMissPartial.rand == Rand.ofSeed 18
#guard pMinusOneWholePartial.raw.residual == 100549 * 100801
#guard pMinusOneWholePartial.attempts == 1
#guard pMinusOneWholePartial.rand == Rand.ofSeed 19

/-! Certificate search and the decision API. -/

/-- Why certificate search stopped without a certificate. -/
inductive PrimeCertStop where
  /-- The input is provably composite (the size check, table completeness, or
  a Miller-Rabin witness); the failure is a verdict. -/
  | composite
  /-- The search budget ran out; no primality claim either way. -/
  | exhausted
deriving Repr, DecidableEq

/-- A resumable certificate-search failure. -/
structure PrimeCertFailure where
  /-- Why the search stopped. -/
  stop : PrimeCertStop
  /-- Search attempts consumed by the complete invocation, including
  deterministic p−1 calls and successful subsearches completed before this
  failure. -/
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
  /-- Candidates conclusively rejected as composite before exhaustion. An
  undecided candidate is not counted. -/
  rejectedCandidates : Nat
  /-- Certificate-search attempts consumed by the undecided candidate,
  including deterministic p−1 calls. Table lookup, trial division, and
  Miller--Rabin work are not counted. -/
  certAttempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- Default fuel for the bounded decision path: one certificate-construction
level per input bit. Above the deterministic tiers, every recursive child that
reaches construction is an odd factor from the product decomposition of
`n - 1`; its complementary factor is at least two, so its bit length is
strictly smaller. The complete table closes inputs below 17 bits without
construction, leaving 16 spare units in this bound. This is not a claim that
bounded factor or witness search finds every available certificate. -/
def defaultPrimeFuel (n : Nat) : Nat := n.log2 + 1

/-- A private non-dependent counted result. Public counted shapes remain
specialized so their factor and indexed-certificate fields have stable names. -/
private structure Counted (α : Type) where
  value : α
  attempts : Nat
  rand : Rand

/-- Witness-search budget per factor entry. -/
private def witnessBudget : Nat := 32

/-- Draw one certificate witness base from the full interval `[2, n - 2]`.
The bounded sampler may consume several words and rejected candidates while
remaining one semantic witness attempt. -/
private def witnessDraw (n : Nat) (r : Rand) (fuel : Nat) :
    Except RandError (Nat × Rand) :=
  match r.nat (n - 3) fuel with
  | .error e => .error e
  | .ok draw => .ok (draw.1 + 2, draw.2)

namespace Internal

/-- Inspect one bounded witness-base draw, including its exact advanced state. -/
def witnessDrawTrace (n : Nat) (r : Rand) (drawFuel : Nat := sampleFuel) :
    Except RandError (Nat × Rand) :=
  witnessDraw n r drawFuel

end Internal

/-- Search a base for one factor entry, checking with the same compiled
`checkWitness` the certificate checker replays. Sampler-internal rejections
advance the state but remain within the one counted witness candidate; sampler
exhaustion counts the in-progress candidate and continues the next candidate
from that exact state. -/
private def witnessGo (n q drawFuel : Nat) :
    Nat → Nat → Rand → Except PrimeCertFailure (Counted Nat)
  | 0, attempts, r => .error ⟨.exhausted, attempts, r⟩
  | t + 1, attempts, r =>
      match witnessDraw n r drawFuel with
      | .error e =>
          witnessGo n q drawFuel t (attempts + 1) (randErrorState r e)
      | .ok draw =>
          if checkWitness n q draw.1 then
            .ok ⟨draw.1, attempts + 1, draw.2⟩
          else witnessGo n q drawFuel t (attempts + 1) draw.2

namespace Internal

/-- Inspect bounded witness search while retaining its exact candidate count
and final state. The optional sampler fuel is for route-level conformance. -/
def witnessSearchTrace (n q : Nat) (r : Rand) (candidates : Nat)
    (drawFuel : Nat := sampleFuel) :
    Except PrimeCertFailure (Nat × Nat × Rand) :=
  match witnessGo n q drawFuel candidates 0 r with
  | .error failure => .error failure
  | .ok success => .ok (success.value, success.attempts, success.rand)

end Internal

/-- Assemble the cube-root node for the factored part `F`: the cofactor
decomposition `R = 2Fs + r` and the square-root witness for the
discriminant. Runtime only, so `Nat.sqrt` is fine here (it never enters a
proof term); the public wrapper's `checkPrime` validation decides
acceptance. -/
private def mkPock3 (n F : Nat) (entries : List (Nat × Nat × PrimeCert)) :
    PrimeCert :=
  let cofactor := (n - 1) / F
  let window := 2 * F
  let r := cofactor % window
  let s := cofactor / window
  .pock3 n r s (Nat.sqrt (r * r - 8 * s)) entries

mutual

/-- One level of certificate search. Size, the complete table tier, and the
fixed Miller-Rabin witness scan run before fuel is inspected and leave attempts
and random state unchanged. A survivor consumes one recursion-depth unit to
begin construction; its children receive the predecessor, so table children
can still close at depth zero while children needing construction cannot.
Then `n - 1` is partially factored and every claimed prime-power entry becomes
a certified child with a searched witness. The candidate entries are sorted
into the checker's canonical subject order, then the assembled node is
validated by the public wrapper; neither the factorization nor this
preprocessing is trusted. -/
private def primeCertGo (factor : FactorSearch) (budget : PrimeCertBudget)
    (fuel n : Nat) (r : Rand) :
    Except PrimeCertFailure (Counted PrimeCert) :=
  if n < 2 then .error ⟨.composite, 0, r⟩
  else if n < primeTableBound then
    if isTablePrime n then .ok ⟨.small n, 0, r⟩
    else .error ⟨.composite, 0, r⟩
  else
    match defaultBases.find? (fun a => !(millerRabin n a)) with
    | some _ => .error ⟨.composite, 0, r⟩
    | none =>
        match fuel with
        | 0 => .error ⟨.exhausted, 0, r⟩
        | fuel + 1 =>
            let allocation : FactorSearchBudget :=
              ⟨budget, fuel, 2 * n.log2 + 8⟩
            let factored := factor allocation (n - 1) r
            match assembleGo factor budget fuel n factored.raw.factors []
                factored.attempts factored.rand with
            | .error f => .error f
            | .ok assembled =>
                let entries := assembled.value.mergeSort fun x y =>
                  x.2.2.subject ≤ y.2.2.subject
                match certProduct (n - 1) entries with
                | none => .error ⟨.exhausted, assembled.attempts, assembled.rand⟩
                | some F =>
                    if n < F * F then
                      .ok ⟨.pock n entries, assembled.attempts,
                        assembled.rand⟩
                    else .ok ⟨mkPock3 n F entries, assembled.attempts,
                      assembled.rand⟩
termination_by (fuel, 0)

/-- Certify every claimed factor entry: a recursive child certificate and a
witness base per entry. A child failure is reported as exhaustion: the
child's compositeness would only mean the untrusted factorization guessed
wrong, never that `n` is composite. -/
private def assembleGo (factor : FactorSearch) (budget : PrimeCertBudget)
    (fuel n : Nat) :
    List (Nat × Nat) → List (Nat × Nat × PrimeCert) → Nat → Rand →
      Except PrimeCertFailure (Counted (List (Nat × Nat × PrimeCert)))
  | [], acc, attempts, r => .ok ⟨acc.reverse, attempts, r⟩
  | (q, e) :: rest, acc, attempts, r =>
      if e = 0 then assembleGo factor budget fuel n rest acc attempts r
      else
        match primeCertGo factor budget fuel q r with
        | .error f => .error ⟨.exhausted, attempts + f.attempts, f.rand⟩
        | .ok child =>
            match witnessGo n q Internal.sampleFuel witnessBudget 0 child.rand with
            | .error f =>
                .error ⟨f.stop, attempts + child.attempts + f.attempts, f.rand⟩
            | .ok witness =>
                assembleGo factor budget fuel n rest
                  ((witness.value, e - 1, child.value) :: acc)
                  (attempts + child.attempts + witness.attempts) witness.rand
termination_by l => (fuel, l.length + 1)

end

namespace Internal

/-- A checked primality certificate together with the exact number of p−1
calls, randomized rho restarts, and witness candidates used to construct it. -/
structure PrimeCertSuccess (n : Nat) where
  /-- Kernel-replayable checked certificate. -/
  cert : CheckedPrimeCert n
  /-- Search attempts used throughout the recursive construction. -/
  attempts : Nat
  /-- Generator state after those attempts. -/
  rand : Rand

/-- Bounded certificate search with an explicit rho allocation, retaining
exact successful-attempt metering. -/
def primeCertCountedUsing? (factor : FactorSearch) (budget : PrimeCertBudget)
    (n : Nat) (r : Rand)
    (fuel : Nat) :
    Except PrimeCertFailure (PrimeCertSuccess n) :=
  match primeCertGo factor budget fuel n r with
  | .error f => .error f
  | .ok result =>
      if hs : result.value.subject = n then
        if hv : checkPrime result.value = true then
          .ok ⟨⟨result.value, hs, hv⟩, result.attempts, result.rand⟩
        else .error ⟨.exhausted, result.attempts, result.rand⟩
      else .error ⟨.exhausted, result.attempts, result.rand⟩

/-- Bounded certificate search with an explicit rho allocation, retaining
exact successful-attempt metering and using the built-in factor producer. -/
def primeCertCountedWith? (budget : PrimeCertBudget) (n : Nat) (r : Rand)
    (fuel : Nat) :
    Except PrimeCertFailure (PrimeCertSuccess n) :=
  primeCertCountedUsing? defaultFactorSearch budget n r fuel

/-- Bounded certificate search retaining exact successful-attempt metering. -/
def primeCertCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (PrimeCertSuccess n) :=
  primeCertCountedWith? defaultPrimeCertBudget n r fuel

end Internal

/-- Bounded certificate search using an explicitly supplied, untrusted
partial-factor producer. Only the returned `CheckedPrimeCert` is accepted;
the producer's factors, accounting, and random state remain search data. -/
def primeCertWith? (factor : FactorSearch) (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (CheckedPrimeCert n × Rand) :=
  match Internal.primeCertCountedUsing? factor defaultPrimeCertBudget n r fuel with
  | .error failure => .error failure
  | .ok success => .ok (success.cert, success.rand)

/-- Bounded certificate search. A success is a `CheckedPrimeCert`, so a
certificate for one number can never answer a request about another; a
`.composite` failure is a verdict (see `primeCert?_composite`); an
`.exhausted` failure makes no claim and carries the advanced state. -/
def primeCert? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (CheckedPrimeCert n × Rand) :=
  match Internal.primeCertCounted? n r fuel with
  | .error failure => .error failure
  | .ok success => .ok (success.cert, success.rand)

private theorem witnessGo_error_stop {n q drawFuel : Nat} :
    ∀ (t attempts : Nat) (r : Rand) {f : PrimeCertFailure},
      witnessGo n q drawFuel t attempts r = .error f → f.stop = .exhausted := by
  intro t
  induction t with
  | zero =>
      intro attempts r f h
      injection h with h
      subst h
      rfl
  | succ t ih =>
      intro attempts r f h
      dsimp only [witnessGo] at h
      split at h
      · exact ih _ _ h
      · split at h
        · cases h
        · exact ih _ _ h

private theorem assembleGo_error_stop {factor : FactorSearch}
    {budget : PrimeCertBudget} {fuel n : Nat} :
    ∀ (l : List (Nat × Nat)) (acc : List (Nat × Nat × PrimeCert))
      (attempts : Nat) (r : Rand) {f : PrimeCertFailure},
      assembleGo factor budget fuel n l acc attempts r = .error f →
        f.stop = .exhausted := by
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

private theorem primeCertGo_composite {factor : FactorSearch}
    {budget : PrimeCertBudget} {fuel n : Nat}
    {r : Rand} {f : PrimeCertFailure}
    (h : primeCertGo factor budget fuel n r = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  unfold primeCertGo at h
  by_cases h2 : n < 2
  · rw [ite_eq_left h2] at h
    intro hp
    have := hp.two_le
    omega
  · rw [ite_eq_right h2] at h
    by_cases htab : n < primeTableBound
    · rw [ite_eq_left htab] at h
      by_cases hhit : isTablePrime n = true
      · rw [ite_eq_left hhit] at h
        cases h
      · rw [ite_eq_right hhit] at h
        intro hp
        exact hhit (isTablePrime_iff.mpr (mem_primeTable_of_prime hp htab))
    · rw [ite_eq_right htab] at h
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
        · injection h with h
          subst h
          cases hstop
        · split at h
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

/-- A counted `.composite` failure is a verdict for every factor producer and
resource allocation because only the fixed size, table, and Miller--Rabin tiers
can emit that stop reason. -/
theorem Internal.primeCertCountedUsing?_composite {factor : FactorSearch}
    {budget : PrimeCertBudget}
    {n : Nat} {r : Rand} {fuel : Nat}
    {f : PrimeCertFailure}
    (hresult : Internal.primeCertCountedUsing? factor budget n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  unfold Internal.primeCertCountedUsing? at hresult
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

/-- A budgeted counted `.composite` failure under the built-in factor producer
is a verdict. -/
theorem Internal.primeCertCountedWith?_composite {budget : PrimeCertBudget}
    {n : Nat} {r : Rand} {fuel : Nat}
    {f : PrimeCertFailure}
    (hresult : Internal.primeCertCountedWith? budget n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  unfold Internal.primeCertCountedWith? at hresult
  exact Internal.primeCertCountedUsing?_composite hresult hstop

/-- A counted `.composite` failure under the default allocation is a verdict:
the input is not prime. -/
theorem Internal.primeCertCounted?_composite {n : Nat} {r : Rand} {fuel : Nat}
    {f : PrimeCertFailure}
    (hresult : Internal.primeCertCounted? n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  exact Internal.primeCertCountedWith?_composite hresult hstop

/-- A `.composite` failure is a verdict for every supplied factor producer. -/
theorem primeCertWith?_composite {factor : FactorSearch} {n : Nat} {r : Rand}
    {fuel : Nat} {f : PrimeCertFailure}
    (hresult : primeCertWith? factor n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n := by
  unfold primeCertWith? at hresult
  split at hresult
  · rename_i f' herr
    injection hresult with h
    subst h
    exact Internal.primeCertCountedUsing?_composite herr hstop
  · cases hresult

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
  · rw [ite_eq_left ht] at h
    injection h with h
    injection h with hb hr
    subst hb
    constructor
    · intro hb'
      exact mem_primeTable_prime (isTablePrime_iff.mp hb')
    · intro hp
      exact isTablePrime_iff.mpr (mem_primeTable_of_prime hp ht)
  · rw [ite_eq_right ht] at h
    by_cases htrial : n < isPrimeTrialThreshold
    · rw [ite_eq_left htrial] at h
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
    · rw [ite_eq_right htrial] at h
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
  | 0, _, rejectedCandidates, r => .error ⟨rejectedCandidates, 0, r⟩
  | steps + 1, m, rejectedCandidates, r =>
      match isPrime? m r certFuel with
      | .error f => .error ⟨rejectedCandidates, f.attempts, f.rand⟩
      | .ok (true, r') => .ok (m, r')
      | .ok (false, r') =>
          nextPrimeGo certFuel steps (m + 1) (rejectedCandidates + 1) r'

private theorem nextPrimeGo_spec (certFuel : Nat) :
    ∀ (steps m rejectedCandidates : Nat) (r : Rand) {p : Nat} {r' : Rand},
      nextPrimeGo certFuel steps m rejectedCandidates r = .ok (p, r') →
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
reported with separate counts for conclusively rejected candidates and
certificate-search attempts, plus the exact advanced state. On
failure, `rejectedCandidates = fuel` means the candidate window was exhausted;
otherwise the undecided candidate is `n + 1 + rejectedCandidates`. -/
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
