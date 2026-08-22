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
  /-- How many restart attempts were consumed. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- Brent cycle search inside one restart: the anchor `x` is re-pinned to
the hare at each power-of-two step count. Returns the first nontrivial gcd
encountered (possibly `n` itself when the cycle closes without exposing a
factor; the caller validates). -/
private def brentGo (n c : Nat) : Nat → Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, x, y, r, k =>
      let y' := (y * y + c) % n
      let d := Nat.gcd ((x + n - y') % n) n
      if 1 < d then some d
      else if k + 1 < r then brentGo n c fuel x y' r (k + 1)
      else brentGo n c fuel y' y' (r * 2) 0

/-- Inner iteration budget for one Brent restart, scaled past the expected
`n^(1/4)` cycle length; restarts absorb the variance. Runtime only, so
`Nat.sqrt` is fine here. -/
private def rhoInnerFuel (n : Nat) : Nat :=
  16 * (Nat.sqrt (Nat.sqrt n) + 2)

/-- Draw the restart parameters: a polynomial offset in `[1, n - 3]`, a
starting point below `n`, and the advanced state. Search seeding, so the
slight modulo bias is irrelevant. -/
private def rhoDraw (n : Nat) (r : Rand) : Nat × Nat × Rand :=
  (r.next.1.toNat % (n - 3) + 1,
    r.next.2.next.1.toNat % n,
    r.next.2.next.2)

private def rhoTry (n : Nat) : Nat → Nat → Rand → Except RhoFailure (Nat × Rand)
  | 0, attempts, r => .error ⟨.exhausted, attempts, r⟩
  | tries + 1, attempts, r =>
      match brentGo n (rhoDraw n r).1 (rhoInnerFuel n) (rhoDraw n r).2.1
          (rhoDraw n r).2.1 1 0 with
      | some d =>
          if 1 < d then
            if d < n then
              if n % d = 0 then .ok (d, (rhoDraw n r).2.2)
              else rhoTry n tries (attempts + 1) (rhoDraw n r).2.2
            else rhoTry n tries (attempts + 1) (rhoDraw n r).2.2
          else rhoTry n tries (attempts + 1) (rhoDraw n r).2.2
      | none => rhoTry n tries (attempts + 1) (rhoDraw n r).2.2

/-- A dynamically validated proper-factor candidate by Brent rho. `fuel`
bounds the restart attempts; each restart draws a fresh polynomial offset
and starting point and runs a cycle budget scaled to `n^(1/4)`. Every
success is validated (`1 < d < n` and `d ∣ n`) before it is returned, so
randomness and fuel affect only whether a factor is found. -/
def rhoFactor? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure (Nat × Rand) :=
  if n < 4 then .error ⟨.invalidInput, 0, r⟩
  else if n % 2 = 0 then .ok (2, r)
  else rhoTry n fuel 0 r

private theorem rhoTry_spec {n : Nat} :
    ∀ (tries attempts : Nat) (r : Rand) {d : Nat} {r' : Rand},
      rhoTry n tries attempts r = .ok (d, r') → 1 < d ∧ d < n ∧ d ∣ n := by
  intro tries
  induction tries with
  | zero =>
      intro attempts r d r' h
      simp [rhoTry] at h
  | succ tries ih =>
      intro attempts r d r' h
      unfold rhoTry at h
      split at h
      · split at h
        · split at h
          · split at h
            · rename_i dd h1 h2 h3
              injection h with h
              injection h with hd hr
              subst hd
              exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3⟩
            · exact ih _ _ h
          · exact ih _ _ h
        · exact ih _ _ h
      · exact ih _ _ h

/-- The one theorem about the rho primitive: a success is a validated
proper factor. -/
theorem rhoFactor?_spec {n d : Nat} {r r' : Rand} {fuel : Nat}
    (h : rhoFactor? n r fuel = .ok (d, r')) : 1 < d ∧ d < n ∧ d ∣ n := by
  unfold rhoFactor? at h
  by_cases h4 : n < 4
  · rw [if_pos h4] at h
    cases h
  · rw [if_neg h4] at h
    by_cases heven : n % 2 = 0
    · rw [if_pos heven] at h
      injection h with h
      injection h with hd hr
      subst hd
      exact ⟨by omega, by omega, Nat.dvd_of_mod_eq_zero heven⟩
    · rw [if_neg heven] at h
      exact rhoTry_spec fuel 0 r h

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
private def rhoRestartBudget : Nat := 8

/-- The rho worklist: pop a pending number, drop it if it is `1`, keep it
as a claimed factor if the filter calls it prime, split it if rho finds a
factor, and multiply it into the residual otherwise. Fuel exhaustion dumps
the remaining stack into the residual, preserving the product exactly. -/
private def rhoPhase :
    Nat → List Nat → List (Nat × Nat) → Nat → Rand →
      (List (Nat × Nat) × Nat) × Rand
  | 0, stack, acc, residual, r => ((acc, listProd stack * residual), r)
  | _ + 1, [], acc, residual, r => ((acc, residual), r)
  | fuel + 1, m :: stack, acc, residual, r =>
      if m = 1 then rhoPhase fuel stack acc residual r
      else if isProbablePrime m then
        rhoPhase fuel stack (insertFactor m acc) residual r
      else
        match rhoFactor? m r rhoRestartBudget with
        | .ok (d, r') => rhoPhase fuel (d :: m / d :: stack) acc residual r'
        | .error f => rhoPhase fuel stack acc (residual * m) f.rand

private theorem rhoPhase_prod :
    ∀ (fuel : Nat) (stack : List Nat) (acc : List (Nat × Nat))
      (residual : Nat) (r : Rand),
      prodPows (rhoPhase fuel stack acc residual r).1.1 *
          (rhoPhase fuel stack acc residual r).1.2 =
        prodPows acc * listProd stack * residual := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack acc residual r
      simp only [rhoPhase]
      rw [Nat.mul_assoc]
  | succ fuel ih =>
      intro stack acc residual r
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
              · rename_i d r' hok
                rw [ih]
                obtain ⟨hd1, hdlt, hddvd⟩ := rhoFactor?_spec hok
                have hdm : d * (m / d * listProd stack) = m * listProd stack := by
                  rw [← Nat.mul_assoc, Nat.mul_div_cancel' hddvd]
                simp only [listProd]
                rw [hdm]
              · rw [ih]
                simp only [listProd]
                simp [Nat.mul_assoc, Nat.mul_comm]

/-- Trial division by the committed table, then Brent rho over a worklist,
with `fuel` bounding the worklist steps. Everything the search cannot split
multiplies into the residual. Internal; certificate search is the only
consumer, and hex-int-factor builds its own assembly over `rhoFactor?`. -/
private def partialFactor (n : Nat) (r : Rand) (fuel : Nat) :
    PartialFactors × Rand :=
  (⟨(rhoPhase fuel [(trialGo primeTable.toList [] n).2]
        (trialGo primeTable.toList [] n).1 1 r).1.1,
    (rhoPhase fuel [(trialGo primeTable.toList [] n).2]
        (trialGo primeTable.toList [] n).1 1 r).1.2⟩,
    (rhoPhase fuel [(trialGo primeTable.toList [] n).2]
        (trialGo primeTable.toList [] n).1 1 r).2)

/-- The product invariant: the claimed powers times the residual recover the
input exactly. This is the one fact certificate search needs. -/
private theorem partialFactor_prod (n : Nat) (r : Rand) (fuel : Nat) :
    prodPows (partialFactor n r fuel).1.factors *
      (partialFactor n r fuel).1.residual = n := by
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
#guard (let pf := (partialFactor 720 (Rand.ofSeed 1) 32).1
        pf.factors.foldl (fun a x => a * x.1 ^ x.2) 1 * pf.residual == 720)
set_option maxRecDepth 10000 in
#guard (let pf := (partialFactor (97 * 101 * 101) (Rand.ofSeed 2) 32).1
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
  /-- How many attempts were consumed. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- A resumable bounded-decision failure. -/
structure PrimeDecisionFailure where
  /-- How many attempts were consumed. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- A resumable next-prime-search failure. -/
structure NextPrimeFailure where
  /-- How many candidates were examined. -/
  attempts : Nat
  /-- The advanced generator state. -/
  rand : Rand
deriving Repr

/-- Default fuel for the bounded decision path: recursion depth scales with
the bit length. A starting point, to be revisited by the bench. -/
def defaultPrimeFuel (n : Nat) : Nat := 2 * n.log2 + 16

/-- Witness-search budget per factor entry. -/
private def witnessBudget : Nat := 32

/-- Search a base for one factor entry, checking with the same compiled
`checkWitness` the certificate checker replays. -/
private def witnessGo (n q : Nat) :
    Nat → Nat → Rand → Except PrimeCertFailure (Nat × Rand)
  | 0, attempts, r => .error ⟨.exhausted, attempts, r⟩
  | t + 1, attempts, r =>
      if checkWitness n q (r.next.1.toNat % (n - 3) + 2) then
        .ok (r.next.1.toNat % (n - 3) + 2, r.next.2)
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
    Except PrimeCertFailure (PrimeCert × Rand) :=
  match fuel with
  | 0 => .error ⟨.exhausted, 0, r⟩
  | fuel + 1 =>
      if n < 2 then .error ⟨.composite, 0, r⟩
      else if n < primeTableBound then
        if isTablePrime n then .ok (.small n, r)
        else .error ⟨.composite, 0, r⟩
      else
        match defaultBases.find? (fun a => !(millerRabin n a)) with
        | some _ => .error ⟨.composite, 0, r⟩
        | none =>
            match assembleGo fuel n
                (partialFactor (n - 1) r (2 * n.log2 + 8)).1.factors []
                (partialFactor (n - 1) r (2 * n.log2 + 8)).2 with
            | .error f => .error f
            | .ok (entries, r') =>
                match certProduct (n - 1) entries with
                | none => .error ⟨.exhausted, 0, r'⟩
                | some F =>
                    if n < F * F then .ok (.pock n entries, r')
                    else .ok (mkPock3 n F entries, r')
termination_by (fuel, 0)

/-- Certify every claimed factor entry: a recursive child certificate and a
witness base per entry. A child failure is reported as exhaustion: the
child's compositeness would only mean the untrusted factorization guessed
wrong, never that `n` is composite. -/
private def assembleGo (fuel n : Nat) :
    List (Nat × Nat) → List (Nat × Nat × PrimeCert) → Rand →
      Except PrimeCertFailure (List (Nat × Nat × PrimeCert) × Rand)
  | [], acc, r => .ok (acc.reverse, r)
  | (q, e) :: rest, acc, r =>
      if e = 0 then assembleGo fuel n rest acc r
      else
        match primeCertGo fuel q r with
        | .error f => .error ⟨.exhausted, f.attempts, f.rand⟩
        | .ok (cq, r1) =>
            match witnessGo n q witnessBudget 0 r1 with
            | .error f => .error f
            | .ok (a, r2) => assembleGo fuel n rest ((a, e - 1, cq) :: acc) r2
termination_by l => (fuel, l.length + 1)

end

/-- Bounded certificate search. A success is a `CheckedPrimeCert`, so a
certificate for one number can never answer a request about another; a
`.composite` failure is a verdict (see `primeCert?_composite`); an
`.exhausted` failure makes no claim and carries the advanced state. -/
def primeCert? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (CheckedPrimeCert n × Rand) :=
  match primeCertGo fuel n r with
  | .error f => .error f
  | .ok (c, r') =>
      if hs : c.subject = n then
        if hv : checkPrime c = true then .ok (⟨c, hs, hv⟩, r')
        else .error ⟨.exhausted, 0, r'⟩
      else .error ⟨.exhausted, 0, r'⟩

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
    ∀ (l : List (Nat × Nat)) (acc : List (Nat × Nat × PrimeCert)) (r : Rand)
      {f : PrimeCertFailure},
      assembleGo fuel n l acc r = .error f → f.stop = .exhausted := by
  intro l
  induction l with
  | nil =>
      intro acc r f h
      simp [assembleGo] at h
  | cons a rest ih =>
      intro acc r f h
      obtain ⟨q, e⟩ := a
      unfold assembleGo at h
      split at h
      · exact ih _ _ h
      · split at h
        · injection h with h
          subst h
          rfl
        · split at h
          next f' hwit =>
            injection h with h
            subst h
            exact witnessGo_error_stop _ _ _ hwit
          next => exact ih _ _ h

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
          · split at h
            · rename_i f' herr
              injection h with h
              subst h
              rw [assembleGo_error_stop _ _ _ herr] at hstop
              cases hstop
            · split at h
              · injection h with h
                subst h
                cases hstop
              · split at h <;> cases h

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

/-- Exact trial division handles everything below this; a placeholder until
the bench measures the crossover with the certificate path. -/
def isPrimeTrialThreshold : Nat := 100000000

/-- The bounded decision: table below `primeTableBound`, exact trial
division below `isPrimeTrialThreshold`, then certificate search. A failed
base or a table/trial miss returns a certified `false`; an accepted
certificate returns `true`; an exhausted search is an error rather than an
unbounded computation. -/
def isPrime? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeDecisionFailure (Bool × Rand) :=
  if n < primeTableBound then .ok (isTablePrime n, r)
  else if n < isPrimeTrialThreshold then .ok (isPrimeTrial n, r)
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
      injection h with h
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
#guard isPrime 10007 = true          -- trial tier
#guard isPrime 99999989 = true       -- just below the trial threshold
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
