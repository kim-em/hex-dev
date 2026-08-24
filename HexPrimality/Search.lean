/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.MillerRabin
public import HexPrimality.Table
public import HexBasic.Rand
-- For the `#guard` regression block only.
meta import HexPrimality.Table
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

/-- Inner iteration budget for one Brent restart: scaled past the expected
`n^(1/4)` cycle length for small `n`, capped at `2^22` so one restart is
bounded wall-clock at every input size. The cap still covers factors to
about `2^44`, past rho's documented remit of roughly `10^12`; beyond it
the honest outcome is a clean `exhausted`, not an inner loop whose budget
outlives the caller. Runtime only, so `Nat.sqrt` is fine here. -/
private def rhoInnerFuel (n : Nat) : Nat :=
  min (16 * (Nat.sqrt (Nat.sqrt n) + 2)) (1 <<< 22)

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
and starting point and runs a cycle budget scaled to `n^(1/4)` and capped
at `2^22` (see `rhoInnerFuel`), so exhaustion arrives rather than hangs
when the smallest factor is out of rho's reach. Every
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

end Nat

end Hex
