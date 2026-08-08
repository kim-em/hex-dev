/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.ModularPolynomial
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL
-- Kernel-reducible `Array`/`Vector` equality; see `HexBasic.ArrayDecEq`.
-- Drop once leanprover/lean4#14270 lands and the toolchain is bumped past it.
public import HexBasic.ArrayDecEq

public import HexBerlekampZassenhaus.BhksRecover
public meta import HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.FactorizationData
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.FactorizationResult
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section
set_option backward.proofsInPublic true

/-!
This module contains the small generic exhaustive search retained by the proof
substrate and the Hensel-precision schedule used by CLD recovery.  The public
classical engine lives under `Classical/`.
-/
namespace Hex

private def recombinationSearchAux
    (target : ZPoly) (localFactors : List ZPoly) : Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate := Array.polyProduct split.1.toArray
          match exactQuotient? target candidate with
          | none => none
          | some quotient =>
              match recombinationSearchAux quotient split.2 fuel with
              | none => none
              | some rest => some (candidate :: rest)

/--
Search for an integer-factor recombination of the lifted local factors.

The search enumerates subsets containing the first remaining local factor,
accepts a subset only when its product exactly divides the current target, and
then recurses on the quotient and unused local factors.
-/
def recombinationSearch (f : ZPoly) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchAux f localFactors (localFactors.length + 1)

/-- Fuelled auxiliary for `recombinationSearchMod`.  Recurses through
`subsetSplitsWithFirst localFactors`: at every level the head local factor is
forced into the candidate, the centred-lift result is normalised and checked
against `shouldRecordPolynomialFactor`, and a successful `exactQuotient?`
divides the search down to the remaining local factors and quotient. -/
@[expose]
def recombinationSearchModAux
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            normalizeFactorSign <|
              ZPoly.primitivePart <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
          if shouldRecordPolynomialFactor candidate then
            match exactQuotient? target candidate with
            | none => none
            | some quotient =>
                match recombinationSearchModAux quotient modulus split.2 fuel with
                | none => none
                | some rest => some (candidate :: rest)
          else
            none

/-- Exhaustive lifted-factor recombination search at a fixed modulus.  Drives
the slow path by iterating subsets of the lifted local factors through
`recombinationSearchModAux`. -/
def recombinationSearchMod
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchModAux f modulus localFactors (localFactors.length + 1)

/-- Exhaustive recombination of the lifted local factors stored in `d`, run at
the Hensel modulus `p^k = liftModulus d`.  Returns the recovered integer
factors as an array on success and `#[]` when the search fails. -/
def recombineExhaustive (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

/-- Size-`k` sublists of `xs`, each paired with its complement, order preserved
in both components. The size-class building block of the size-ordered classical
recombination search. -/
@[expose]
def subsetsOfSizeWithComplement {α : Type} : List α → Nat → List (List α × List α)
  | xs, 0 => [([], xs)]
  | [], _ + 1 => []
  | x :: xs, k + 1 =>
      (subsetsOfSizeWithComplement xs k).map (fun sc => (x :: sc.1, sc.2)) ++
      (subsetsOfSizeWithComplement xs (k + 1)).map (fun sc => (sc.1, x :: sc.2))

/-- Initial Hensel precision used by the fast BHKS doubling schedule. -/
def initialHenselPrecision (B : Nat) : Nat :=
  if B ≤ 4 then B else 4

/-- Successor precision used by the fast BHKS doubling schedule. -/
def nextHenselPrecision (k B : Nat) : Nat :=
  if 2 * k < B then
    2 * k
  else
    B

namespace ZPoly

/--
Build the fixed-precision Hensel lift data for the monic transform of an
square-free part. The exhaustive slow path still recombines against the original
primitive polynomial, but the lift stage sees the monic polynomial required by the
Hensel computation.
-/
@[expose]
def toMonicLiftData
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : LiftData :=
  henselLiftData (toMonic core).monic
    (precisionForCoeffBound B primeData.p) primeData

/--
Multiplicative inverse of `core`'s leading coefficient modulo `p ^ k`, read off
the integer Bezout certificate `s · ℓf + t · p^k = gcd(ℓf, p^k)`.  When
`gcd(leadingCoeff core, p ^ k) = 1` (the good-prime condition `p ∤ ℓf`) this is a
genuine inverse: `leadingCoeffInverse core p k * leadingCoeff core ≡ 1 (mod p^k)`
(`leadingCoeffInverse_mul_emod`).
-/
def leadingCoeffInverse (core : ZPoly) (p k : Nat) : Int :=
  (HexArith.Int.extGcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k))).2.1

/--
BHKS leading-coefficient-faithful monic target for `core`: rescale `core` by the
modular inverse of its leading coefficient, then reduce modulo `p ^ k`.

This is van Hoeij's `M1` normalisation (factor out `ℓf`, BHKS §2: `f = ℓf·f₁···fr`
with the `fᵢ` monic in `Z_p`), distinct from the `toMonic` `x ↦ x/ℓf` substitution
(`M2`).  Over `(ℤ/p^k)[x]` it equals `core · ℓf⁻¹`, so its monic local factors
divide `core` directly with no dilation.  It is monic over ℤ when
`gcd(leadingCoeff core, p ^ k) = 1` and `core` is nonconstant
(`monicTarget_monic`).
-/
@[expose]
def monicTarget (core : ZPoly) (p k : Nat) : ZPoly :=
  reduceModPow (DensePoly.scale (leadingCoeffInverse core p k) core) p k

/--
Fixed-precision Hensel lift data over `core`'s own coordinate (BHKS-faithful).

Mirrors `toMonicLiftData`, but lifts `core`'s monic modular factors against the
leading-coefficient-normalised `monicTarget` rather than the `x ↦ x/ℓf` dilation
`(toMonic core).monic`.  The lifted factors therefore divide `core` in
`(ℤ/p^a)[x]` directly, and the CLD lattice runs over `core`'s own coordinate.
-/
@[expose]
def directLiftData
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : LiftData :=
  henselLiftData (monicTarget core primeData.p (precisionForCoeffBound B primeData.p))
    (precisionForCoeffBound B primeData.p) primeData

/-- Abstract Bezout-to-residue step: if `A + t·P = 1` and `1 < P` then `A % P = 1`.
Used to read the unit residue `leadingCoeffInverse · ℓf ≡ 1 (mod p^k)` off the
integer extended-GCD certificate. -/
private theorem emod_eq_one_of_bezout {A t P : Int} (hP : 1 < P) (h : A + t * P = 1) :
    A % P = 1 := by
  have h2 : A = 1 + (-t) * P := by
    have hsub : A = 1 - t * P := by omega
    rw [hsub, Int.sub_eq_add_neg, Int.neg_mul]
  rw [h2, Int.add_mul_emod_self_right]
  exact Int.emod_eq_of_lt (by decide) hP

/-- The `leadingCoeffInverse` is a genuine inverse of `core`'s leading coefficient
modulo `p ^ k` when the leading coefficient is coprime to `p ^ k` (the good-prime
condition `p ∤ ℓf`).  This is the unit-residue fact the BHKS monic target rests on. -/
theorem leadingCoeffInverse_mul_emod (core : ZPoly) (p k : Nat)
    (hpk : 1 < p ^ k)
    (hgcd : Int.gcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1) :
    (leadingCoeffInverse core p k * DensePoly.leadingCoeff core)
        % Int.ofNat (p ^ k) = 1 := by
  unfold leadingCoeffInverse
  have hbez := HexArith.Int.extGcd_bezout_proj
    (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k))
  rw [HexArith.Int.extGcd_fst, hgcd] at hbez
  have hP : (1 : Int) < Int.ofNat (p ^ k) := by
    have h := Int.ofNat_lt.mpr hpk
    simpa using h
  exact emod_eq_one_of_bezout hP hbez

/-- Size of `reduceModPow` is bounded by the source size (trimming only drops
trailing zeros). -/
theorem reduceModPow_size_le (f : ZPoly) (p k : Nat) :
    (reduceModPow f p k).size ≤ f.size := by
  unfold reduceModPow
  refine Nat.le_trans (DensePoly.size_ofList_le _) ?_
  simp

/--
The direct-coordinate monic target has exactly the input polynomial's size.
Reduction cannot add coefficients, while coprimality makes its top coefficient
equal to one, so reduction cannot discard the input's top degree.
-/
theorem monicTarget_size_eq (core : ZPoly) (p k : Nat)
    (hpk : 1 < p ^ k)
    (hgcd : Int.gcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1)
    (hcore : 0 < core.size) :
    (monicTarget core p k).size = core.size := by
  have hpk_pos : 0 < p ^ k := by omega
  have hemod := leadingCoeffInverse_mul_emod core p k hpk hgcd
  have hs_ne : leadingCoeffInverse core p k ≠ 0 := by
    intro hzero
    rw [hzero, Int.zero_mul, Int.zero_emod] at hemod
    exact absurd hemod (by decide)
  have hscale_size :
      (DensePoly.scale (leadingCoeffInverse core p k) core).size = core.size :=
    scale_size_of_ne_zero _ core hs_ne
  have hscale_pos :
      0 < (DensePoly.scale (leadingCoeffInverse core p k) core).size := by
    rw [hscale_size]
    exact hcore
  have hg_top :
      (DensePoly.scale (leadingCoeffInverse core p k) core).coeff (core.size - 1)
        = leadingCoeffInverse core p k * DensePoly.leadingCoeff core := by
    have hlead :=
      leadingCoeff_scale_of_nonzero (leadingCoeffInverse core p k) core hs_ne
    rw [DensePoly.leadingCoeff_eq_coeff_last _ hscale_pos, hscale_size] at hlead
    exact hlead
  have htop : (monicTarget core p k).coeff (core.size - 1) = 1 := by
    unfold monicTarget
    rw [coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpk_pos, hg_top]
    exact hemod
  apply Nat.le_antisymm
  · unfold monicTarget
    exact Nat.le_trans (reduceModPow_size_le _ p k)
      (Nat.le_of_eq hscale_size)
  · rcases Nat.lt_or_ge (monicTarget core p k).size core.size with hlt | hge
    · have hle : (monicTarget core p k).size ≤ core.size - 1 := by omega
      have hzero :=
        DensePoly.coeff_eq_zero_of_size_le (monicTarget core p k) hle
      rw [htop] at hzero
      exact absurd hzero (by decide)
    · exact hge

/--
The BHKS leading-coefficient-faithful monic target is genuinely monic over ℤ when
`core`'s leading coefficient is coprime to `p ^ k` and `core` is nonconstant.

This is the load-bearing soundness fact for handling the existing monic Hensel lift
against `monicTarget` (van Hoeij `M1`) instead of the `toMonic` `x ↦ x/ℓf`
dilation (`M2`): the lift's producer lemma
`QuadraticMultifactorLiftInvariant_of_choosePrimeData` requires its target monic,
and `monicTarget` supplies that while keeping `core`'s own coordinate.
-/
theorem monicTarget_monic (core : ZPoly) (p k : Nat)
    (hpk : 1 < p ^ k)
    (hgcd : Int.gcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1)
    (hcore : 0 < core.size) :
    DensePoly.Monic (monicTarget core p k) := by
  have hpk_pos : 0 < p ^ k := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hpk)
  have hemod := leadingCoeffInverse_mul_emod core p k hpk hgcd
  have hs_ne : leadingCoeffInverse core p k ≠ 0 := by
    intro h0
    rw [h0, Int.zero_mul, Int.zero_emod] at hemod
    exact absurd hemod (by decide)
  have hscale_size :
      (DensePoly.scale (leadingCoeffInverse core p k) core).size = core.size :=
    scale_size_of_ne_zero _ core hs_ne
  have hscale_pos :
      0 < (DensePoly.scale (leadingCoeffInverse core p k) core).size := by
    rw [hscale_size]; exact hcore
  have hg_top :
      (DensePoly.scale (leadingCoeffInverse core p k) core).coeff (core.size - 1)
        = leadingCoeffInverse core p k * DensePoly.leadingCoeff core := by
    have h1 := leadingCoeff_scale_of_nonzero (leadingCoeffInverse core p k) core hs_ne
    rw [DensePoly.leadingCoeff_eq_coeff_last _ hscale_pos, hscale_size] at h1
    exact h1
  have htop : (monicTarget core p k).coeff (core.size - 1) = 1 := by
    unfold monicTarget
    rw [coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpk_pos, hg_top]
    exact hemod
  have hmt_le : (monicTarget core p k).size ≤ core.size := by
    unfold monicTarget
    exact Nat.le_trans (reduceModPow_size_le _ p k) (Nat.le_of_eq hscale_size)
  have hmt_ge : core.size ≤ (monicTarget core p k).size := by
    rcases Nat.lt_or_ge (monicTarget core p k).size core.size with hlt | hge
    · have hle : (monicTarget core p k).size ≤ core.size - 1 := by omega
      have hz := DensePoly.coeff_eq_zero_of_size_le (monicTarget core p k) hle
      rw [htop] at hz
      exact absurd hz (by decide)
    · exact hge
  have hsize : (monicTarget core p k).size = core.size := Nat.le_antisymm hmt_le hmt_ge
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _ (by rw [hsize]; exact hcore), hsize]
  exact htop

end ZPoly

/--
CLD column-adequacy floor for the fast recovery acceptance condition.

A successful BHKS recovery at schedule coefficient bound `k` only certifies
column adequacy (the BHKS Lemma 5.7 separation `hsep`) once the lift precision
`precisionForCoeffBound k primeData.p` clears the per-coordinate CLD threshold.
The lattice and its CLD columns are built directly over `core`, so the floor is
twice the largest per-coordinate bound of `core` itself.
-/
@[expose]
def cldCoeffFloor (core : ZPoly) : Nat :=
  let n := core.degree?.getD 0
  2 * (List.range (n + 1)).foldl
    (fun acc j => max acc (bhksCoeffBound core j)) 0

/-- Acceptance floor for the fast recovery loop: the CLD column-adequacy floor
`cldCoeffFloor` joined with the direct Mignotte recovery bound of `core`. -/
def bhksRecoveryFloor (core : ZPoly) : Nat :=
  max (cldCoeffFloor core) (ZPoly.defaultFactorCoeffBound core)

/-- The recovery floor is at least the logarithmic-derivative coefficient floor. -/
theorem cldCoeffFloor_le_bhksRecoveryFloor (core : ZPoly) :
    cldCoeffFloor core ≤ bhksRecoveryFloor core :=
  Nat.le_max_left _ _

/-- The recovery floor is at least the direct coefficient-recovery bound. -/
theorem defaultFactorCoeffBound_le_bhksRecoveryFloor (core : ZPoly) :
    ZPoly.defaultFactorCoeffBound core ≤ bhksRecoveryFloor core :=
  Nat.le_max_right _ _

/-- An irreducible copy of the acceptance floor used when reducing the fast loop.

Definitionally `bhksRecoveryFloor`, but marked `irreducible` so that `whnf` in
downstream proofs that case-split on a `bhksRecoveryCoreWithBound` application
does not eagerly expand the (symbolic, structurally large) floor computation
while reducing the loop's head `if`.  The loop's behavioural unfolding lemma
`bhksRecoveryCoreWithBound_unfold` re-exposes the plain `bhksRecoveryFloor`
comparison, so proofs reason about the genuine floor. -/
@[irreducible] def bhksRecoveryThreshold (core : ZPoly) : Nat :=
  bhksRecoveryFloor core

/-- The opaque recovery threshold equals its mathematical coefficient floor. -/
theorem bhksRecoveryThreshold_eq (core : ZPoly) :
    bhksRecoveryThreshold core = bhksRecoveryFloor core := by
  simp only [bhksRecoveryThreshold]

/-- Inner fast recovery recombination loop, parameterised by a precomputed CLD
column-adequacy `floor`.  Below `floor` a success cannot be accepted and every
recovery class (success or failure) advances the schedule identically, so the
expensive Hensel-lift / CLD-lattice / LLL / reconstruction computation is skipped
and the loop steps straight to the next scheduled precision.  At/above `floor`
a success is column-adequate and accepted immediately.

`floor` is threaded as a parameter so the (structurally large, degree-
exponential) `cldCoeffFloor` is evaluated once by `bhksRecoveryCoreWithBound`
rather than re-evaluated at every doubling step.

Private: only `bhksRecoveryCoreWithBound` (which passes `cldCoeffFloorGate core`)
is the semantically supported entry point; the bare `floor` parameter must not
be set independently. -/
private def bhksRecoveryLoop
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    Nat → Nat → Option (Array ZPoly)
  | _k, 0 => none
  | k, fuel + 1 =>
      if k < floor then
        if k ≥ B then
          none
        else
          bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel
      else
        match bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
        | .success factors =>
          some factors
        | .candidateFailure =>
          if k ≥ B then
            none
          else
            bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .productMismatch _ =>
          if k ≥ B then
            none
          else
            bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .degenerate =>
          if k ≥ B then
            none
          else
            bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel

/-- BHKS fast recovery recombination loop.  Computes the CLD column-adequacy floor
once (through the irreducible `bhksRecoveryThreshold`, so `whnf` in downstream
proofs that case-split on this application does not eagerly expand the symbolic
floor) and runs `bhksRecoveryLoop`. -/
def bhksRecoveryCoreWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    Option (Array ZPoly) :=
  bhksRecoveryLoop core B (bhksRecoveryThreshold core) primeData k fuel

/-- Behavioural unfolding for the optimized fast recovery loop: the precision-floor
short-circuit is propositionally equal to the original "recover at every step,
accept only at the floor" body.  Below the floor every recovery class steps to
the next precision, and at/above the floor a success is column-adequate; both
match the conditional form, so this lemma lets the recovery-on-schedule proofs reason
about the loop exactly as before. -/
private theorem bhksRecoveryCoreWithBound_unfold
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    bhksRecoveryCoreWithBound core B primeData k (fuel + 1) =
      match bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
      | .success factors =>
        if k ≥ bhksRecoveryFloor core then
          some factors
        else if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .candidateFailure =>
        if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .productMismatch _ =>
        if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .degenerate =>
        if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel := by
  have hrec : ∀ k',
      bhksRecoveryLoop core B (bhksRecoveryFloor core) primeData k' fuel =
        bhksRecoveryCoreWithBound core B primeData k' fuel := by
    intro k'
    rw [bhksRecoveryCoreWithBound, bhksRecoveryThreshold_eq]
  rw [bhksRecoveryCoreWithBound, bhksRecoveryThreshold_eq, bhksRecoveryLoop]
  simp only [hrec]
  by_cases hf : k < bhksRecoveryFloor core
  · rw [if_pos hf]
    have hfloor : ¬ k ≥ bhksRecoveryFloor core := Nat.not_le.mpr hf
    cases bhksRecoverClassified core (ZPoly.directLiftData core k primeData) <;>
      simp only [hfloor, if_false]
  · rw [if_neg hf]
    have hfloor : k ≥ bhksRecoveryFloor core := Nat.le_of_not_lt hf
    cases bhksRecoverClassified core (ZPoly.directLiftData core k primeData) <;>
      simp only [hfloor, if_true]

/-- Finite list of Hensel precisions inspected by the fast BHKS recovery loop. -/
def henselPrecisionSchedule (B : Nat) : Nat → Nat → List Nat
  | _k, 0 => []
  | k, fuel + 1 =>
      k :: if k ≥ B then [] else henselPrecisionSchedule B (nextHenselPrecision k B) fuel

private theorem initialHenselPrecision_le (B : Nat) :
    initialHenselPrecision B ≤ B := by
  unfold initialHenselPrecision
  by_cases hB : B ≤ 4
  · simp [hB]
  · simp [hB]
    omega

private theorem nextHenselPrecision_le (k B : Nat) :
    nextHenselPrecision k B ≤ B := by
  unfold nextHenselPrecision
  by_cases h : 2 * k < B
  · simp [h]
    omega
  · simp [h]

private theorem nextHenselPrecision_eq_B_of_cap_reached {k B : Nat}
    (h : B ≤ 2 * k) :
    nextHenselPrecision k B = B := by
  unfold nextHenselPrecision
  have hnot : ¬ 2 * k < B := by omega
  simp [hnot]

private theorem initialHenselPrecision_mem_schedule (B fuel : Nat) :
    initialHenselPrecision B ∈
      henselPrecisionSchedule B (initialHenselPrecision B) (fuel + 1) := by
  simp [henselPrecisionSchedule]

private theorem nextHenselPrecision_mem_schedule {B k fuel : Nat}
    (hk : ¬ k ≥ B) :
    nextHenselPrecision k B ∈
      henselPrecisionSchedule B k (fuel + 2) := by
  simp [henselPrecisionSchedule, hk]

/-- Helper: when the doubling fuel `fuel` is large enough that the geometric
progression starting from `k` reaches the cap `B`, the cap appears in the
finite Hensel precision schedule.  The geometric bound `B ≤ k * 2 ^ fuel`
is what we will discharge for the canonical executable choice
`k = initialHenselPrecision B`, `fuel = quadraticDoublingSteps B + 1`. -/
private theorem henselPrecisionSchedule_mem_cap
    {B : Nat} :
    ∀ (k fuel : Nat), 0 < k → k ≤ B → B ≤ k * 2 ^ fuel →
      B ∈ henselPrecisionSchedule B k (fuel + 1) := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro _ hk_le hfuel
      have hkB : k = B := by
        have : k * 2 ^ 0 = k := by simp
        omega
      subst hkB
      simp [henselPrecisionSchedule]
  | succ fuel ih =>
      intro hk_pos hk_le hfuel
      by_cases hk_eq : k = B
      · subst hk_eq
        simp [henselPrecisionSchedule]
      · have hk_lt : k < B := Nat.lt_of_le_of_ne hk_le hk_eq
        rw [henselPrecisionSchedule]
        simp only [List.mem_cons]
        right
        rw [if_neg (by omega : ¬ k ≥ B)]
        unfold nextHenselPrecision
        have hpow : k * 2 ^ (fuel + 1) = 2 * k * 2 ^ fuel := by
          rw [Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm k 2]
        by_cases h2 : 2 * k < B
        · rw [if_pos h2]
          refine ih (2 * k) (by omega) (by omega) ?_
          omega
        · rw [if_neg h2]
          refine ih B (by omega) (Nat.le_refl _) ?_
          have hge1 : 1 ≤ 2 ^ fuel := Nat.one_le_two_pow
          calc B = B * 1 := (Nat.mul_one B).symm
            _ ≤ B * 2 ^ fuel := Nat.mul_le_mul_left B hge1

/--
The fast-path cap `B` is itself a member of the canonical Hensel precision
schedule the executable loop walks: `henselPrecisionSchedule B
(initialHenselPrecision B) (quadraticDoublingSteps B + 2)`.

This is the connective schedule lemma used by the Mathlib-facing Group D
forward-recovery wrapper: callers who supply `ForwardRecoveryInputs` at the
canonical terminal precision no longer need to re-prove the executable
doubling-schedule membership obligation.
-/
theorem cap_mem_henselPrecisionSchedule (B : Nat) :
    B ∈ henselPrecisionSchedule B (initialHenselPrecision B)
      (ZPoly.quadraticDoublingSteps B + 2) := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    simp [henselPrecisionSchedule, initialHenselPrecision]
  · -- B ≥ 1.  Reduce to the geometric-bound helper.
    have hinit_pos : 0 < initialHenselPrecision B := by
      unfold initialHenselPrecision
      by_cases hle : B ≤ 4
      · simp [hle]; omega
      · simp [hle]
    have hinit_le : initialHenselPrecision B ≤ B := initialHenselPrecision_le B
    have hbound :
        B ≤ initialHenselPrecision B * 2 ^ (ZPoly.quadraticDoublingSteps B + 1) := by
      by_cases hsmall : B ≤ 4
      · have hinit : initialHenselPrecision B = B := by
          unfold initialHenselPrecision; simp [hsmall]
        rw [hinit]
        have hpow : 1 ≤ 2 ^ (ZPoly.quadraticDoublingSteps B + 1) :=
          Nat.one_le_two_pow
        calc B = B * 1 := (Nat.mul_one B).symm
          _ ≤ B * 2 ^ (ZPoly.quadraticDoublingSteps B + 1) :=
              Nat.mul_le_mul_left B hpow
      · have hinit : initialHenselPrecision B = 4 := by
          unfold initialHenselPrecision
          simp [hsmall]
        rw [hinit]
        have hquad :
            ZPoly.quadraticDoublingSteps B = (B - 1).log2 + 1 := by
          unfold ZPoly.quadraticDoublingSteps
          have : ¬ B ≤ 1 := by omega
          simp [this]
        rw [hquad]
        -- Goal: B ≤ 4 * 2 ^ ((B - 1).log2 + 1 + 1)
        have hlog : B - 1 < 2 ^ ((B - 1).log2 + 1) := Nat.lt_log2_self
        have hB_le : B ≤ 2 ^ ((B - 1).log2 + 1) := by omega
        have hexp :
            2 ^ ((B - 1).log2 + 1 + 1) = 2 * 2 ^ ((B - 1).log2 + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        calc B ≤ 2 ^ ((B - 1).log2 + 1) := hB_le
          _ ≤ 4 * 2 ^ ((B - 1).log2 + 1 + 1) := by
              rw [hexp]
              -- 2^(x+1) ≤ 4 * (2 * 2^(x+1)) = 8 * 2^(x+1)
              have hle : 2 ^ ((B - 1).log2 + 1) ≤ 8 * 2 ^ ((B - 1).log2 + 1) := by
                have : 1 ≤ 8 := by decide
                calc 2 ^ ((B - 1).log2 + 1)
                    = 1 * 2 ^ ((B - 1).log2 + 1) := (Nat.one_mul _).symm
                  _ ≤ 8 * 2 ^ ((B - 1).log2 + 1) := Nat.mul_le_mul_right _ this
              have h8eq : 4 * (2 * 2 ^ ((B - 1).log2 + 1)) =
                  8 * 2 ^ ((B - 1).log2 + 1) := by
                rw [← Nat.mul_assoc]
              omega
    exact henselPrecisionSchedule_mem_cap _ _ hinit_pos hinit_le hbound

private theorem bhksRecoveryCoreWithBound_isSome_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (ZPoly.directLiftData core target primeData) = some factors) :
    (bhksRecoveryCoreWithBound core B primeData start fuel).isSome := by
  induction fuel generalizing start with
  | zero =>
      simp [henselPrecisionSchedule] at hmem
  | succ fuel ih =>
      rw [bhksRecoveryCoreWithBound_unfold]
      cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core start primeData) with
      | success xs =>
          by_cases hstart : start ≥ bhksRecoveryFloor core
          · simp [hstart]
          · by_cases hk : start ≥ B
            · exfalso
              have htarget : target = start := by
                simpa [henselPrecisionSchedule, hk] using hmem
              omega
            · simp [hstart, hk]
              have hmem' :
                  target ∈
                    henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                have hmem_tail :
                    target = start ∨
                      target ∈
                        henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                  simpa [henselPrecisionSchedule, hk] using hmem
                cases hmem_tail with
                | inl htarget => omega
                | inr htail => exact htail
              exact ih hmem'
      | degenerate =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'
      | candidateFailure =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'
      | productMismatch cands =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'

/--
If a target precision is on the fast recovery schedule, recovery succeeds there,
and no other scheduled precision before the target succeeds, then the
first-success loop returns exactly the target recovery.

This is the executable-loop determinism skeleton.  The BHKS precision theorem
supplies the `hno` premise by ruling out successful recovery below the
Mignotte/cap precision.
-/
theorem bhksRecoveryCoreWithBound_eq_some_of_recovery_on_schedule_of_no_prior_recovery
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hno :
      ∀ k, k ∈ henselPrecisionSchedule B start fuel → k ≠ target →
        bhksRecover? core (ZPoly.directLiftData core k primeData) = none)
    (hrecover :
      bhksRecover? core (ZPoly.directLiftData core target primeData) = some factors) :
    bhksRecoveryCoreWithBound core B primeData start fuel = some factors := by
  induction fuel generalizing start with
  | zero =>
      simp [henselPrecisionSchedule] at hmem
  | succ fuel ih =>
      rw [bhksRecoveryCoreWithBound_unfold]
      cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core start primeData) with
      | success xs =>
          by_cases htarget : start = target
          · subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
            simp only [ge_iff_le, hfloor, if_true]
            exact congrArg some hrecover
          · have hstart_mem :
                start ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule]
            have hnone := hno start hstart_mem htarget
            rw [bhksRecover?] at hnone
            simp [hclass, BhksRecoveryResult.toOption] at hnone
      | degenerate =>
          by_cases hk : start ≥ B
          · simp [hk]
            have htarget : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem_tail :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_cases :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_cases with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            refine ih hmem_tail ?_
            intro k hk_mem hk_ne
            have hk_schedule :
                k ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule, hk, hk_mem]
            exact hno k hk_schedule hk_ne
      | candidateFailure =>
          by_cases hk : start ≥ B
          · simp [hk]
            have htarget : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem_tail :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_cases :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_cases with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            refine ih hmem_tail ?_
            intro k hk_mem hk_ne
            have hk_schedule :
                k ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule, hk, hk_mem]
            exact hno k hk_schedule hk_ne
      | productMismatch cands =>
          by_cases hk : start ≥ B
          · simp [hk]
            have htarget : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem_tail :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_cases :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_cases with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            refine ih hmem_tail ?_
            intro k hk_mem hk_ne
            have hk_schedule :
                k ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule, hk, hk_mem]
            exact hno k hk_schedule hk_ne

end Hex
