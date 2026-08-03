/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.FactorizationData
public import HexBerlekampZassenhaus.SquareFreeModularCert

public section
set_option backward.proofsInPublic true

/-!
# A finite-field obstruction to integer divisibility

Reduction modulo a prime `q` is a ring homomorphism `ℤ[X] → 𝔽_q[X]`, so it
carries divisibility forward: a divisor of the recombination target reduces to a
divisor of the reduced target, and `𝔽_q[X]` division then leaves no remainder.
Contrapositively, a nonzero remainder is a *proof* that the candidate does not
divide, obtained in machine-word arithmetic rather than by dividing multi-limb
integer polynomials.

The obstruction is one-sided.  A zero remainder says nothing: exact integer
division remains the only accepting test, and the traversal falls through to it
unchanged.  The divisor's image is allowed to be zero or to lose its leading
coefficient; `mod_eq_zero_of_dvd` covers those cases uniformly, so there is no
"inconclusive" branch to get wrong.
-/

namespace Hex

/-- The fixed word-sized prime carrying the divisibility obstruction.

Any prime below `2 ^ 31` satisfies `ZMod64.Bounds`; `2 ^ 26 - 5` is large enough
that an accidental zero remainder costs at most one exact division that would
have been performed anyway, and small enough that its trial-division primality
proof is cheap to check in the kernel. -/
def obstructionPrime : Nat := 67108859

instance : ZMod64.Bounds obstructionPrime where
  pPos := by decide
  pLtR := by decide

set_option maxRecDepth 4000 in
/-- `obstructionPrime` is prime, by kernel-checked trial division. -/
theorem obstructionPrime_prime : Hex.Nat.Prime obstructionPrime :=
  Hex.Nat.isPrimeTrial_isPrime (by decide)

instance : ZMod64.PrimeModulus obstructionPrime :=
  ZMod64.primeModulusOfPrime obstructionPrime_prime

/-- The image of an integer polynomial in `𝔽_q[X]`. -/
@[expose]
def obstructionImage (f : ZPoly) : FpPoly obstructionPrime :=
  ZPoly.modP obstructionPrime f

/-- The recombination target's image in `𝔽_q[X]`, computed once for a whole
subset-cardinality level rather than once per candidate.

The proof field pins the stored array to the reference reduction, so a traversal
reading this is interchangeable with one reducing the target at every leaf. -/
structure TargetImage (target : ZPoly) where
  /-- The reduced target. -/
  image : FpPoly obstructionPrime
  /-- The stored reduction is the reference reduction. -/
  image_eq : image = obstructionImage target

/-- Reduce a recombination target once. -/
@[expose]
def targetImage (target : ZPoly) : TargetImage target :=
  { image := obstructionImage target, image_eq := rfl }

/-- Reference form of the obstruction: the `𝔽_q[X]` remainder of the reduced
target by the reduced candidate. -/
@[expose]
def obstructionRemainder (target candidate : ZPoly) : FpPoly obstructionPrime :=
  DensePoly.mod (obstructionImage target) (obstructionImage candidate)

/-- The divisibility obstruction: `true` exactly when the reduced candidate
leaves a nonzero remainder in the reduced target, which certifies that the
candidate does not divide the target over `ℤ`.

The divisor's leading-coefficient inverse is computed once for the whole
long-division pass, which is the only difference from `obstructionRemainder`. -/
@[expose]
def obstructs {target : ZPoly} (cached : TargetImage target)
    (candidate : ZPoly) : Bool :=
  !(FpPoly.modCached cached.image (obstructionImage candidate)).isZero

/-- The optimized obstruction computes the reference remainder. -/
theorem obstructs_eq {target : ZPoly} (cached : TargetImage target)
    (candidate : ZPoly) :
    obstructs cached candidate = !(obstructionRemainder target candidate).isZero := by
  unfold obstructs obstructionRemainder
  rw [cached.image_eq, FpPoly.modCached_eq]

/-- Reduction modulo `q` carries integer divisibility into `𝔽_q[X]`, where
division by the image leaves no remainder.  This is the whole content of the
obstruction: it fires only on candidates that cannot divide. -/
theorem obstructionRemainder_eq_zero_of_dvd {target candidate : ZPoly}
    (hdvd : candidate ∣ target) :
    obstructionRemainder target candidate = 0 :=
  DensePoly.mod_eq_zero_of_dvd _ _ (ZPoly.modP_dvd_of_dvd hdvd)

/-- No false rejection: a genuine divisor is never obstructed. -/
theorem obstructs_eq_false_of_dvd {target : ZPoly} (cached : TargetImage target)
    {candidate : ZPoly} (hdvd : candidate ∣ target) :
    obstructs cached candidate = false := by
  rw [obstructs_eq, obstructionRemainder_eq_zero_of_dvd hdvd]
  rfl

/-- An obstructed candidate does not divide the target. -/
theorem not_dvd_of_obstructs {target : ZPoly} (cached : TargetImage target)
    {candidate : ZPoly} (hobstructs : obstructs cached candidate = true) :
    ¬ candidate ∣ target := by
  intro hdvd
  rw [obstructs_eq_false_of_dvd cached hdvd] at hobstructs
  exact Bool.noConfusion hobstructs

/-- An obstructed candidate would have failed exact division, so skipping the
exact division changes nothing.  This is the equation the traversal's leaf
rewrites through. -/
theorem exactQuotient?_eq_none_of_obstructs {target : ZPoly}
    (cached : TargetImage target) {candidate : ZPoly}
    (hobstructs : obstructs cached candidate = true) :
    exactQuotient? target candidate = none := by
  cases hquot : exactQuotient? target candidate with
  | none => rfl
  | some quotient =>
      refine absurd ⟨quotient, ?_⟩ (not_dvd_of_obstructs cached hobstructs)
      rw [DensePoly.mul_comm_poly]
      exact (exactQuotient?_product hquot).symm

end Hex
