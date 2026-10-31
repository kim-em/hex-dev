/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateReplay

public section

namespace Hex.Groebner

/-- Sealed continuation distinguishes production from independent replay.
Original field/order and polynomial data are fixed by the type parameters. -/
structure DivideState (context : Context) (divisors : Array Certificate.Polynomial)
    (dividend : Certificate.Polynomial) where
  private mk ::
  stage : Sum Certificate.Division.State (Certificate.Verification.State context divisors dividend)

/-- A checked result, invalid input, a rejected candidate, exhausted allowance,
platform addressability and an internal arithmetic failure remain distinct. -/
inductive DivideResult (context : Context) (divisors : Array Certificate.Polynomial)
    (dividend : Certificate.Polynomial) where
  | success (value : Certificate.CheckedDivision context divisors dividend) (usage : Certificate.Usage)
  | invalid (index : Nat) (usage : Certificate.Usage)
  | exhausted (resource : Certificate.Resource) (state : DivideState context divisors dividend)
  | address (state : DivideState context divisors dividend)
  | internal (usage : Certificate.Usage)

private def verified {context : Context} {divisors : Array Certificate.Polynomial}
    {dividend : Certificate.Polynomial} :
    Certificate.Verification.Result context divisors dividend → DivideResult context divisors dividend
  | .checked value usage => .success value usage
  | .invalid i usage => .invalid i usage
  | .rejected usage => .internal usage
  | .exhausted resource state => .exhausted resource ⟨.inr state⟩
  | .address state => .address ⟨.inr state⟩
  | .internal usage => .internal usage

private def produced (context : Context) (budget : Certificate.Budget)
    (divisors : Array Certificate.Polynomial) (dividend : Certificate.Polynomial) :
    Certificate.Division.Result → DivideResult context divisors dividend
  | .candidate value usage =>
    verified (Certificate.Verification.verifyFrom context budget divisors dividend value usage)
  | .invalid i usage => .invalid i usage
  | .exhausted resource state => .exhausted resource ⟨.inl state⟩
  | .address state => .address ⟨.inl state⟩
  | .internal usage => .internal usage

/-- Resume an unfinished production or replay stage with absolute allowances.
No argument can replace the original field/order, divisors or dividend. -/
def resumeDivideWith {context : Context} {divisors : Array Certificate.Polynomial}
    {dividend : Certificate.Polynomial} (budget : Certificate.Budget)
    (state : DivideState context divisors dividend) : DivideResult context divisors dividend :=
  match state.stage with
  | .inl producer => produced context budget divisors dividend (Certificate.Division.resumeWith budget producer)
  | .inr replay => verified (Certificate.Verification.resumeWith budget replay)

/-- Bounded exact prime-field division on canonical ordinary residue lists.
Success contains explicit quotients and an irreducible remainder accepted by
independent reconstruction and degree-bound checking. Production and replay
consume the same cumulative allowance. This certificate-oriented reference
route uses ordinary lists separately from packed F4 candidate hot loops. -/
def divideWith (context : Context) (budget : Certificate.Budget)
    (divisors : Array Certificate.Polynomial) (dividend : Certificate.Polynomial) :
    DivideResult context divisors dividend :=
  produced context budget divisors dividend
    (Certificate.Division.computeWith context budget divisors dividend)

end Hex.Groebner
