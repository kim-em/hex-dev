/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.Prime
public import HexModArith.Prime
public import HexPolyFp.Degree
public import HexBerlekamp.Irreducibility
public import HexBerlekamp.RabinSoundness

public section

/-!
Kernel-decidable irreducibility entry points for `FpPoly p`, consumed by the
`irreducibility`/`factor_poly` elaborators: every hypothesis is a Boolean check
on literal data, so a reified application discharges each slot with
`Eq.refl true`/`Eq.refl false` and the kernel verifies by reduction alone.

The monic-guarded checker `checkMonicCert` folds the monicity side condition
into the Boolean (the `checkCertAtFactor` idiom), so callers never construct a
`DensePoly.Monic` proof term. The scaled entry point
`irreducible_of_checkMonicCert_scale` additionally strips a unit scaling, so a
non-monic polynomial is certified through its monic normalization `m` and
leading coefficient `c` with the reconstruction check `scale c m = f` performed
by `DensePoly.beqCoeffs`.
-/

namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- Monic-guarded wrapper around the incremental linear certificate checker:
`true` only when `m` is monic and the certificate replays. Folding the monicity
guard into the Boolean lets reified applications avoid constructing a
`DensePoly.Monic` proof term. -/
@[expose]
def checkMonicCert (m : FpPoly p) (cert : IrreducibilityCertificate) : Bool :=
  if hmonic : DensePoly.leadingCoeff m = 1 then
    checkIrreducibilityCertificateLinearIncremental m (by exact hmonic) cert
  else false

/-- A passing `checkMonicCert` forces irreducibility of the (necessarily monic)
input. -/
theorem irreducible_of_checkMonicCert [ZMod64.PrimeModulus p]
    (m : FpPoly p) (cert : IrreducibilityCertificate)
    (hcheck : checkMonicCert m cert = true) :
    FpPoly.Irreducible m := by
  unfold checkMonicCert at hcheck
  split at hcheck
  · exact checkIrreducibilityCertificateLinearIncremental_imp_irreducible
      m (by assumption) cert hcheck
  · exact absurd hcheck (by simp)

/-- Kernel-decidable irreducibility for a possibly non-monic `f : FpPoly p`:
`f` reconstructs as `scale c m` for a monic `m` whose Rabin certificate
replays, with a nonzero scalar and a prime modulus. Every hypothesis is a
Boolean check on literal data. -/
theorem irreducible_of_checkMonicCert_scale
    (f m : FpPoly p) (c : ZMod64 p) (cert : IrreducibilityCertificate)
    (hp : Hex.Nat.isPrimeTrial p = true)
    (hc : decide (c = 0) = false)
    (hfm : DensePoly.beqCoeffs (DensePoly.scale c m) f = true)
    (hcheck : checkMonicCert m cert = true) :
    FpPoly.Irreducible f := by
  haveI : ZMod64.PrimeModulus p :=
    ZMod64.primeModulusOfPrime (Hex.Nat.isPrimeTrial_isPrime hp)
  have hm : FpPoly.Irreducible m := irreducible_of_checkMonicCert m cert hcheck
  have hcne : c ≠ 0 := of_decide_eq_false hc
  have hscaled := FpPoly.irreducible_scale_of_ne_zero hcne hm
  rwa [DensePoly.eq_of_beqCoeffs hfm] at hscaled

end Berlekamp
end Hex
