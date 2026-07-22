/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.IrreducibleDecide
public import HexBerlekampZassenhaus.IrreducibleCore
public import HexBerlekampZassenhaus.PrimeSelection

public section

/-!
Kernel-decidable irreducibility entry point for `Hex.ZPoly` via a single-prime
modular witness, consumed by the `irreducibility`/`factor_poly` elaborators.

For a primitive, non-constant `f` whose leading coefficient survives reduction
mod a prime `p`, irreducibility of `ZPoly.modP p f` transfers to `f` by the
Gauss-style `Irreducible_of_modP_irreducible_of_primitive_of_admissible`. The
modular irreducibility itself is certified through the monic normalization
`m` (with leading unit `c`) and a Rabin certificate replayed by
`Berlekamp.checkMonicCert`. Every hypothesis is a Boolean check on literal
data, so a reified application discharges each slot with `Eq.refl true` /
`Eq.refl false` and the kernel verifies by reduction alone; the only
non-trivial kernel work is one `modP` pass and the incremental Rabin pow-chain
replay, both on literals.
-/

namespace Hex
namespace ZPoly

/-- Kernel-decidable single-prime irreducibility for `f : ZPoly`: `f` is
primitive and non-constant, its reduction mod the trial-division prime `p`
reconstructs as `scale c m` for a monic `m` with a passing Rabin certificate,
and the leading coefficient survives the reduction. Fails to apply (no slot
reduces to `true`) exactly when no single prime witnesses irreducibility —
balanced inputs need the multi-prime degree-obstruction certificate from the
Mathlib bridge. -/
theorem irreducible_of_modPCert
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (m : FpPoly p) (c : ZMod64 p) (cert : Berlekamp.IrreducibilityCertificate)
    (hp : Hex.Nat.isPrimeTrial p = true)
    (hcontent : decide (ZPoly.content f = 1) = true)
    (hadm : decide (ZPoly.leadingCoeffModP f p ≠ 0) = true)
    (hsize : decide (1 < f.size) = true)
    (hc : decide (c = 0) = false)
    (hfm : DensePoly.beqCoeffs (DensePoly.scale c m) (ZPoly.modP p f) = true)
    (hcheck : Berlekamp.checkMonicCert m cert = true) :
    ZPoly.Irreducible f := by
  have hprime : Hex.Nat.Prime p := Hex.Nat.isPrimeTrial_isPrime hp
  have hirr : FpPoly.Irreducible (ZPoly.modP p f) :=
    Berlekamp.irreducible_of_checkMonicCert_scale (ZPoly.modP p f) m c cert
      hp hc hfm hcheck
  have hprim : ZPoly.Primitive f :=
    of_decide_eq_true (p := ZPoly.content f = 1) hcontent
  have hadm' : leadingCoeffAdmissible f p :=
    of_decide_eq_true (p := ZPoly.leadingCoeffModP f p ≠ 0) hadm
  exact ZPoly.Irreducible_of_modP_irreducible_of_primitive_of_admissible f p
    hprime hprim hadm' (of_decide_eq_true hsize) hirr

end ZPoly
end Hex
