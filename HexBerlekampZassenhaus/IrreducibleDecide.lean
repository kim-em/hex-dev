/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.IrreducibleDecide
public import HexBerlekampZassenhaus.EisensteinCore
public import HexBerlekampZassenhaus.IrreducibleCore
public import HexBerlekampZassenhaus.PrimeSelection

public section

/-!
Kernel-decidable irreducibility entry points for `Hex.ZPoly` — a single-prime
modular witness or an Eisenstein-after-shift certificate — consumed by the
`irreducibility`/`factor_poly` elaborators.

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

/-- A dense-size-one polynomial is the constant on its zeroth coefficient. -/
theorem eq_C_coeff_zero_of_size_one {f : ZPoly} (h : f.size = 1) :
    f = DensePoly.C (f.coeff 0) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_C]
  match i with
  | 0 => rw [if_pos rfl]
  | i + 1 =>
      rw [if_neg (by omega)]
      exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

/-- A single-prime modular irreducibility witness for a `ZPoly` factor,
packing its own modulus and bounds instance (the `PrimeFactorData` idiom) so
witnesses at different primes share one type. -/
structure ModPWitness where
  /-- The witnessing prime. -/
  p : Nat
  /-- Bounds instance for the modulus. -/
  bounds : ZMod64.Bounds p
  /-- The monic image of the reduction mod `p`. -/
  m : @FpPoly p bounds
  /-- The leading unit of the reduction mod `p`. -/
  c : @ZMod64 p bounds
  /-- Rabin certificate for `m`. -/
  cert : Berlekamp.IrreducibilityCertificate

/-- One irreducibility witness for a `ZPoly`: a prime constant, a primitive
linear, a single-prime modular reduction certificate, or an
Eisenstein-after-shift certificate. -/
inductive IrredWitness where
  /-- The polynomial is a constant with prime absolute value. -/
  | primeConst
  /-- The polynomial is linear (dense size two) and primitive. -/
  | linear
  /-- Single-prime route: the reduction mod `w.p` is irreducible. -/
  | modP (w : ModPWitness)
  /-- Eisenstein route: `ZPoly.translate shift f` satisfies Eisenstein's
  criterion at the prime `q`. -/
  | eisenstein (q : Nat) (shift : Int)

/-- Kernel-decidable check that `w` witnesses irreducibility of `f`. -/
@[expose]
def checkIrredWitness (f : ZPoly) : IrredWitness → Bool
  | .primeConst => decide (f.size = 1) && isNatPrime (f.coeff 0).natAbs
  | .linear => decide (f.size = 2) && decide (ZPoly.content f = 1)
  | .modP w =>
      letI := w.bounds
      Hex.Nat.isPrimeTrial w.p && decide (ZPoly.content f = 1) &&
        decide (ZPoly.leadingCoeffModP f w.p ≠ 0) && decide (1 < f.size) &&
        !(decide (w.c = 0)) &&
        DensePoly.beqCoeffs (DensePoly.scale w.c w.m) (ZPoly.modP w.p f) &&
        Berlekamp.checkMonicCert w.m w.cert
  | .eisenstein q shift =>
      let g := ZPoly.translate shift f
      Hex.Nat.isPrimeTrial q && decide (ZPoly.content g = 1) &&
        decide (1 < g.size) &&
        !(decide (g.coeff (g.size - 1) % (q : Int) = 0)) &&
        ((List.range (g.size - 1)).all fun i =>
          decide (g.coeff i % (q : Int) = 0)) &&
        !(decide (g.coeff 0 % ((q : Int) * (q : Int)) = 0))

/-- A passing `checkIrredWitness` forces irreducibility. -/
theorem irreducible_of_checkIrredWitness
    (f : ZPoly) (w : IrredWitness)
    (hcheck : checkIrredWitness f w = true) :
    ZPoly.Irreducible f := by
  match w with
  | .primeConst =>
      unfold checkIrredWitness at hcheck
      rw [Bool.and_eq_true] at hcheck
      obtain ⟨hsize, hprime⟩ := hcheck
      rw [eq_C_coeff_zero_of_size_one (of_decide_eq_true hsize)]
      exact irreducible_C_of_isNatPrime hprime
  | .linear =>
      unfold checkIrredWitness at hcheck
      rw [Bool.and_eq_true] at hcheck
      exact irreducible_of_linear f hcheck.1 hcheck.2
  | .modP wit =>
      unfold checkIrredWitness at hcheck
      letI := wit.bounds
      simp only [Bool.and_eq_true] at hcheck
      obtain ⟨⟨⟨⟨⟨⟨hp, hcontent⟩, hadm⟩, hsize⟩, hc⟩, hfm⟩, hcert⟩ := hcheck
      rw [Bool.not_eq_true'] at hc
      exact irreducible_of_modPCert f wit.p wit.m wit.c wit.cert
        hp (decide_eq_true (of_decide_eq_true hcontent))
        (decide_eq_true (of_decide_eq_true hadm))
        (decide_eq_true (of_decide_eq_true hsize)) hc hfm hcert
  | .eisenstein q shift =>
      unfold checkIrredWitness at hcheck
      simp only [Bool.and_eq_true] at hcheck
      obtain ⟨⟨⟨⟨⟨hp, hcontent⟩, hsize⟩, hlead⟩, hlow⟩, hsq⟩ := hcheck
      rw [Bool.not_eq_true'] at hlead hsq
      exact irreducible_of_eisensteinCert f q shift hp hcontent hsize
        hlead hlow hsq

/-- Bulk kernel-decidable irreducibility for a `ZPoly` factor list with
repetition: `certified` carries one `(factor, witness)` entry per *distinct*
factor, matched by `beqCoeffs`, so each witness is checked once regardless of
multiplicity. -/
@[expose]
def checkIrredCover (factors : List ZPoly)
    (certified : List (ZPoly × IrredWitness)) : Bool :=
  (certified.all fun e => checkIrredWitness e.1 e.2) &&
    (factors.all fun q => certified.any fun e => DensePoly.beqCoeffs e.1 q)

/-- A passing `checkIrredCover` forces irreducibility of every listed factor.
The single Boolean hypothesis is the `factors_irred` slot of a reified
`ZPoly.Factored` value. -/
theorem irreducible_of_checkIrredCover
    (factors : List ZPoly) (certified : List (ZPoly × IrredWitness))
    (hcheck : checkIrredCover factors certified = true) :
    ∀ q ∈ factors, ZPoly.Irreducible q := by
  unfold checkIrredCover at hcheck
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨hvalid, hcover⟩ := hcheck
  rw [List.all_eq_true] at hvalid hcover
  intro q hq
  have hq' := hcover q hq
  rw [List.any_eq_true] at hq'
  obtain ⟨e, he, hbeq⟩ := hq'
  have hw := irreducible_of_checkIrredWitness e.1 e.2 (hvalid e he)
  rwa [DensePoly.eq_of_beqCoeffs hbeq] at hw

end ZPoly
end Hex
