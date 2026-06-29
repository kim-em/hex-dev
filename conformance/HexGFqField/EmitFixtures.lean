/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGFqField.Operations
import HexBerlekamp.RabinSoundness

/-!
JSONL emit driver for the `hex-gfq-field` oracle.

`lake exe hexgfqfield_emit_fixtures` writes one `gfqfield` fixture
record plus five `result` records per case to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/gfqfield_flint.py` reads the same stream and re-runs
each operation through python-flint's `fq_default_ctx` configured
with the same explicit modulus.

Cases cover `F_p[x] / (m(x))` for every `(p, n)` with
`p ∈ {2, 3, 5, 7}` and `n ∈ {2, 3, 4, 6}` (one case per pair, sixteen
in total).  For each case we emit:

* `mul`  — coefficients of `(a * b) mod m` in `F_p`;
* `inv`  — coefficients of `a⁻¹` (well-defined: `a` is nonzero);
* `div`  — coefficients of `a / b` (well-defined: `b` is nonzero);
* `frob` — coefficients of the Frobenius `a^p`;
* `zpow` — coefficients of `a^zexp` for the integer exponent carried
  by the fixture (positive and negative exponents are exercised
  across the matrix).

Each modulus's irreducibility is discharged by a literal
`Berlekamp.IrreducibilityCertificate` whose pow chain and Bezout
witnesses are checked by the kernel-reducible
`Berlekamp.checkIrreducibilityCertificateLinear`, then routed through
`Berlekamp.rabinTest_imp_irreducible` (see
`HexBerlekamp/RabinSoundness.lean`).
-/

namespace Hex.GFqFieldEmit

open Hex.Conformance.Emit
open Hex
open Hex.GFqField

private def lib : String := "HexGFqField"

private theorem prime_two : Hex.Nat.Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem prime_three : Hex.Nat.Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · exact Or.inr rfl

private theorem prime_five : Hex.Nat.Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · simp at hm
  · simp at hm
  · exact Or.inr rfl

private theorem prime_seven : Hex.Nat.Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  · exact Or.inr rfl

private instance bounds_two : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
private instance bounds_three : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance bounds_five : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance bounds_seven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private instance pm_two : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime prime_two
private instance pm_three : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime prime_three
private instance pm_five : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five
private instance pm_seven : ZMod64.PrimeModulus 7 :=
  ZMod64.primeModulusOfPrime prime_seven

/-- Build an `FpPoly p` from a `Nat` coefficient list (constant term first).
Used for the per-case `a` / `b` operands at runtime; the moduli below
are constructed directly as struct literals so `decide` can discharge
the positive-degree obligation without recursing through the
`trimTrailingZeros` pass that `ofCoeffs` would interpose. -/
private def mkPoly {p : Nat} [ZMod64.Bounds p] (coeffs : List Nat) : FpPoly p :=
  FpPoly.ofCoeffs (coeffs.toArray.map (fun n => ZMod64.ofNat p n))

/-- Per-prime `Array Nat → FpPoly p` helpers used by the certificate
literals below. The simp set in each `..._certificate_check` proof
unfolds these to expose the underlying `ofCoeffs` array. -/
private def polyP2 (coeffs : Array Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))
private def polyP3 (coeffs : Array Nat) : FpPoly 3 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 3 n))
private def polyP5 (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))
private def polyP7 (coeffs : Array Nat) : FpPoly 7 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 7 n))

/-- Lift an `FpPoly p` to `List Int` via the canonical `[0, p)` representative. -/
private def liftCoeffs {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Int :=
  f.toArray.toList.map (fun c => Int.ofNat c.toNat)

private theorem one_ne_zero_two : (1 : ZMod64 2) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 2) 1 0).mp h
  simp at hm

private theorem one_ne_zero_three : (1 : ZMod64 3) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 3) 1 0).mp h
  simp at hm

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_seven : (1 : ZMod64 7) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 7) 1 0).mp h
  simp at hm

/-- Run one case for a fully-specified modulus: emit one `gfqfield`
fixture plus the five op results.  Each call site supplies the
prime witness `hp`, modulus `m`, positive-degree and irreducibility
proofs, the case identifier, the unreduced operand coefficient
lists, and the `zpow` exponent. -/
private def emitAt
    {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    (m : FpPoly p) (hpos : 0 < FpPoly.degree m)
    (hirr : FpPoly.Irreducible m)
    (caseId : String) (aCoeffs bCoeffs : List Nat) (zexp : Int) :
    IO Unit := do
  let aPoly : FpPoly p := mkPoly aCoeffs
  let bPoly : FpPoly p := mkPoly bCoeffs
  let xa : FiniteField m hpos hp hirr := ofPoly m hpos hp hirr aPoly
  let xb : FiniteField m hpos hp hirr := ofPoly m hpos hp hirr bPoly
  emitGfqFieldFixture lib caseId (Int.ofNat p)
    (liftCoeffs m) (liftCoeffs (repr xa)) (liftCoeffs (repr xb)) zexp
  emitResult lib caseId "mul"  (polyValue (liftCoeffs (repr (xa * xb))))
  emitResult lib caseId "inv"  (polyValue (liftCoeffs (repr xa⁻¹)))
  emitResult lib caseId "div"  (polyValue (liftCoeffs (repr (xa / xb))))
  emitResult lib caseId "frob" (polyValue (liftCoeffs (repr (frob xa))))
  emitResult lib caseId "zpow" (polyValue (liftCoeffs (repr (zpow xa zexp))))

/-! ## Per-modulus declarations and emit helpers.

Sixteen `(p, n)` pairs.  For each, define the irreducible modulus,
record positive-degree by `decide`, and discharge `FpPoly.Irreducible`
via a literal `Berlekamp.IrreducibilityCertificate` checked by
`Berlekamp.checkIrreducibilityCertificateLinear` and routed through
`Berlekamp.rabinTest_imp_irreducible`. -/

/-- Precomputed `maximalProperDivisors` for the four `n` values used
below. `simp` does not reliably reduce the underlying filter for `n ≥ 3`,
so we rewrite via these explicit equalities. -/
private theorem maxProperDiv_2 : Berlekamp.maximalProperDivisors 2 = [1] := by decide
private theorem maxProperDiv_3 : Berlekamp.maximalProperDivisors 3 = [1] := by decide
private theorem maxProperDiv_4 : Berlekamp.maximalProperDivisors 4 = [2] := by decide
private theorem maxProperDiv_6 : Berlekamp.maximalProperDivisors 6 = [2, 3] := by decide

-- p = 2

/-- `x^2 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n2 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 1]
    normalized := Or.inr (by decide) }
private theorem m_p2_n2_pos : 0 < FpPoly.degree m_p2_n2 := by decide
private theorem m_p2_n2_monic : DensePoly.Monic m_p2_n2 := by rfl

private def m_p2_n2_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 2
  powChain := #[polyP2 #[0, 1], polyP2 #[1, 1], polyP2 #[0, 1]]
  bezout := #[{ left := polyP2 #[], right := polyP2 #[1] }]

set_option maxRecDepth 4096 in
private theorem m_p2_n2_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p2_n2 m_p2_n2_monic
        m_p2_n2_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p2_n2_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_2,
    m_p2_n2, polyP2]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p2_n2_irr : FpPoly.Irreducible m_p2_n2 :=
  Berlekamp.rabinTest_imp_irreducible m_p2_n2 m_p2_n2_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p2_n2 m_p2_n2_monic m_p2_n2_certificate
      m_p2_n2_certificate_check)

/-- `x^3 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n3 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p2_n3_pos : 0 < FpPoly.degree m_p2_n3 := by decide
private theorem m_p2_n3_monic : DensePoly.Monic m_p2_n3 := by rfl

private def m_p2_n3_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 3
  powChain :=
    #[polyP2 #[0, 1], polyP2 #[0, 0, 1], polyP2 #[0, 1, 1], polyP2 #[0, 1]]
  bezout := #[{ left := polyP2 #[1], right := polyP2 #[1, 1] }]

set_option maxRecDepth 4096 in
private theorem m_p2_n3_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p2_n3 m_p2_n3_monic
        m_p2_n3_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p2_n3_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_3,
    m_p2_n3, polyP2]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p2_n3_irr : FpPoly.Irreducible m_p2_n3 :=
  Berlekamp.rabinTest_imp_irreducible m_p2_n3 m_p2_n3_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p2_n3 m_p2_n3_monic m_p2_n3_certificate
      m_p2_n3_certificate_check)

/-- `x^4 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n4 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p2_n4_pos : 0 < FpPoly.degree m_p2_n4 := by decide
private theorem m_p2_n4_monic : DensePoly.Monic m_p2_n4 := by rfl

private def m_p2_n4_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 4
  powChain :=
    #[polyP2 #[0, 1], polyP2 #[0, 0, 1], polyP2 #[1, 1],
      polyP2 #[1, 0, 1], polyP2 #[0, 1]]
  bezout := #[{ left := polyP2 #[], right := polyP2 #[1] }]

set_option maxRecDepth 4096 in
private theorem m_p2_n4_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p2_n4 m_p2_n4_monic
        m_p2_n4_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p2_n4_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4,
    m_p2_n4, polyP2]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p2_n4_irr : FpPoly.Irreducible m_p2_n4 :=
  Berlekamp.rabinTest_imp_irreducible m_p2_n4 m_p2_n4_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p2_n4 m_p2_n4_monic m_p2_n4_certificate
      m_p2_n4_certificate_check)

/-- `x^6 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n6 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 0, 0, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p2_n6_pos : 0 < FpPoly.degree m_p2_n6 := by decide
private theorem m_p2_n6_monic : DensePoly.Monic m_p2_n6 := by rfl

private def m_p2_n6_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 6
  powChain :=
    #[polyP2 #[0, 1], polyP2 #[0, 0, 1], polyP2 #[0, 0, 0, 0, 1],
      polyP2 #[0, 0, 1, 1], polyP2 #[1, 1, 0, 0, 1],
      polyP2 #[1, 0, 0, 1], polyP2 #[0, 1]]
  bezout :=
    #[{ left := polyP2 #[1, 0, 1, 1],
        right := polyP2 #[1, 1, 0, 0, 1, 1] },
      { left := polyP2 #[1, 1],
        right := polyP2 #[0, 1, 1, 0, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem m_p2_n6_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p2_n6 m_p2_n6_monic
        m_p2_n6_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p2_n6_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_6,
    m_p2_n6, polyP2]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
          omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · exact ⟨rfl, rfl⟩

private theorem m_p2_n6_irr : FpPoly.Irreducible m_p2_n6 :=
  Berlekamp.rabinTest_imp_irreducible m_p2_n6 m_p2_n6_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p2_n6 m_p2_n6_monic m_p2_n6_certificate
      m_p2_n6_certificate_check)

-- p = 3

/-- `x^2 + 1` — irreducible over `F_3` (-1 is a non-square mod 3). -/
private def m_p3_n2 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p3_n2_pos : 0 < FpPoly.degree m_p3_n2 := by decide
private theorem m_p3_n2_monic : DensePoly.Monic m_p3_n2 := by rfl

private def m_p3_n2_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 2
  powChain := #[polyP3 #[0, 1], polyP3 #[0, 2], polyP3 #[0, 1]]
  bezout := #[{ left := polyP3 #[1], right := polyP3 #[0, 2] }]

set_option maxRecDepth 4096 in
private theorem m_p3_n2_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p3_n2 m_p3_n2_monic
        m_p3_n2_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p3_n2_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_2,
    m_p3_n2, polyP3]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p3_n2_irr : FpPoly.Irreducible m_p3_n2 :=
  Berlekamp.rabinTest_imp_irreducible m_p3_n2 m_p3_n2_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p3_n2 m_p3_n2_monic m_p3_n2_certificate
      m_p3_n2_certificate_check)

/-- `x^3 + 2x + 1` — irreducible over `F_3`. -/
private def m_p3_n3 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 2, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p3_n3_pos : 0 < FpPoly.degree m_p3_n3 := by decide
private theorem m_p3_n3_monic : DensePoly.Monic m_p3_n3 := by rfl

private def m_p3_n3_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 3
  powChain :=
    #[polyP3 #[0, 1], polyP3 #[2, 1], polyP3 #[1, 1], polyP3 #[0, 1]]
  bezout := #[{ left := polyP3 #[], right := polyP3 #[2] }]

set_option maxRecDepth 4096 in
private theorem m_p3_n3_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p3_n3 m_p3_n3_monic
        m_p3_n3_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p3_n3_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_3,
    m_p3_n3, polyP3]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p3_n3_irr : FpPoly.Irreducible m_p3_n3 :=
  Berlekamp.rabinTest_imp_irreducible m_p3_n3 m_p3_n3_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p3_n3 m_p3_n3_monic m_p3_n3_certificate
      m_p3_n3_certificate_check)

/-- `x^4 + 2x^3 + 2` — Conway polynomial for `GF(81)`. -/
private def m_p3_n4 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 0, 0, 2, 1]
    normalized := Or.inr (by decide) }
private theorem m_p3_n4_pos : 0 < FpPoly.degree m_p3_n4 := by decide
private theorem m_p3_n4_monic : DensePoly.Monic m_p3_n4 := by rfl

private def m_p3_n4_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 4
  powChain :=
    #[polyP3 #[0, 1], polyP3 #[0, 0, 0, 1], polyP3 #[0, 2, 1, 1],
      polyP3 #[1, 0, 2, 1], polyP3 #[0, 1]]
  bezout := #[{ left := polyP3 #[2, 1, 2], right := polyP3 #[1, 1, 0, 1] }]

set_option maxRecDepth 4096 in
private theorem m_p3_n4_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p3_n4 m_p3_n4_monic
        m_p3_n4_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p3_n4_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4,
    m_p3_n4, polyP3]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p3_n4_irr : FpPoly.Irreducible m_p3_n4 :=
  Berlekamp.rabinTest_imp_irreducible m_p3_n4 m_p3_n4_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p3_n4 m_p3_n4_monic m_p3_n4_certificate
      m_p3_n4_certificate_check)

/-- `x^6 + 2x^4 + x^2 + 2x + 2` — Conway polynomial for `GF(729)`. -/
private def m_p3_n6 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 2, 1, 0, 2, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p3_n6_pos : 0 < FpPoly.degree m_p3_n6 := by decide
private theorem m_p3_n6_monic : DensePoly.Monic m_p3_n6 := by rfl

private def m_p3_n6_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 6
  powChain :=
    #[polyP3 #[0, 1], polyP3 #[0, 0, 0, 1], polyP3 #[0, 1, 1, 0, 1],
      polyP3 #[1, 2, 0, 0, 2, 2], polyP3 #[0, 0, 0, 2, 2, 2],
      polyP3 #[2, 2, 2, 0, 1, 2], polyP3 #[0, 1]]
  bezout :=
    #[{ left := polyP3 #[2, 1, 1, 2],
        right := polyP3 #[0, 2, 0, 0, 2, 1] },
      { left := polyP3 #[1, 2, 1, 0, 1],
        right := polyP3 #[2, 1, 1, 1, 2, 1] }]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
private theorem m_p3_n6_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p3_n6 m_p3_n6_monic
        m_p3_n6_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p3_n6_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_6,
    m_p3_n6, polyP3]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
          omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · exact ⟨rfl, rfl⟩

private theorem m_p3_n6_irr : FpPoly.Irreducible m_p3_n6 :=
  Berlekamp.rabinTest_imp_irreducible m_p3_n6 m_p3_n6_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p3_n6 m_p3_n6_monic m_p3_n6_certificate
      m_p3_n6_certificate_check)

-- p = 5

/-- `x^2 + 4x + 2` — Conway polynomial for `GF(25)`. -/
private def m_p5_n2 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 4, 1]
    normalized := Or.inr (by decide) }
private theorem m_p5_n2_pos : 0 < FpPoly.degree m_p5_n2 := by decide
private theorem m_p5_n2_monic : DensePoly.Monic m_p5_n2 := by rfl

private def m_p5_n2_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyP5 #[0, 1], polyP5 #[1, 4], polyP5 #[0, 1]]
  bezout := #[{ left := polyP5 #[2], right := polyP5 #[2, 1] }]

set_option maxRecDepth 4096 in
private theorem m_p5_n2_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p5_n2 m_p5_n2_monic
        m_p5_n2_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p5_n2_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_2,
    m_p5_n2, polyP5]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p5_n2_irr : FpPoly.Irreducible m_p5_n2 :=
  Berlekamp.rabinTest_imp_irreducible m_p5_n2 m_p5_n2_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p5_n2 m_p5_n2_monic m_p5_n2_certificate
      m_p5_n2_certificate_check)

/-- `x^3 + 3x + 3` — Conway polynomial for `GF(125)`. -/
private def m_p5_n3 : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 3, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p5_n3_pos : 0 < FpPoly.degree m_p5_n3 := by decide
private theorem m_p5_n3_monic : DensePoly.Monic m_p5_n3 := by rfl

private def m_p5_n3_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 3
  powChain :=
    #[polyP5 #[0, 1], polyP5 #[4, 4, 2], polyP5 #[1, 0, 3], polyP5 #[0, 1]]
  bezout := #[{ left := polyP5 #[3, 3], right := polyP5 #[3, 2, 1] }]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem m_p5_n3_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p5_n3 m_p5_n3_monic
        m_p5_n3_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p5_n3_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_3,
    m_p5_n3, polyP5]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p5_n3_irr : FpPoly.Irreducible m_p5_n3 :=
  Berlekamp.rabinTest_imp_irreducible m_p5_n3 m_p5_n3_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p5_n3 m_p5_n3_monic m_p5_n3_certificate
      m_p5_n3_certificate_check)

/-- `x^4 + 2` — irreducible over `F_5` (matches `HexGFqField.Conformance`). -/
private def m_p5_n4 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 0, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p5_n4_pos : 0 < FpPoly.degree m_p5_n4 := by decide
private theorem m_p5_n4_monic : DensePoly.Monic m_p5_n4 := by rfl

private def m_p5_n4_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 4
  powChain :=
    #[polyP5 #[0, 1], polyP5 #[0, 3], polyP5 #[0, 4],
      polyP5 #[0, 2], polyP5 #[0, 1]]
  bezout := #[{ left := polyP5 #[3], right := polyP5 #[0, 0, 0, 4] }]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem m_p5_n4_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p5_n4 m_p5_n4_monic
        m_p5_n4_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p5_n4_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4,
    m_p5_n4, polyP5]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p5_n4_irr : FpPoly.Irreducible m_p5_n4 :=
  Berlekamp.rabinTest_imp_irreducible m_p5_n4 m_p5_n4_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p5_n4 m_p5_n4_monic m_p5_n4_certificate
      m_p5_n4_certificate_check)

/-- `x^6 + x^4 + 4x^3 + x^2 + 2` — Conway polynomial for `GF(15625)`.

`Berlekamp.checkIrreducibilityCertificateLinear` re-evaluates each pow-chain
entry by expanding `X^(p^k) mod m` as a straight-line product of `p^k`
modular multiplications.  For `(p, n) = (5, 6)` that is `5^6 = 15625`
kernel-reducible iterations per entry — far beyond practical budgets.

The incremental variant `checkIrreducibilityCertificateLinearIncremental`
uses `(X^(p^k) mod m)^p mod m` (only `p` mults per step) and discharges this
case in `n · p = 30` total multiplications. -/
private def m_p5_n6 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1, 4, 1, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p5_n6_pos : 0 < FpPoly.degree m_p5_n6 := by decide
private theorem m_p5_n6_monic : DensePoly.Monic m_p5_n6 := by rfl

private def m_p5_n6_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 6
  powChain :=
    #[polyP5 #[0, 1], polyP5 #[0, 0, 0, 0, 0, 1],
      polyP5 #[4, 4, 0, 3, 4, 2], polyP5 #[3, 0, 3, 2, 4, 1],
      polyP5 #[1, 0, 0, 2, 1, 3], polyP5 #[2, 0, 2, 3, 1, 3],
      polyP5 #[0, 1]]
  bezout :=
    #[{ left := polyP5 #[0, 4, 0, 1, 1],
        right := polyP5 #[4, 0, 0, 3, 3, 2] },
      { left := polyP5 #[4, 2, 1, 4, 3],
        right := polyP5 #[1, 4, 0, 0, 3, 2] }]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem m_p5_n6_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental m_p5_n6
        m_p5_n6_monic m_p5_n6_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    m_p5_n6_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinearIncremental,
    Berlekamp.checkPowChainLinearIncrementalStep,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_6,
    m_p5_n6, polyP5]
  constructor
  · constructor
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x hx
          have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · exact ⟨rfl, rfl⟩

private theorem m_p5_n6_irr : FpPoly.Irreducible m_p5_n6 :=
  Berlekamp.rabinTest_imp_irreducible m_p5_n6 m_p5_n6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      m_p5_n6 m_p5_n6_monic m_p5_n6_certificate
      m_p5_n6_certificate_check)

-- p = 7

/-- `x^2 + 6x + 3` — Conway polynomial for `GF(49)`. -/
private def m_p7_n2 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 1]
    normalized := Or.inr (by decide) }
private theorem m_p7_n2_pos : 0 < FpPoly.degree m_p7_n2 := by decide
private theorem m_p7_n2_monic : DensePoly.Monic m_p7_n2 := by rfl

private def m_p7_n2_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 2
  powChain := #[polyP7 #[0, 1], polyP7 #[1, 6], polyP7 #[0, 1]]
  bezout := #[{ left := polyP7 #[1], right := polyP7 #[5, 4] }]

set_option maxRecDepth 4096 in
private theorem m_p7_n2_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p7_n2 m_p7_n2_monic
        m_p7_n2_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p7_n2_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_2,
    m_p7_n2, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p7_n2_irr : FpPoly.Irreducible m_p7_n2 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n2 m_p7_n2_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p7_n2 m_p7_n2_monic m_p7_n2_certificate
      m_p7_n2_certificate_check)

/-- `x^3 + 6x^2 + 4` — Conway polynomial for `GF(343)`. -/
private def m_p7_n3 : FpPoly 7 :=
  { coeffs := #[(4 : ZMod64 7), 0, 6, 1]
    normalized := Or.inr (by decide) }
private theorem m_p7_n3_pos : 0 < FpPoly.degree m_p7_n3 := by decide
private theorem m_p7_n3_monic : DensePoly.Monic m_p7_n3 := by rfl

private def m_p7_n3_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 3
  powChain :=
    #[polyP7 #[0, 1], polyP7 #[0, 5, 3], polyP7 #[1, 1, 4], polyP7 #[0, 1]]
  bezout := #[{ left := polyP7 #[2], right := polyP7 #[0, 4] }]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem m_p7_n3_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p7_n3 m_p7_n3_monic
        m_p7_n3_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p7_n3_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_3,
    m_p7_n3, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p7_n3_irr : FpPoly.Irreducible m_p7_n3 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n3 m_p7_n3_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p7_n3 m_p7_n3_monic m_p7_n3_certificate
      m_p7_n3_certificate_check)

/-- `x^4 + 5x^2 + 4x + 3` — Conway polynomial for `GF(2401)`. -/
private def m_p7_n4 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 4, 5, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p7_n4_pos : 0 < FpPoly.degree m_p7_n4 := by decide
private theorem m_p7_n4_monic : DensePoly.Monic m_p7_n4 := by rfl

private def m_p7_n4_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 4
  powChain :=
    #[polyP7 #[0, 1], polyP7 #[5, 3, 5, 1], polyP7 #[0, 0, 3, 1],
      polyP7 #[2, 3, 6, 5], polyP7 #[0, 1]]
  bezout := #[{ left := polyP7 #[5, 3, 5], right := polyP7 #[1, 6, 5, 2] }]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 8000000 in
private theorem m_p7_n4_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinear m_p7_n4 m_p7_n4_monic
        m_p7_n4_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    m_p7_n4_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4,
    m_p7_n4, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p7_n4_irr : FpPoly.Irreducible m_p7_n4 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n4 m_p7_n4_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      m_p7_n4 m_p7_n4_monic m_p7_n4_certificate
      m_p7_n4_certificate_check)

/-- `x^6 + x^4 + 5x^3 + 4x^2 + 6x + 3` — Conway polynomial for `GF(7^6)`.

Uses the incremental Rabin certificate checker (see comment on `m_p5_n6`);
`(p, n) = (7, 6)` would require `7^6 = 117649` mults per entry on the
straight-line path, but only `n · p = 42` total mults on the incremental
path. -/
private def m_p7_n6 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 4, 5, 1, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p7_n6_pos : 0 < FpPoly.degree m_p7_n6 := by decide
private theorem m_p7_n6_monic : DensePoly.Monic m_p7_n6 := by rfl

private def m_p7_n6_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 6
  powChain :=
    #[polyP7 #[0, 1], polyP7 #[0, 4, 1, 3, 2, 6],
      polyP7 #[1, 3, 4, 5, 5], polyP7 #[6, 4, 5, 6, 0, 4],
      polyP7 #[3, 2, 5, 0, 5, 3], polyP7 #[4, 0, 6, 0, 2, 1],
      polyP7 #[0, 1]]
  bezout :=
    #[{ left := polyP7 #[6, 0, 2, 2],
        right := polyP7 #[4, 5, 0, 3, 0, 1] },
      { left := polyP7 #[1, 1, 0, 2, 3],
        right := polyP7 #[2, 1, 2, 3, 3, 1] }]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 32000000 in
private theorem m_p7_n6_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental m_p7_n6
        m_p7_n6_monic m_p7_n6_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    m_p7_n6_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinearIncremental,
    Berlekamp.checkPowChainLinearIncrementalStep,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_6,
    m_p7_n6, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x hx
          have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · exact ⟨rfl, rfl⟩

private theorem m_p7_n6_irr : FpPoly.Irreducible m_p7_n6 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n6 m_p7_n6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      m_p7_n6 m_p7_n6_monic m_p7_n6_certificate
      m_p7_n6_certificate_check)

end Hex.GFqFieldEmit

open Hex.GFqFieldEmit in
def main : IO Unit := do
  -- p = 2 (Frobenius is squaring; covers GF(4), GF(8), GF(16), GF(64)).
  emitAt prime_two  m_p2_n2 m_p2_n2_pos m_p2_n2_irr "p2/n2/typical" [1, 1] [1, 0, 1]    3
  emitAt prime_two  m_p2_n3 m_p2_n3_pos m_p2_n3_irr "p2/n3/typical" [0, 1, 1] [1, 0, 0, 1] (-2)
  emitAt prime_two  m_p2_n4 m_p2_n4_pos m_p2_n4_irr "p2/n4/typical" [1, 0, 1, 1] [0, 1, 0, 0, 1] 4
  emitAt prime_two  m_p2_n6 m_p2_n6_pos m_p2_n6_irr "p2/n6/typical" [1, 1, 0, 1] [0, 1, 1, 0, 0, 1] (-3)
  -- p = 3.
  emitAt prime_three m_p3_n2 m_p3_n2_pos m_p3_n2_irr "p3/n2/typical" [1, 2] [2, 1] (-2)
  emitAt prime_three m_p3_n3 m_p3_n3_pos m_p3_n3_irr "p3/n3/typical" [2, 1, 1] [1, 0, 2] 3
  emitAt prime_three m_p3_n4 m_p3_n4_pos m_p3_n4_irr "p3/n4/typical" [1, 2, 0, 1] [2, 0, 1, 2] (-3)
  emitAt prime_three m_p3_n6 m_p3_n6_pos m_p3_n6_irr "p3/n6/typical" [1, 0, 2, 1, 0, 2] [2, 1, 0, 0, 1, 1] 2
  -- p = 5.
  emitAt prime_five  m_p5_n2 m_p5_n2_pos m_p5_n2_irr "p5/n2/typical" [3, 2] [4, 1] 4
  emitAt prime_five  m_p5_n3 m_p5_n3_pos m_p5_n3_irr "p5/n3/typical" [2, 3, 4] [1, 0, 2] (-2)
  emitAt prime_five  m_p5_n4 m_p5_n4_pos m_p5_n4_irr "p5/n4/typical" [2, 3] [4, 1, 0, 1] (-2)
  emitAt prime_five  m_p5_n6 m_p5_n6_pos m_p5_n6_irr "p5/n6/typical" [4, 0, 1, 2, 3, 1] [1, 2, 0, 3, 0, 4] 3
  -- p = 7.
  emitAt prime_seven m_p7_n2 m_p7_n2_pos m_p7_n2_irr "p7/n2/typical" [4, 5] [6, 2] 3
  emitAt prime_seven m_p7_n3 m_p7_n3_pos m_p7_n3_irr "p7/n3/typical" [3, 6, 1] [5, 2, 4] (-2)
  emitAt prime_seven m_p7_n4 m_p7_n4_pos m_p7_n4_irr "p7/n4/typical" [1, 2, 4, 6] [5, 3, 0, 1] (-3)
  emitAt prime_seven m_p7_n6 m_p7_n6_pos m_p7_n6_irr "p7/n6/typical" [6, 0, 5, 2, 4, 1] [1, 4, 2, 0, 5, 3] 2
