/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFqField.Operations
import HexBerlekamp.RabinSoundness
import Hex.BenchOracle.Flint
import LeanBench

/-!
Benchmark registrations for `hex-gfq-field`.

This Phase 4 benchmark surface measures the executable finite-field wrapper over
`F_7[x] / (f)`. The smoke path uses small moduli with kernel-checked Rabin
certificates. Larger scientific rungs use committed sparse trinomials whose
Rabin tests run in compiled `prep`; the soundness theorem turns each successful
test into the irreducibility witness required by `GFqField`. Construction is
hoisted through `prep`, and timed targets return compact polynomial checksums.

Scientific registrations:

* `runOfPolyReprChecksum`: field construction followed by projection,
  `O(n^2)`.
* `runAddChecksum`: field addition on canonical representatives, `O(n)`.
* `runMulChecksum`: field multiplication on canonical representatives,
  `O(n^2)`.
* `runNegSubChecksum`: field negation and subtraction, `O(n)`.
* `runPowChecksum`: square-and-multiply exponentiation, `O(n^2 log n)`.
* `runInvDivChecksum`: extended-gcd inversion and division, `O(n^2)`.
* `runZPowChecksum`: signed square-and-multiply exponentiation,
  `O(n^2 log n)`.
* `runFrobChecksum`: Frobenius as the `p`-th power, `O(n^2 log p)`.

Informational external comparator (FLINT `fq_default` via the shared
persistent-subprocess driver from `scripts/oracle/flint_bench_driver.py`):

* `runFlintOfPolyReprChecksum*` ↔ `runOfPolyReprChecksum`
  (`fq_default.reduce`) for dense canonical reduction.
* `runFlintAddChecksum*`, `runFlintMulChecksum*`, and
  `runFlintNegSubChecksum*` ↔ the field-arithmetic targets
  (`fq_default.add`, `mul`, `neg`, `sub`).
* `runFlintPowChecksum*`, `runFlintZPowChecksum*`, and
  `runFlintFrobChecksum*` ↔ the field-exponentiation targets
  (`fq_default.pow`, with natural, signed, and `p`-th exponents).
* `runFlintInvDivChecksum*` ↔ field inversion and division
  (`fq_default.inv`, `div`).
-/

namespace Hex
namespace GFqFieldBench

open GFqField

private instance benchBoundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private theorem one_ne_zero_seven : (1 : ZMod64 7) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 7) 1 0).mp h
  simp at hm

private def noNontrivialDivisors (p : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
      noNontrivialDivisors p k &&
        if k + 1 = 1 ∨ k + 1 = p then true else p % (k + 1) != 0

private theorem noNontrivialDivisors_sound {p n m : Nat} (hp0 : 0 < p)
    (hcheck : noNontrivialDivisors p n = true) (hmn : m ≤ n) (hm : m ∣ p) :
    m = 1 ∨ m = p := by
  induction n generalizing m with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rcases hm with ⟨c, hc⟩
      omega
  | succ n ih =>
      have hparts :
          noNontrivialDivisors p n = true ∧
            ((n = 0 ∨ n + 1 = p) ∨ ¬p % (n + 1) = 0) := by
        simpa [noNontrivialDivisors] using hcheck
      by_cases hmle : m ≤ n
      · exact ih hparts.1 hmle hm
      · have hmEq : m = n + 1 := by omega
        subst m
        rcases hparts.2 with hleft | hnmod
        · rcases hleft with hn0 | hnp
          · left
            omega
          · exact Or.inr hnp
        · have hmod : p % (n + 1) = 0 := Nat.mod_eq_zero_of_dvd hm
          contradiction

set_option maxRecDepth 100000 in
private theorem prime_seven : Hex.Nat.Prime 7 := by
  constructor
  · decide
  · intro m hm
    exact noNontrivialDivisors_sound (p := 7) (n := 7) (m := m)
      (by decide) (by decide) (Nat.le_of_dvd (by decide : 0 < 7) hm) hm

instance : Hashable (ZMod64 7) where
  hash a := hash a.toNat

instance : Hashable (FpPoly 7) where
  hash f := hash f.toArray

private instance primeModulusSeven : ZMod64.PrimeModulus 7 :=
  ZMod64.primeModulusOfPrime prime_seven

/-- Deterministic coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : ZMod64 7 :=
  ZMod64.ofNat 7 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 7

/-- Deterministic dense polynomial over the benchmark prime field. -/
def densePoly (n salt : Nat) : FpPoly 7 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

private def polyP7 (coeffs : Array Nat) : FpPoly 7 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 7 n))

private theorem maxProperDiv_2 : Berlekamp.maximalProperDivisors 2 = [1] := by decide
private theorem maxProperDiv_3 : Berlekamp.maximalProperDivisors 3 = [1] := by decide
private theorem maxProperDiv_4 : Berlekamp.maximalProperDivisors 4 = [2] := by decide
private theorem maxProperDiv_5 : Berlekamp.maximalProperDivisors 5 = [1] := by decide
private theorem maxProperDiv_6 : Berlekamp.maximalProperDivisors 6 = [2, 3] := by decide
private theorem maxProperDiv_8 : Berlekamp.maximalProperDivisors 8 = [4] := by decide

/-! # Certificate-backed benchmark moduli -/

/-- `x^2 + 6x + 3` over `F_7`. -/
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

/-- `x^3 + 6x^2 + 4` over `F_7`. -/
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

/-- `x^4 + 5x^2 + 4x + 3` over `F_7`. -/
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

/-- `x^5 + x + 4` over `F_7`. -/
private def m_p7_n5 : FpPoly 7 :=
  { coeffs := #[(4 : ZMod64 7), 1, 0, 0, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p7_n5_pos : 0 < FpPoly.degree m_p7_n5 := by decide
private theorem m_p7_n5_monic : DensePoly.Monic m_p7_n5 := by rfl

private def m_p7_n5_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 5
  powChain :=
    #[polyP7 #[0, 1], polyP7 #[0, 0, 3, 6], polyP7 #[6, 3, 0, 2, 4],
      polyP7 #[4, 2, 4, 4, 5], polyP7 #[4, 1, 0, 2, 5], polyP7 #[0, 1]]
  bezout := #[{ left := polyP7 #[2], right := polyP7 #[2, 6, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem m_p7_n5_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental m_p7_n5
        m_p7_n5_monic m_p7_n5_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    m_p7_n5_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinearIncremental,
    Berlekamp.checkPowChainLinearIncrementalStep,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_5,
    m_p7_n5, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x hx
          have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p7_n5_irr : FpPoly.Irreducible m_p7_n5 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n5 m_p7_n5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      m_p7_n5 m_p7_n5_monic m_p7_n5_certificate
      m_p7_n5_certificate_check)

/-- `x^6 + x^4 + 5x^3 + 4x^2 + 6x + 3` over `F_7`. -/
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

/-- `x^8 + x + 3` over `F_7`. -/
private def m_p7_n8 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 1, 0, 0, 0, 0, 0, 0, 1]
    normalized := Or.inr (by decide) }
private theorem m_p7_n8_pos : 0 < FpPoly.degree m_p7_n8 := by decide
private theorem m_p7_n8_monic : DensePoly.Monic m_p7_n8 := by rfl

private def m_p7_n8_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 8
  powChain :=
    #[polyP7 #[0, 1], polyP7 #[0, 0, 0, 0, 0, 0, 0, 1],
      polyP7 #[0, 1, 2, 4, 1, 2, 4, 1], polyP7 #[0, 1, 3, 2, 6, 4, 5, 1],
      polyP7 #[0, 1, 5, 4, 6, 2, 3, 1], polyP7 #[0, 1, 1, 1, 1, 1, 1, 1],
      polyP7 #[0, 1, 4, 2, 1, 4, 2, 1], polyP7 #[0, 1, 6, 1, 6, 1, 6, 1],
      polyP7 #[0, 1]]
  bezout :=
    #[{ left := polyP7 #[5, 3, 6, 0, 6, 3, 1],
        right := polyP7 #[0, 3, 1, 1, 4, 3, 0, 6] }]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 80000000 in
private theorem m_p7_n8_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental m_p7_n8 m_p7_n8_monic
        m_p7_n8_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    m_p7_n8_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinearIncremental,
    Berlekamp.checkPowChainLinearIncrementalStep,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_8,
    m_p7_n8, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x hx
          have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨
              x = 6 ∨ x = 7 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem m_p7_n8_irr : FpPoly.Irreducible m_p7_n8 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n8 m_p7_n8_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      m_p7_n8 m_p7_n8_monic m_p7_n8_certificate
      m_p7_n8_certificate_check)

/-! ## Scientific-only runtime-checked moduli

The high-degree trinomials below are checked for irreducibility during compiled
benchmark preparation. This uses the same proven
`rabinTest_imp_irreducible` route as the static certificates above, while
avoiding the large kernel reductions that exhausted GitHub-hosted CI in
PR #2790.
-/

/-- Sparse monic polynomial `x^n + x^k + constant` over `F_7`. -/
private def sparseModulus (n k constant : Nat) : FpPoly 7 :=
  DensePoly.ofCoeffs <| (Array.range (n + 1)).map fun i =>
    if i = 0 then ZMod64.ofNat 7 constant
    else if i = k ∨ i = n then 1 else 0

private theorem sparseModulus_coeff_top {n k constant : Nat} (hn : 0 < n) :
    (sparseModulus n k constant).coeff n = 1 := by
  rw [sparseModulus, DensePoly.coeff_ofCoeffs,
    Array.getD_eq_getD_getElem?, Array.getElem?_map]
  have hlt : n < (Array.range (n + 1)).size := by simp
  rw [Array.getElem?_eq_getElem hlt]
  simp [Nat.ne_of_gt hn]

private theorem sparseModulus_size {n k constant : Nat} (hn : 0 < n) :
    (sparseModulus n k constant).size = n + 1 := by
  apply Nat.le_antisymm
  · exact Nat.le_trans (DensePoly.size_ofCoeffs_le _) (by simp)
  · apply Nat.succ_le_of_lt
    refine Nat.lt_of_not_ge fun hle => ?_
    have hzero := DensePoly.coeff_eq_zero_of_size_le
      (sparseModulus n k constant) hle
    rw [sparseModulus_coeff_top hn] at hzero
    exact (by decide : (1 : ZMod64 7) ≠ 0) hzero

private theorem sparseModulus_degree {n k constant : Nat} (hn : 0 < n) :
    FpPoly.degree (sparseModulus n k constant) = n := by
  change (sparseModulus n k constant).degree?.getD 0 = n
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by
    rw [sparseModulus_size hn]
    omega)]
  simp [sparseModulus_size hn]

private theorem sparseModulus_monic {n k constant : Nat} (hn : 0 < n) :
    DensePoly.Monic (sparseModulus n k constant) := by
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _ (by
    rw [sparseModulus_size hn]
    omega)]
  rw [sparseModulus_size hn]
  exact sparseModulus_coeff_top (n := n) (k := k) (constant := constant) hn

/-- A modulus together with its positive-degree and irreducibility
witnesses, used by the benchmark prep functions to dispatch on the
parameter `n` and select the correct per-degree fixture. -/
private structure ModulusBundle where
  modulus : FpPoly 7
  pos : 0 < FpPoly.degree modulus
  irr : FpPoly.Irreducible modulus

private instance : Inhabited ModulusBundle :=
  ⟨⟨m_p7_n2, m_p7_n2_pos, m_p7_n2_irr⟩⟩

/-- Run the Rabin test in compiled benchmark preparation and, on success,
package its proven irreducibility result. This keeps large certificate
reduction out of kernel elaboration while retaining checked field inputs. -/
private def runtimeCheckedBundle (f : FpPoly 7) (hpos : 0 < FpPoly.degree f)
    (hmonic : DensePoly.Monic f) : Option ModulusBundle :=
  if h : Berlekamp.rabinTest f hmonic = true then
    some ⟨f, hpos, Berlekamp.rabinTest_imp_irreducible f hmonic h⟩
  else
    none

private def runtimeCheckedSparseBundle (n k constant : Nat) (hn : 0 < n) :
    Option ModulusBundle :=
  runtimeCheckedBundle (sparseModulus n k constant) (by
      rw [sparseModulus_degree hn]
      exact hn)
    (sparseModulus_monic hn)

/-- Require the scheduled sparse modulus to pass Rabin's test. A rejected
fixture is a benchmark configuration error and must be visible rather than
silently changing the field degree attached to the harness parameter. -/
private def checkedSparseBundle (n k constant : Nat) (hn : 0 < n) :
    ModulusBundle :=
  match runtimeCheckedSparseBundle n k constant hn with
  | some bundle => bundle
  | none => panic! "scheduled GFqField modulus failed the Rabin test"

/-- Look up the per-degree modulus fixture for benchmark parameter `n`.
The match enumerates the union of `paramSchedule` entries used by the
registrations below; any `n` outside that schedule falls back to a
degree-2 fixture so that the function remains total. -/
private def bundleForN (n : Nat) : ModulusBundle :=
  match n with
  | 2 => ⟨m_p7_n2, m_p7_n2_pos, m_p7_n2_irr⟩
  | 3 => ⟨m_p7_n3, m_p7_n3_pos, m_p7_n3_irr⟩
  | 4 => ⟨m_p7_n4, m_p7_n4_pos, m_p7_n4_irr⟩
  | 5 => ⟨m_p7_n5, m_p7_n5_pos, m_p7_n5_irr⟩
  | 6 => ⟨m_p7_n6, m_p7_n6_pos, m_p7_n6_irr⟩
  | 8 => ⟨m_p7_n8, m_p7_n8_pos, m_p7_n8_irr⟩
  | 432 => checkedSparseBundle 432 54 3 (by omega)
  | 600 => checkedSparseBundle 600 75 3 (by omega)
  | 768 => checkedSparseBundle 768 96 3 (by omega)
  | 936 => checkedSparseBundle 936 324 3 (by omega)
  | 1216 => checkedSparseBundle 1216 144 3 (by omega)
  | _ => ⟨m_p7_n2, m_p7_n2_pos, m_p7_n2_irr⟩

/-- Degree 2 is a low-cost manual check. The scientific tail spans more than a
factor of `e`, and every tail degree is congruent to `40` modulo `56`, so
`densePoly` supplies the same coefficient pattern while fixed word and dispatch
costs amortize. Harness verification uses parameters 0 and 1 independently of
this schedule. -/
private def scientificSchedule : Array Nat := #[2, 432, 600, 768, 936, 1216]

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly (f : FpPoly 7) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum over an integer coefficient list returned by FLINT. -/
def checksumIntCoeffs (coeffs : List Int) : UInt64 :=
  coeffs.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Encode an `FpPoly 7` as a JSON coefficient list (ascending degree) over
non-negative integer representatives in `[0, 7)`. -/
def fpPolySevenToFlintJson (f : FpPoly 7) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson <|
    f.toArray.toList.map fun coeff => Int.ofNat coeff.toNat

/-- Decode a FLINT `fq_default` coefficient-list reply and checksum it. -/
def checksumFlintCoeffReply (reply : Lean.Json) : IO UInt64 := do
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts reply
  return checksumIntCoeffs coeffs

/-- Prepared input for field construction/projection benchmarks. -/
structure OfPolyInput where
  modulus : FpPoly 7
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  poly : FpPoly 7

/-- Prepared input for binary field operations. -/
structure BinaryInput where
  modulus : FpPoly 7
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  lhs : FiniteField modulus modulusDegreePos prime_seven modulusIrreducible
  rhs : FiniteField modulus modulusDegreePos prime_seven modulusIrreducible

/-- Prepared input for unary field operations. -/
structure UnaryInput where
  modulus : FpPoly 7
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  value : FiniteField modulus modulusDegreePos prime_seven modulusIrreducible

/-- Prepared input for field exponentiation. -/
structure PowInput where
  modulus : FpPoly 7
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  value : FiniteField modulus modulusDegreePos prime_seven modulusIrreducible
  exponent : Nat

/-- Prepared input for signed field exponentiation. -/
structure ZPowInput where
  modulus : FpPoly 7
  modulusDegreePos : 0 < FpPoly.degree modulus
  modulusIrreducible : FpPoly.Irreducible modulus
  value : FiniteField modulus modulusDegreePos prime_seven modulusIrreducible
  exponent : Int

instance : Hashable OfPolyInput where
  hash input := mixHash (hash input.modulus) (hash input.poly)

instance : Hashable BinaryInput where
  hash input :=
    mixHash
      (mixHash (hash input.modulus) (hash <| repr input.lhs))
      (hash <| repr input.rhs)

instance : Hashable UnaryInput where
  hash input := mixHash (hash input.modulus) (hash <| repr input.value)

instance : Hashable PowInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.value)) (hash input.exponent)

instance : Hashable ZPowInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.value)) (hash input.exponent)

/-- Per-parameter fixture for field construction. -/
def prepOfPolyInput (n : Nat) : OfPolyInput :=
  let b := bundleForN n
  { modulus := b.modulus
    modulusDegreePos := b.pos
    modulusIrreducible := b.irr
    poly := densePoly (2 * (n + 1) + 1) 23 }

/-- Per-parameter fixture for field binary operations. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  let b := bundleForN n
  { modulus := b.modulus
    modulusDegreePos := b.pos
    modulusIrreducible := b.irr
    lhs := ofPoly b.modulus b.pos prime_seven b.irr (densePoly (n + 1) 37)
    rhs := ofPoly b.modulus b.pos prime_seven b.irr (densePoly (n + 1) 71) }

/-- Per-parameter fixture for field unary operations. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  let input := prepBinaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    modulusIrreducible := input.modulusIrreducible
    value := input.lhs }

/-- Exponent with all bits set at the benchmark parameter's bit length. -/
def denseExponent (n : Nat) : Nat :=
  2 ^ (Nat.log2 (n + 1) + 1) - 1

/-- Per-parameter fixture for field exponentiation. -/
def prepPowInput (n : Nat) : PowInput :=
  let input := prepUnaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    modulusIrreducible := input.modulusIrreducible
    value := input.value
    exponent := denseExponent n }

/-- Per-parameter fixture for signed field exponentiation. -/
def prepZPowInput (n : Nat) : ZPowInput :=
  let input := prepUnaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    modulusIrreducible := input.modulusIrreducible
    value := input.value
    exponent := -Int.ofNat (denseExponent n) }

/-- Benchmark target: construct and project a finite-field representative. -/
def runOfPolyReprChecksum (input : OfPolyInput) : UInt64 :=
  checksumPoly <| repr <| ofPoly input.modulus input.modulusDegreePos
    prime_seven input.modulusIrreducible input.poly

/-- Benchmark target: field addition checksum. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| repr (input.lhs + input.rhs)

/-- Benchmark target: field multiplication checksum. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| repr (input.lhs * input.rhs)

/-- Benchmark target: field negation and subtraction checksum. -/
def runNegSubChecksum (input : BinaryInput) : UInt64 :=
  mixHash (checksumPoly <| repr (-input.lhs)) (checksumPoly <| repr (input.lhs - input.rhs))

/-- Benchmark target: field exponentiation checksum. -/
def runPowChecksum (input : PowInput) : UInt64 :=
  checksumPoly <| repr (input.value ^ input.exponent)

/-- Benchmark target: field inverse and division checksum. -/
def runInvDivChecksum (input : BinaryInput) : UInt64 :=
  mixHash (checksumPoly <| repr input.lhs⁻¹) (checksumPoly <| repr (input.lhs / input.rhs))

/-- Benchmark target: signed field exponentiation checksum. -/
def runZPowChecksum (input : ZPowInput) : UInt64 :=
  checksumPoly <| repr (zpow input.value input.exponent)

/-- Benchmark target: Frobenius checksum. -/
def runFrobChecksum (input : UnaryInput) : UInt64 :=
  checksumPoly <| repr (frob input.value)

def runFlintOfPolyReprChecksum (input : OfPolyInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fq_default" "reduce"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson input.poly)]
  checksumFlintCoeffReply result

/-- Drive FLINT `fq_default` `add` on a `BinaryInput` (shared modulus plus the
two operands `lhs`, `rhs`) and return a checksum of the FLINT reply, for
comparison against the native `runAddChecksum` target at the same rung. -/
def runFlintAddChecksum (input : BinaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fq_default" "add"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.lhs)),
      ("b", fpPolySevenToFlintJson (repr input.rhs))]
  checksumFlintCoeffReply result

/-- Drive FLINT `fq_default` `mul` on a `BinaryInput` (shared modulus plus the
two operands `lhs`, `rhs`) and return a checksum of the FLINT reply, for
comparison against the native `runMulChecksum` target at the same rung. -/
def runFlintMulChecksum (input : BinaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fq_default" "mul"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.lhs)),
      ("b", fpPolySevenToFlintJson (repr input.rhs))]
  checksumFlintCoeffReply result

/-- Drive two FLINT `fq_default` operations on a `BinaryInput` — `neg` on `lhs`
and `sub` on `lhs - rhs` over the shared modulus — and return the `mixHash` of
their two reply checksums, for comparison against the native target at the same
rung. -/
def runFlintNegSubChecksum (input : BinaryInput) : IO UInt64 := do
  let negResult ← Hex.BenchOracle.Flint.runOp "fq_default" "neg"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.lhs))]
  let subResult ← Hex.BenchOracle.Flint.runOp "fq_default" "sub"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.lhs)),
      ("b", fpPolySevenToFlintJson (repr input.rhs))]
  return mixHash (← checksumFlintCoeffReply negResult) (← checksumFlintCoeffReply subResult)

/-- Drive FLINT `fq_default` `pow` on a `PowInput` (modulus, base `value`, and a
natural-number `exponent`) and return a checksum of the FLINT reply, for
comparison against the native `runPowChecksum` target at the same rung. -/
def runFlintPowChecksum (input : PowInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fq_default" "pow"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.value)),
      ("exponent", Lean.Json.num (Lean.JsonNumber.fromNat input.exponent))]
  checksumFlintCoeffReply result

/-- Drive two FLINT `fq_default` operations on a `BinaryInput` — `inv` on `lhs`
and `div` on `lhs / rhs` over the shared modulus — and return the `mixHash` of
their two reply checksums, for comparison against the native target at the same
rung. -/
def runFlintInvDivChecksum (input : BinaryInput) : IO UInt64 := do
  let invResult ← Hex.BenchOracle.Flint.runOp "fq_default" "inv"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.lhs))]
  let divResult ← Hex.BenchOracle.Flint.runOp "fq_default" "div"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.lhs)),
      ("b", fpPolySevenToFlintJson (repr input.rhs))]
  return mixHash (← checksumFlintCoeffReply invResult) (← checksumFlintCoeffReply divResult)

/-- Drive FLINT `fq_default` `pow` on a `ZPowInput` (modulus, base `value`, and a
signed integer `exponent`) and return a checksum of the FLINT reply, for
comparison against the native `runZPowChecksum` target at the same rung. -/
def runFlintZPowChecksum (input : ZPowInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fq_default" "pow"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.value)),
      ("exponent", Lean.Json.num (Lean.JsonNumber.fromInt input.exponent))]
  checksumFlintCoeffReply result

/-- Drive the Frobenius map as FLINT `fq_default` `pow` with the fixed exponent
`p = 7` on a `UnaryInput` (modulus and base `value`) and return a checksum of the
FLINT reply, for comparison against the native `runFrobChecksum` target at the
same rung. -/
def runFlintFrobChecksum (input : UnaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fq_default" "pow"
    #[("p", (7 : Lean.Json)),
      ("modulus", fpPolySevenToFlintJson input.modulus),
      ("a", fpPolySevenToFlintJson (repr input.value)),
      ("exponent", Lean.Json.num (Lean.JsonNumber.fromNat 7))]
  checksumFlintCoeffReply result

/-! Per-rung wrappers for paired fixed-benchmark registrations. Each `runFooN`
calls the Hex target on the prepared fixture, while each `runFlintFooN` calls
FLINT `fq_default` on the same modulus and operands. The rung ladder reuses the
certificate-checked `#[2, 3, 4, 5, 6, 8]` schedule so the headline report can
record raw and overhead-adjusted ratios for every Phase-4 input family without
adding larger certificate elaboration to the normal bench module. -/

/-- Read fixed Hex inputs through runtime state so the batching harness cannot
turn the pure target into a compile-time constant. -/
@[noinline] private def runFixed (f : α → UInt64) (input : IO.Ref α) : IO UInt64 := do
  let value ← input.get
  input.set value
  return f value

private instance : Inhabited OfPolyInput := ⟨prepOfPolyInput 2⟩
private instance : Inhabited BinaryInput := ⟨prepBinaryInput 2⟩
private instance : Inhabited PowInput := ⟨prepPowInput 2⟩
private instance : Inhabited ZPowInput := ⟨prepZPowInput 2⟩
private instance : Inhabited UnaryInput := ⟨prepUnaryInput 2⟩

private initialize fixedOfPoly2 : IO.Ref OfPolyInput ← IO.mkRef (prepOfPolyInput 2)
private initialize fixedOfPoly3 : IO.Ref OfPolyInput ← IO.mkRef (prepOfPolyInput 3)
private initialize fixedOfPoly4 : IO.Ref OfPolyInput ← IO.mkRef (prepOfPolyInput 4)
private initialize fixedOfPoly5 : IO.Ref OfPolyInput ← IO.mkRef (prepOfPolyInput 5)
private initialize fixedOfPoly6 : IO.Ref OfPolyInput ← IO.mkRef (prepOfPolyInput 6)
private initialize fixedOfPoly8 : IO.Ref OfPolyInput ← IO.mkRef (prepOfPolyInput 8)

private initialize fixedBinary2 : IO.Ref BinaryInput ← IO.mkRef (prepBinaryInput 2)
private initialize fixedBinary3 : IO.Ref BinaryInput ← IO.mkRef (prepBinaryInput 3)
private initialize fixedBinary4 : IO.Ref BinaryInput ← IO.mkRef (prepBinaryInput 4)
private initialize fixedBinary5 : IO.Ref BinaryInput ← IO.mkRef (prepBinaryInput 5)
private initialize fixedBinary6 : IO.Ref BinaryInput ← IO.mkRef (prepBinaryInput 6)
private initialize fixedBinary8 : IO.Ref BinaryInput ← IO.mkRef (prepBinaryInput 8)

private initialize fixedPow2 : IO.Ref PowInput ← IO.mkRef (prepPowInput 2)
private initialize fixedPow3 : IO.Ref PowInput ← IO.mkRef (prepPowInput 3)
private initialize fixedPow4 : IO.Ref PowInput ← IO.mkRef (prepPowInput 4)
private initialize fixedPow5 : IO.Ref PowInput ← IO.mkRef (prepPowInput 5)
private initialize fixedPow6 : IO.Ref PowInput ← IO.mkRef (prepPowInput 6)
private initialize fixedPow8 : IO.Ref PowInput ← IO.mkRef (prepPowInput 8)

private initialize fixedZPow2 : IO.Ref ZPowInput ← IO.mkRef (prepZPowInput 2)
private initialize fixedZPow3 : IO.Ref ZPowInput ← IO.mkRef (prepZPowInput 3)
private initialize fixedZPow4 : IO.Ref ZPowInput ← IO.mkRef (prepZPowInput 4)
private initialize fixedZPow5 : IO.Ref ZPowInput ← IO.mkRef (prepZPowInput 5)
private initialize fixedZPow6 : IO.Ref ZPowInput ← IO.mkRef (prepZPowInput 6)
private initialize fixedZPow8 : IO.Ref ZPowInput ← IO.mkRef (prepZPowInput 8)

private initialize fixedUnary2 : IO.Ref UnaryInput ← IO.mkRef (prepUnaryInput 2)
private initialize fixedUnary3 : IO.Ref UnaryInput ← IO.mkRef (prepUnaryInput 3)
private initialize fixedUnary4 : IO.Ref UnaryInput ← IO.mkRef (prepUnaryInput 4)
private initialize fixedUnary5 : IO.Ref UnaryInput ← IO.mkRef (prepUnaryInput 5)
private initialize fixedUnary6 : IO.Ref UnaryInput ← IO.mkRef (prepUnaryInput 6)
private initialize fixedUnary8 : IO.Ref UnaryInput ← IO.mkRef (prepUnaryInput 8)

def runOfPoly2 : Unit → IO UInt64 := fun _ => runFixed runOfPolyReprChecksum fixedOfPoly2
def runFlintOfPoly2 : Unit → IO UInt64 := fun _ => runFlintOfPolyReprChecksum (prepOfPolyInput 2)
def runOfPoly3 : Unit → IO UInt64 := fun _ => runFixed runOfPolyReprChecksum fixedOfPoly3
def runFlintOfPoly3 : Unit → IO UInt64 := fun _ => runFlintOfPolyReprChecksum (prepOfPolyInput 3)
def runOfPoly4 : Unit → IO UInt64 := fun _ => runFixed runOfPolyReprChecksum fixedOfPoly4
def runFlintOfPoly4 : Unit → IO UInt64 := fun _ => runFlintOfPolyReprChecksum (prepOfPolyInput 4)
def runOfPoly5 : Unit → IO UInt64 := fun _ => runFixed runOfPolyReprChecksum fixedOfPoly5
def runFlintOfPoly5 : Unit → IO UInt64 := fun _ => runFlintOfPolyReprChecksum (prepOfPolyInput 5)
def runOfPoly6 : Unit → IO UInt64 := fun _ => runFixed runOfPolyReprChecksum fixedOfPoly6
def runFlintOfPoly6 : Unit → IO UInt64 := fun _ => runFlintOfPolyReprChecksum (prepOfPolyInput 6)
def runOfPoly8 : Unit → IO UInt64 := fun _ => runFixed runOfPolyReprChecksum fixedOfPoly8
def runFlintOfPoly8 : Unit → IO UInt64 := fun _ => runFlintOfPolyReprChecksum (prepOfPolyInput 8)

def runAdd2 : Unit → IO UInt64 := fun _ => runFixed runAddChecksum fixedBinary2
def runFlintAdd2 : Unit → IO UInt64 := fun _ => runFlintAddChecksum (prepBinaryInput 2)
def runAdd3 : Unit → IO UInt64 := fun _ => runFixed runAddChecksum fixedBinary3
def runFlintAdd3 : Unit → IO UInt64 := fun _ => runFlintAddChecksum (prepBinaryInput 3)
def runAdd4 : Unit → IO UInt64 := fun _ => runFixed runAddChecksum fixedBinary4
def runFlintAdd4 : Unit → IO UInt64 := fun _ => runFlintAddChecksum (prepBinaryInput 4)
def runAdd5 : Unit → IO UInt64 := fun _ => runFixed runAddChecksum fixedBinary5
def runFlintAdd5 : Unit → IO UInt64 := fun _ => runFlintAddChecksum (prepBinaryInput 5)
def runAdd6 : Unit → IO UInt64 := fun _ => runFixed runAddChecksum fixedBinary6
def runFlintAdd6 : Unit → IO UInt64 := fun _ => runFlintAddChecksum (prepBinaryInput 6)
def runAdd8 : Unit → IO UInt64 := fun _ => runFixed runAddChecksum fixedBinary8
def runFlintAdd8 : Unit → IO UInt64 := fun _ => runFlintAddChecksum (prepBinaryInput 8)

def runMul2 : Unit → IO UInt64 := fun _ => runFixed runMulChecksum fixedBinary2
def runFlintMul2 : Unit → IO UInt64 := fun _ => runFlintMulChecksum (prepBinaryInput 2)
def runMul3 : Unit → IO UInt64 := fun _ => runFixed runMulChecksum fixedBinary3
def runFlintMul3 : Unit → IO UInt64 := fun _ => runFlintMulChecksum (prepBinaryInput 3)
def runMul4 : Unit → IO UInt64 := fun _ => runFixed runMulChecksum fixedBinary4
def runFlintMul4 : Unit → IO UInt64 := fun _ => runFlintMulChecksum (prepBinaryInput 4)
def runMul5 : Unit → IO UInt64 := fun _ => runFixed runMulChecksum fixedBinary5
def runFlintMul5 : Unit → IO UInt64 := fun _ => runFlintMulChecksum (prepBinaryInput 5)
def runMul6 : Unit → IO UInt64 := fun _ => runFixed runMulChecksum fixedBinary6
def runFlintMul6 : Unit → IO UInt64 := fun _ => runFlintMulChecksum (prepBinaryInput 6)
def runMul8 : Unit → IO UInt64 := fun _ => runFixed runMulChecksum fixedBinary8
def runFlintMul8 : Unit → IO UInt64 := fun _ => runFlintMulChecksum (prepBinaryInput 8)

def runNegSub2 : Unit → IO UInt64 := fun _ => runFixed runNegSubChecksum fixedBinary2
def runFlintNegSub2 : Unit → IO UInt64 := fun _ => runFlintNegSubChecksum (prepBinaryInput 2)
def runNegSub3 : Unit → IO UInt64 := fun _ => runFixed runNegSubChecksum fixedBinary3
def runFlintNegSub3 : Unit → IO UInt64 := fun _ => runFlintNegSubChecksum (prepBinaryInput 3)
def runNegSub4 : Unit → IO UInt64 := fun _ => runFixed runNegSubChecksum fixedBinary4
def runFlintNegSub4 : Unit → IO UInt64 := fun _ => runFlintNegSubChecksum (prepBinaryInput 4)
def runNegSub5 : Unit → IO UInt64 := fun _ => runFixed runNegSubChecksum fixedBinary5
def runFlintNegSub5 : Unit → IO UInt64 := fun _ => runFlintNegSubChecksum (prepBinaryInput 5)
def runNegSub6 : Unit → IO UInt64 := fun _ => runFixed runNegSubChecksum fixedBinary6
def runFlintNegSub6 : Unit → IO UInt64 := fun _ => runFlintNegSubChecksum (prepBinaryInput 6)
def runNegSub8 : Unit → IO UInt64 := fun _ => runFixed runNegSubChecksum fixedBinary8
def runFlintNegSub8 : Unit → IO UInt64 := fun _ => runFlintNegSubChecksum (prepBinaryInput 8)

def runPow2 : Unit → IO UInt64 := fun _ => runFixed runPowChecksum fixedPow2
def runFlintPow2 : Unit → IO UInt64 := fun _ => runFlintPowChecksum (prepPowInput 2)
def runPow3 : Unit → IO UInt64 := fun _ => runFixed runPowChecksum fixedPow3
def runFlintPow3 : Unit → IO UInt64 := fun _ => runFlintPowChecksum (prepPowInput 3)
def runPow4 : Unit → IO UInt64 := fun _ => runFixed runPowChecksum fixedPow4
def runFlintPow4 : Unit → IO UInt64 := fun _ => runFlintPowChecksum (prepPowInput 4)
def runPow5 : Unit → IO UInt64 := fun _ => runFixed runPowChecksum fixedPow5
def runFlintPow5 : Unit → IO UInt64 := fun _ => runFlintPowChecksum (prepPowInput 5)
def runPow6 : Unit → IO UInt64 := fun _ => runFixed runPowChecksum fixedPow6
def runFlintPow6 : Unit → IO UInt64 := fun _ => runFlintPowChecksum (prepPowInput 6)
def runPow8 : Unit → IO UInt64 := fun _ => runFixed runPowChecksum fixedPow8
def runFlintPow8 : Unit → IO UInt64 := fun _ => runFlintPowChecksum (prepPowInput 8)

def runInvDiv2 : Unit → IO UInt64 := fun _ => runFixed runInvDivChecksum fixedBinary2
def runFlintInvDiv2 : Unit → IO UInt64 := fun _ => runFlintInvDivChecksum (prepBinaryInput 2)
def runInvDiv3 : Unit → IO UInt64 := fun _ => runFixed runInvDivChecksum fixedBinary3
def runFlintInvDiv3 : Unit → IO UInt64 := fun _ => runFlintInvDivChecksum (prepBinaryInput 3)
def runInvDiv4 : Unit → IO UInt64 := fun _ => runFixed runInvDivChecksum fixedBinary4
def runFlintInvDiv4 : Unit → IO UInt64 := fun _ => runFlintInvDivChecksum (prepBinaryInput 4)
def runInvDiv5 : Unit → IO UInt64 := fun _ => runFixed runInvDivChecksum fixedBinary5
def runFlintInvDiv5 : Unit → IO UInt64 := fun _ => runFlintInvDivChecksum (prepBinaryInput 5)
def runInvDiv6 : Unit → IO UInt64 := fun _ => runFixed runInvDivChecksum fixedBinary6
def runFlintInvDiv6 : Unit → IO UInt64 := fun _ => runFlintInvDivChecksum (prepBinaryInput 6)
def runInvDiv8 : Unit → IO UInt64 := fun _ => runFixed runInvDivChecksum fixedBinary8
def runFlintInvDiv8 : Unit → IO UInt64 := fun _ => runFlintInvDivChecksum (prepBinaryInput 8)

def runZPow2 : Unit → IO UInt64 := fun _ => runFixed runZPowChecksum fixedZPow2
def runFlintZPow2 : Unit → IO UInt64 := fun _ => runFlintZPowChecksum (prepZPowInput 2)
def runZPow3 : Unit → IO UInt64 := fun _ => runFixed runZPowChecksum fixedZPow3
def runFlintZPow3 : Unit → IO UInt64 := fun _ => runFlintZPowChecksum (prepZPowInput 3)
def runZPow4 : Unit → IO UInt64 := fun _ => runFixed runZPowChecksum fixedZPow4
def runFlintZPow4 : Unit → IO UInt64 := fun _ => runFlintZPowChecksum (prepZPowInput 4)
def runZPow5 : Unit → IO UInt64 := fun _ => runFixed runZPowChecksum fixedZPow5
def runFlintZPow5 : Unit → IO UInt64 := fun _ => runFlintZPowChecksum (prepZPowInput 5)
def runZPow6 : Unit → IO UInt64 := fun _ => runFixed runZPowChecksum fixedZPow6
def runFlintZPow6 : Unit → IO UInt64 := fun _ => runFlintZPowChecksum (prepZPowInput 6)
def runZPow8 : Unit → IO UInt64 := fun _ => runFixed runZPowChecksum fixedZPow8
def runFlintZPow8 : Unit → IO UInt64 := fun _ => runFlintZPowChecksum (prepZPowInput 8)

def runFrob2 : Unit → IO UInt64 := fun _ => runFixed runFrobChecksum fixedUnary2
def runFlintFrob2 : Unit → IO UInt64 := fun _ => runFlintFrobChecksum (prepUnaryInput 2)
def runFrob3 : Unit → IO UInt64 := fun _ => runFixed runFrobChecksum fixedUnary3
def runFlintFrob3 : Unit → IO UInt64 := fun _ => runFlintFrobChecksum (prepUnaryInput 3)
def runFrob4 : Unit → IO UInt64 := fun _ => runFixed runFrobChecksum fixedUnary4
def runFlintFrob4 : Unit → IO UInt64 := fun _ => runFlintFrobChecksum (prepUnaryInput 4)
def runFrob5 : Unit → IO UInt64 := fun _ => runFixed runFrobChecksum fixedUnary5
def runFlintFrob5 : Unit → IO UInt64 := fun _ => runFlintFrobChecksum (prepUnaryInput 5)
def runFrob6 : Unit → IO UInt64 := fun _ => runFixed runFrobChecksum fixedUnary6
def runFlintFrob6 : Unit → IO UInt64 := fun _ => runFlintFrobChecksum (prepUnaryInput 6)
def runFrob8 : Unit → IO UInt64 := fun _ => runFixed runFrobChecksum fixedUnary8
def runFlintFrob8 : Unit → IO UInt64 := fun _ => runFlintFrobChecksum (prepUnaryInput 8)

/-
`ofPoly` normalizes through degree-`n` quotient-ring reduction, giving
quadratic work; `repr` is only the projection of the stored canonical
representative.
-/
setup_benchmark runOfPolyReprChecksum n => n * n
  with prep := prepOfPolyInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
Field addition delegates to quotient-ring addition on canonical
degree-bounded representatives, followed by linear degree-bounded
normalization.
-/
setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
Field multiplication delegates to quotient-ring multiplication: multiply two
degree-bounded dense representatives and reduce modulo a degree-`n` modulus,
giving the same quadratic model as quotient-ring multiplication.
-/
setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
Negation and subtraction are linear coefficientwise operations on canonical
degree-bounded representatives, followed by degree-bounded normalization.
-/
setup_benchmark runNegSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
The prepared all-ones exponent has Theta(log n) bits and exercises both the
square and multiply-by-base branch on every bit. Each field multiplication
delegates to a quadratic quotient-ring multiplication.
-/
setup_benchmark runPowChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepPowInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
Inversion computes one polynomial extended gcd against a degree-`n` modulus and
reduces the inverse candidate. Division adds one quadratic field
multiplication after that inverse. The wider custom ladder keeps the small
extended-gcd constants from dominating the fitted quadratic slope.
-/
setup_benchmark runInvDivChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
Negative signed powers compute a natural power with Theta(log n) dense bits and
then invert the result. The quadratic multiplications in the power dominate the
single quadratic inverse at these parameters.
-/
setup_benchmark runZPowChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepZPowInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-
Frobenius is implemented as the fixed `p`-th power. The benchmark prime
`p = 7` has all binary exponent bits set, so the square-and-multiply path
performs Theta(log p) quadratic field multiplications.
-/
setup_benchmark runFrobChecksum n => n * n * Nat.log2 7
  with prep := prepUnaryInput
  where {
    paramFloor := 2
    paramCeiling := 1216
    paramSchedule := .custom scientificSchedule
    maxSecondsPerCall := 120.0
    targetInnerNanos := 200000000
    outerTrials := 3
    signalFloorMultiplier := 1.0
  }

/-! # FLINT `fq_default` informational comparator fixed registrations -/

/-- The FLINT targets make one discarded call to start the persistent Python
driver before timing, then amortise protocol overhead across a 200 ms timed
batch. The pure closed Lean anchors retain isolated calls: batching those
constant fixtures would allow the compiler to fold away their work. -/
private def flintCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 6.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

private def leanCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runOfPoly2 where leanCompareConfig
setup_fixed_benchmark runFlintOfPoly2 where flintCompareConfig
setup_fixed_benchmark runOfPoly3 where leanCompareConfig
setup_fixed_benchmark runFlintOfPoly3 where flintCompareConfig
setup_fixed_benchmark runOfPoly4 where leanCompareConfig
setup_fixed_benchmark runFlintOfPoly4 where flintCompareConfig
setup_fixed_benchmark runOfPoly5 where leanCompareConfig
setup_fixed_benchmark runFlintOfPoly5 where flintCompareConfig
setup_fixed_benchmark runOfPoly6 where leanCompareConfig
setup_fixed_benchmark runFlintOfPoly6 where flintCompareConfig
setup_fixed_benchmark runOfPoly8 where leanCompareConfig
setup_fixed_benchmark runFlintOfPoly8 where flintCompareConfig

setup_fixed_benchmark runAdd2 where leanCompareConfig
setup_fixed_benchmark runFlintAdd2 where flintCompareConfig
setup_fixed_benchmark runAdd3 where leanCompareConfig
setup_fixed_benchmark runFlintAdd3 where flintCompareConfig
setup_fixed_benchmark runAdd4 where leanCompareConfig
setup_fixed_benchmark runFlintAdd4 where flintCompareConfig
setup_fixed_benchmark runAdd5 where leanCompareConfig
setup_fixed_benchmark runFlintAdd5 where flintCompareConfig
setup_fixed_benchmark runAdd6 where leanCompareConfig
setup_fixed_benchmark runFlintAdd6 where flintCompareConfig
setup_fixed_benchmark runAdd8 where leanCompareConfig
setup_fixed_benchmark runFlintAdd8 where flintCompareConfig

setup_fixed_benchmark runMul2 where leanCompareConfig
setup_fixed_benchmark runFlintMul2 where flintCompareConfig
setup_fixed_benchmark runMul3 where leanCompareConfig
setup_fixed_benchmark runFlintMul3 where flintCompareConfig
setup_fixed_benchmark runMul4 where leanCompareConfig
setup_fixed_benchmark runFlintMul4 where flintCompareConfig
setup_fixed_benchmark runMul5 where leanCompareConfig
setup_fixed_benchmark runFlintMul5 where flintCompareConfig
setup_fixed_benchmark runMul6 where leanCompareConfig
setup_fixed_benchmark runFlintMul6 where flintCompareConfig
setup_fixed_benchmark runMul8 where leanCompareConfig
setup_fixed_benchmark runFlintMul8 where flintCompareConfig

setup_fixed_benchmark runNegSub2 where leanCompareConfig
setup_fixed_benchmark runFlintNegSub2 where flintCompareConfig
setup_fixed_benchmark runNegSub3 where leanCompareConfig
setup_fixed_benchmark runFlintNegSub3 where flintCompareConfig
setup_fixed_benchmark runNegSub4 where leanCompareConfig
setup_fixed_benchmark runFlintNegSub4 where flintCompareConfig
setup_fixed_benchmark runNegSub5 where leanCompareConfig
setup_fixed_benchmark runFlintNegSub5 where flintCompareConfig
setup_fixed_benchmark runNegSub6 where leanCompareConfig
setup_fixed_benchmark runFlintNegSub6 where flintCompareConfig
setup_fixed_benchmark runNegSub8 where leanCompareConfig
setup_fixed_benchmark runFlintNegSub8 where flintCompareConfig

setup_fixed_benchmark runPow2 where leanCompareConfig
setup_fixed_benchmark runFlintPow2 where flintCompareConfig
setup_fixed_benchmark runPow3 where leanCompareConfig
setup_fixed_benchmark runFlintPow3 where flintCompareConfig
setup_fixed_benchmark runPow4 where leanCompareConfig
setup_fixed_benchmark runFlintPow4 where flintCompareConfig
setup_fixed_benchmark runPow5 where leanCompareConfig
setup_fixed_benchmark runFlintPow5 where flintCompareConfig
setup_fixed_benchmark runPow6 where leanCompareConfig
setup_fixed_benchmark runFlintPow6 where flintCompareConfig
setup_fixed_benchmark runPow8 where leanCompareConfig
setup_fixed_benchmark runFlintPow8 where flintCompareConfig

setup_fixed_benchmark runInvDiv2 where leanCompareConfig
setup_fixed_benchmark runFlintInvDiv2 where flintCompareConfig
setup_fixed_benchmark runInvDiv3 where leanCompareConfig
setup_fixed_benchmark runFlintInvDiv3 where flintCompareConfig
setup_fixed_benchmark runInvDiv4 where leanCompareConfig
setup_fixed_benchmark runFlintInvDiv4 where flintCompareConfig
setup_fixed_benchmark runInvDiv5 where leanCompareConfig
setup_fixed_benchmark runFlintInvDiv5 where flintCompareConfig
setup_fixed_benchmark runInvDiv6 where leanCompareConfig
setup_fixed_benchmark runFlintInvDiv6 where flintCompareConfig
setup_fixed_benchmark runInvDiv8 where leanCompareConfig
setup_fixed_benchmark runFlintInvDiv8 where flintCompareConfig

setup_fixed_benchmark runZPow2 where leanCompareConfig
setup_fixed_benchmark runFlintZPow2 where flintCompareConfig
setup_fixed_benchmark runZPow3 where leanCompareConfig
setup_fixed_benchmark runFlintZPow3 where flintCompareConfig
setup_fixed_benchmark runZPow4 where leanCompareConfig
setup_fixed_benchmark runFlintZPow4 where flintCompareConfig
setup_fixed_benchmark runZPow5 where leanCompareConfig
setup_fixed_benchmark runFlintZPow5 where flintCompareConfig
setup_fixed_benchmark runZPow6 where leanCompareConfig
setup_fixed_benchmark runFlintZPow6 where flintCompareConfig
setup_fixed_benchmark runZPow8 where leanCompareConfig
setup_fixed_benchmark runFlintZPow8 where flintCompareConfig

setup_fixed_benchmark runFrob2 where leanCompareConfig
setup_fixed_benchmark runFlintFrob2 where flintCompareConfig
setup_fixed_benchmark runFrob3 where leanCompareConfig
setup_fixed_benchmark runFlintFrob3 where flintCompareConfig
setup_fixed_benchmark runFrob4 where leanCompareConfig
setup_fixed_benchmark runFlintFrob4 where flintCompareConfig
setup_fixed_benchmark runFrob5 where leanCompareConfig
setup_fixed_benchmark runFlintFrob5 where flintCompareConfig
setup_fixed_benchmark runFrob6 where leanCompareConfig
setup_fixed_benchmark runFlintFrob6 where flintCompareConfig
setup_fixed_benchmark runFrob8 where leanCompareConfig
setup_fixed_benchmark runFlintFrob8 where flintCompareConfig

end GFqFieldBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
