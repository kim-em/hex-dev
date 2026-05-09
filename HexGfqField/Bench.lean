import HexGfqField.Operations
import HexBerlekamp.RabinSoundness
import LeanBench

/-!
Benchmark registrations for `hex-gfq-field`.

This Phase 4 smoke surface measures the executable finite-field wrapper over
`F_7[x] / (f)`. Inputs use a small schedule of Conway-style irreducible
moduli with certificate-checked Rabin witnesses; construction is hoisted
through `prep`, and timed targets return compact polynomial checksums.

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
private theorem maxProperDiv_6 : Berlekamp.maximalProperDivisors 6 = [2, 3] := by decide
private theorem maxProperDiv_8 : Berlekamp.maximalProperDivisors 8 = [4] := by decide
private theorem maxProperDiv_12 : Berlekamp.maximalProperDivisors 12 = [4, 6] := by decide
private theorem maxProperDiv_16 : Berlekamp.maximalProperDivisors 16 = [8] := by decide

/-! ## Certificate-backed benchmark moduli -/

/-- `x^2 + 6x + 3` over `F_7`. -/
private def m_p7_n2 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
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
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
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
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
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

/-- `x^6 + x^4 + 5x^3 + 4x^2 + 6x + 3` over `F_7`. -/
private def m_p7_n6 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 4, 5, 1, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
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
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
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

/-- `x^12 + x^2 + x + 2` over `F_7`. -/
private def m_p7_n12 : FpPoly 7 :=
  { coeffs := #[(2 : ZMod64 7), 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
private theorem m_p7_n12_pos : 0 < FpPoly.degree m_p7_n12 := by decide
private theorem m_p7_n12_monic : DensePoly.Monic m_p7_n12 := by rfl

private def m_p7_n12_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 12
  powChain :=
    #[polyP7 #[0, 1], polyP7 #[0, 0, 0, 0, 0, 0, 0, 1],
      polyP7 #[0, 2, 4, 0, 0, 0, 0, 0, 4, 1],
      polyP7 #[3, 0, 5, 3, 4, 2, 6, 2, 1, 2, 6, 1],
      polyP7 #[3, 3, 1, 1, 0, 3, 2, 0, 1, 3, 4, 6],
      polyP7 #[2, 2, 5, 6, 3, 2, 6, 1, 1, 4, 4, 3],
      polyP7 #[4, 1, 3, 1, 4, 6, 4, 2, 4, 4, 6, 4],
      polyP7 #[4, 1, 5, 0, 1, 3, 2, 2, 3, 5, 6, 4],
      polyP7 #[6, 6, 2, 2, 6, 0, 0, 6, 6, 1, 3],
      polyP7 #[3, 5, 0, 1, 4, 1, 3, 6, 4, 2, 2, 4],
      polyP7 #[1, 1, 4, 3, 4, 5, 1, 6, 6, 5, 1, 4],
      polyP7 #[2, 6, 6, 4, 2, 6, 4, 2, 5, 1, 3, 2], polyP7 #[0, 1]]
  bezout :=
    #[{ left := polyP7 #[4, 1, 1, 2, 1, 1, 4, 1, 1, 6, 6],
        right := polyP7 #[0, 5, 6, 4, 6, 5, 6, 4, 2, 6, 2, 6] },
      { left := polyP7 #[5, 0, 2, 2, 2, 6, 1, 5, 0, 3, 5],
        right := polyP7 #[3, 4, 6, 0, 0, 0, 0, 4, 5, 0, 2, 4] }]

set_option maxRecDepth 262144 in
set_option maxHeartbeats 400000000 in
private theorem m_p7_n12_certificate_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental m_p7_n12 m_p7_n12_monic
        m_p7_n12_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    m_p7_n12_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinearIncremental,
    Berlekamp.checkPowChainLinearIncrementalStep,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_12,
    m_p7_n12, polyP7]
  constructor
  · constructor
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x hx
          have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨
              x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · exact ⟨rfl, rfl⟩

private theorem m_p7_n12_irr : FpPoly.Irreducible m_p7_n12 :=
  Berlekamp.rabinTest_imp_irreducible m_p7_n12 m_p7_n12_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      m_p7_n12 m_p7_n12_monic m_p7_n12_certificate
      m_p7_n12_certificate_check)

/-- A modulus together with its positive-degree and irreducibility
witnesses, used by the benchmark prep functions to dispatch on the
parameter `n` and select the correct per-degree fixture. -/
private structure ModulusBundle where
  modulus : FpPoly 7
  pos : 0 < FpPoly.degree modulus
  irr : FpPoly.Irreducible modulus

/-- Look up the per-degree modulus fixture for benchmark parameter `n`.
The match enumerates the union of `paramSchedule` entries used by the
registrations below; any `n` outside that schedule falls back to a
degree-2 fixture so that the function remains total. -/
private def bundleForN (n : Nat) : ModulusBundle :=
  match n with
  | 2 => ⟨m_p7_n2, m_p7_n2_pos, m_p7_n2_irr⟩
  | 3 => ⟨m_p7_n3, m_p7_n3_pos, m_p7_n3_irr⟩
  | 4 => ⟨m_p7_n4, m_p7_n4_pos, m_p7_n4_irr⟩
  | 6 => ⟨m_p7_n6, m_p7_n6_pos, m_p7_n6_irr⟩
  | _ => ⟨m_p7_n2, m_p7_n2_pos, m_p7_n2_irr⟩

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly (f : FpPoly 7) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

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

/-
`ofPoly` normalizes through degree-`n` quotient-ring reduction, giving
quadratic work; `repr` is only the projection of the stored canonical
representative.
-/
setup_benchmark runOfPolyReprChecksum n => n * n
  with prep := prepOfPolyInput
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
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
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
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
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
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
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
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
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Inversion computes one polynomial extended gcd against a degree-`n` modulus and
reduces the inverse candidate. Division adds one quadratic field
multiplication after that inverse. The wider doubling ladder keeps the small
extended-gcd constants from dominating the fitted quadratic slope.
-/
setup_benchmark runInvDivChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
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
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
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
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 6]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end GFqFieldBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
