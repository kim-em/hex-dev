import HexBerlekampMathlib.Basic

/-!
Core conformance checks for `hex-berlekamp-mathlib`.

Oracle: none
Mode: always
Covered operations:
- `fpPolyToPolynomial`, `polynomialToFpPoly`, `fpPolyEquiv`,
  `fpPolyEquiv.symm`, and `toMathlibPolynomial`
- coefficient bridge theorems between executable finite-field polynomials,
  `ZMod64`, `ZMod`, and the generic `HexPolyMathlib.toPolynomial` transport
- Rabin-facing Mathlib surfaces: `Rabin.frobeniusPolynomial`,
  `rabin_irreducible`, `rabin_irreducible_of_positive_degree`,
  `checkIrreducibilityCertificate_irreducible`, and
  `irreducibleDecidablePred`
Covered properties:
- forward transport and the ring-equivalence forward map agree on committed
  `F_5` inputs
- inverse transport and the ring-equivalence inverse map agree on committed
  `F_5` Mathlib polynomials
- round-trips through `fpPolyEquiv` preserve committed executable and Mathlib
  polynomial inputs
- transported coefficients agree with both `ZMod64.equiv` and the generic
  `HexPolyMathlib.toPolynomial` coefficient view
- executable Rabin and certificate checks on committed inputs line up with the
  instantiated Mathlib irreducibility theorem surfaces
Covered edge cases:
- linear monic polynomial over `F_5`
- irreducible quadratic `x^2 + 2` over `F_5`
- reducible quadratic `x^2 + 4` over `F_5`
- zero/trailing-zero Mathlib polynomial representatives for inverse transport
-/

namespace HexBerlekampMathlib
namespace Conformance

noncomputable section

private instance boundsFive : Hex.ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem hexPrimeFive : Hex.Nat.Prime 5 := by
  constructor
  · norm_num
  · intro m hm
    have hle : m ≤ 5 := Nat.le_of_dvd (by norm_num) hm
    interval_cases m <;> simp_all [Nat.dvd_iff_mod_eq_zero]

private instance primeModulusFive : Hex.ZMod64.PrimeModulus 5 :=
  Hex.ZMod64.primeModulusOfPrime hexPrimeFive

private theorem one_ne_zero_five : (1 : Hex.ZMod64 5) ≠ 0 := by
  intro h
  have hm := (Hex.ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def linearPoly : Hex.FpPoly 5 :=
  { coeffs := #[(1 : Hex.ZMod64 5), 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem linearPoly_monic : Hex.DensePoly.Monic linearPoly := by
  rfl

private def irreducibleQuad : Hex.FpPoly 5 :=
  { coeffs := #[(2 : Hex.ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem irreducibleQuad_monic : Hex.DensePoly.Monic irreducibleQuad := by
  rfl

private def reducibleQuad : Hex.FpPoly 5 :=
  { coeffs := #[(4 : Hex.ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem reducibleQuad_monic : Hex.DensePoly.Monic reducibleQuad := by
  rfl

private def mathLinear : Polynomial (ZMod 5) :=
  Polynomial.X + 1

private def mathIrreducibleQuad : Polynomial (ZMod 5) :=
  Polynomial.X ^ 2 + 2

private def mathReducibleQuad : Polynomial (ZMod 5) :=
  Polynomial.X ^ 2 + 4

private def mathZero : Polynomial (ZMod 5) :=
  0

private def mathTrailingZeroRepresentative : Polynomial (ZMod 5) :=
  Polynomial.C 3 + Polynomial.C 4 * Polynomial.X

private def liftedLinearDense : Hex.DensePoly (ZMod 5) :=
  Hex.DensePoly.ofCoeffs #[(1 : ZMod 5), 1]

private def liftedIrreducibleQuadDense : Hex.DensePoly (ZMod 5) :=
  Hex.DensePoly.ofCoeffs #[(2 : ZMod 5), 0, 1]

private def liftedReducibleQuadDense : Hex.DensePoly (ZMod 5) :=
  Hex.DensePoly.ofCoeffs #[(4 : ZMod 5), 0, 1]

private def validQuadCert : Hex.Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[
    Hex.FpPoly.ofCoeffs #[(Hex.ZMod64.ofNat 5 0), Hex.ZMod64.ofNat 5 1],
    Hex.FpPoly.ofCoeffs #[(Hex.ZMod64.ofNat 5 0), Hex.ZMod64.ofNat 5 4],
    Hex.FpPoly.ofCoeffs #[(Hex.ZMod64.ofNat 5 0), Hex.ZMod64.ofNat 5 1]]
  bezout :=
    #[{ left := Hex.FpPoly.ofCoeffs #[(Hex.ZMod64.ofNat 5 3)],
        right := Hex.FpPoly.ofCoeffs #[(Hex.ZMod64.ofNat 5 0), Hex.ZMod64.ofNat 5 4] }]

example : fpPolyEquiv linearPoly = fpPolyToPolynomial linearPoly := by
  rfl

example : fpPolyEquiv irreducibleQuad = fpPolyToPolynomial irreducibleQuad := by
  rfl

example : fpPolyEquiv reducibleQuad = fpPolyToPolynomial reducibleQuad := by
  rfl

example : fpPolyEquiv.symm mathLinear = polynomialToFpPoly mathLinear := by
  rfl

example : fpPolyEquiv.symm mathIrreducibleQuad = polynomialToFpPoly mathIrreducibleQuad := by
  rfl

example : fpPolyEquiv.symm mathReducibleQuad = polynomialToFpPoly mathReducibleQuad := by
  rfl

example : fpPolyEquiv.symm mathZero = polynomialToFpPoly mathZero := by
  rfl

example : fpPolyEquiv.symm (fpPolyEquiv linearPoly) = linearPoly := by
  exact RingEquiv.symm_apply_apply fpPolyEquiv linearPoly

example : fpPolyEquiv.symm (fpPolyEquiv irreducibleQuad) = irreducibleQuad := by
  exact RingEquiv.symm_apply_apply fpPolyEquiv irreducibleQuad

example : fpPolyEquiv.symm (fpPolyEquiv reducibleQuad) = reducibleQuad := by
  exact RingEquiv.symm_apply_apply fpPolyEquiv reducibleQuad

example : fpPolyEquiv (fpPolyEquiv.symm mathLinear) = mathLinear := by
  exact RingEquiv.apply_symm_apply fpPolyEquiv mathLinear

example : fpPolyEquiv (fpPolyEquiv.symm mathIrreducibleQuad) = mathIrreducibleQuad := by
  exact RingEquiv.apply_symm_apply fpPolyEquiv mathIrreducibleQuad

example : fpPolyEquiv (fpPolyEquiv.symm mathTrailingZeroRepresentative) =
    mathTrailingZeroRepresentative := by
  exact RingEquiv.apply_symm_apply fpPolyEquiv mathTrailingZeroRepresentative

example : fpPolyEquiv (fpPolyEquiv.symm mathZero) = mathZero := by
  exact RingEquiv.apply_symm_apply fpPolyEquiv mathZero

example : (toMathlibPolynomial linearPoly).coeff 0 =
    HexModArithMathlib.ZMod64.equiv (linearPoly.coeff 0) :=
  toMathlibPolynomial_coeff_bridge linearPoly 0

example : (toMathlibPolynomial irreducibleQuad).coeff 2 =
    HexModArithMathlib.ZMod64.equiv (irreducibleQuad.coeff 2) :=
  toMathlibPolynomial_coeff_bridge irreducibleQuad 2

example : (toMathlibPolynomial reducibleQuad).coeff 1 =
    HexModArithMathlib.ZMod64.equiv (reducibleQuad.coeff 1) :=
  toMathlibPolynomial_coeff_bridge reducibleQuad 1

example : (HexPolyMathlib.toPolynomial liftedLinearDense).coeff 0 =
    HexModArithMathlib.ZMod64.equiv (linearPoly.coeff 0) := by
  rw [hexPolyMathlib_coeff_bridge]
  rfl

example : (HexPolyMathlib.toPolynomial liftedIrreducibleQuadDense).coeff 2 =
    HexModArithMathlib.ZMod64.equiv (irreducibleQuad.coeff 2) := by
  rw [hexPolyMathlib_coeff_bridge]
  rfl

example : (HexPolyMathlib.toPolynomial liftedReducibleQuadDense).coeff 1 =
    HexModArithMathlib.ZMod64.equiv (reducibleQuad.coeff 1) := by
  rw [hexPolyMathlib_coeff_bridge]
  rfl

example :
    Rabin.frobeniusPolynomial 5 1 = (Polynomial.X : Polynomial (ZMod 5)) ^ (5 ^ 1) -
      Polynomial.X := by
  rfl

#guard Hex.Berlekamp.rabinTest linearPoly linearPoly_monic
#guard Hex.Berlekamp.rabinTest irreducibleQuad irreducibleQuad_monic
#guard !Hex.Berlekamp.rabinTest reducibleQuad reducibleQuad_monic

#guard
  Hex.Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic
    validQuadCert

example :
    Hex.Berlekamp.rabinTest linearPoly linearPoly_monic = true ↔
      Irreducible (toMathlibPolynomial linearPoly) :=
  rabin_irreducible linearPoly linearPoly_monic 1 rfl

example :
    Hex.Berlekamp.rabinTest irreducibleQuad irreducibleQuad_monic = true ↔
      Irreducible (toMathlibPolynomial irreducibleQuad) :=
  rabin_irreducible irreducibleQuad irreducibleQuad_monic 2 rfl

example :
    Hex.Berlekamp.rabinTest reducibleQuad reducibleQuad_monic = true ↔
      Irreducible (toMathlibPolynomial reducibleQuad) :=
  rabin_irreducible reducibleQuad reducibleQuad_monic 2 rfl

example :
    Hex.Berlekamp.rabinTest irreducibleQuad irreducibleQuad_monic = true ↔
      Irreducible (toMathlibPolynomial irreducibleQuad) :=
  rabin_irreducible_of_positive_degree irreducibleQuad irreducibleQuad_monic rfl (by decide)

example :
    Hex.Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic
        validQuadCert = true →
      Irreducible (toMathlibPolynomial irreducibleQuad) :=
  checkIrreducibilityCertificate_irreducible irreducibleQuad irreducibleQuad_monic
    validQuadCert

example : Decidable (Irreducible (toMathlibPolynomial linearPoly)) := by
  infer_instance

example : Decidable (Irreducible (toMathlibPolynomial irreducibleQuad)) := by
  infer_instance

example : Decidable (Irreducible (toMathlibPolynomial reducibleQuad)) := by
  infer_instance

end

end Conformance
end HexBerlekampMathlib
