import HexHenselMathlib.Basic
import HexPolyMathlib.Basic

/-!
Core conformance checks for `hex-hensel-mathlib`.

Oracle: none
Mode: always
Covered operations:
- coefficient reduction through `Polynomial.map (Int.castRingHom (ZMod m))`
- `coeff_map_intCastRingHom_eq_zero_iff_dvd`
- `coeff_map_intCastRingHom_eq_iff_dvd_sub`
- `polynomial_map_zmod_pow_succ_to_base`
- `polynomial_map_zmod_pow_succ_to_pow`
- `HexPolyMathlib.toPolynomial` paired with Mathlib coefficient reduction
Covered properties:
- a mapped coefficient is zero exactly when the integer coefficient is divisible
  by the modulus
- two mapped coefficients are equal exactly when the modulus divides their
  integer coefficient difference
- direct reduction to `ZMod p` agrees with reduction through
  `ZMod (p^(k+1))`
- direct reduction to `ZMod (p^k)` agrees with reduction through
  `ZMod (p^(k+1))`
- executable `Hex.ZPoly` coefficients expose the same Mathlib reduction surface
  through `HexPolyMathlib.toPolynomial`
Covered edge cases:
- the zero polynomial
- degree-zero constants with negative coefficients
- sparse polynomials with internal and trailing zero coefficients
- mixed-sign polynomials whose coefficients straddle several modulus classes
- prime powers at `k = 0` and at nontrivial positive exponents
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

private def typical : Polynomial ℤ :=
  Polynomial.C 17 - Polynomial.C 11 * Polynomial.X +
    Polynomial.C 25 * Polynomial.X ^ 2 + Polynomial.C 4 * Polynomial.X ^ 5

private def edgeZero : Polynomial ℤ :=
  0

private def adversarial : Polynomial ℤ :=
  Polynomial.C (-18) + Polynomial.C 30 * Polynomial.X ^ 2 -
    Polynomial.C 45 * Polynomial.X ^ 4 + Polynomial.C 7 * Polynomial.X ^ 8

private def constantNegative : Polynomial ℤ :=
  Polynomial.C (-35)

private def shiftedTypical : Polynomial ℤ :=
  Polynomial.C 2 - Polynomial.C 6 * Polynomial.X +
    Polynomial.C 40 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X ^ 5

private def shiftedAdversarial : Polynomial ℤ :=
  Polynomial.C 7 + Polynomial.C 3 * Polynomial.X ^ 2 -
    Polynomial.C 10 * Polynomial.X ^ 4 + Polynomial.C 42 * Polynomial.X ^ 8

private def zpolyTypical : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[17, -11, 25, 0, 0, 4]

private def zpolyZero : Hex.ZPoly :=
  0

private def zpolyAdversarial : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[-18, 0, 30, 0, -45, 0, 0, 0, 7, 0, 0]

-- Coefficient divisibility/equality after `Polynomial.map`.

example :
    (typical.map (Int.castRingHom (ZMod 5))).coeff 2 = 0 ↔
      (5 : ℤ) ∣ typical.coeff 2 :=
  coeff_map_intCastRingHom_eq_zero_iff_dvd typical 5 2

example :
    (edgeZero.map (Int.castRingHom (ZMod 7))).coeff 4 = 0 ↔
      (7 : ℤ) ∣ edgeZero.coeff 4 :=
  coeff_map_intCastRingHom_eq_zero_iff_dvd edgeZero 7 4

example :
    (adversarial.map (Int.castRingHom (ZMod 9))).coeff 4 = 0 ↔
      (9 : ℤ) ∣ adversarial.coeff 4 :=
  coeff_map_intCastRingHom_eq_zero_iff_dvd adversarial 9 4

example : (typical.map (Int.castRingHom (ZMod 5))).coeff 2 = 0 := by
  apply (coeff_map_intCastRingHom_eq_zero_iff_dvd typical 5 2).mpr
  norm_num [typical, Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : (edgeZero.map (Int.castRingHom (ZMod 7))).coeff 4 = 0 := by
  apply (coeff_map_intCastRingHom_eq_zero_iff_dvd edgeZero 7 4).mpr
  simp [edgeZero]

example : (adversarial.map (Int.castRingHom (ZMod 9))).coeff 4 = 0 := by
  apply (coeff_map_intCastRingHom_eq_zero_iff_dvd adversarial 9 4).mpr
  norm_num [adversarial, Polynomial.coeff_X, Polynomial.coeff_X_pow]

example :
    (typical.map (Int.castRingHom (ZMod 5))).coeff 1 =
        (shiftedTypical.map (Int.castRingHom (ZMod 5))).coeff 1 ↔
      (5 : ℤ) ∣ typical.coeff 1 - shiftedTypical.coeff 1 :=
  coeff_map_intCastRingHom_eq_iff_dvd_sub typical shiftedTypical 5 1

example :
    (edgeZero.map (Int.castRingHom (ZMod 11))).coeff 3 =
        (constantNegative.map (Int.castRingHom (ZMod 11))).coeff 3 ↔
      (11 : ℤ) ∣ edgeZero.coeff 3 - constantNegative.coeff 3 :=
  coeff_map_intCastRingHom_eq_iff_dvd_sub edgeZero constantNegative 11 3

example :
    (adversarial.map (Int.castRingHom (ZMod 5))).coeff 8 =
        (shiftedAdversarial.map (Int.castRingHom (ZMod 5))).coeff 8 ↔
      (5 : ℤ) ∣ adversarial.coeff 8 - shiftedAdversarial.coeff 8 :=
  coeff_map_intCastRingHom_eq_iff_dvd_sub adversarial shiftedAdversarial 5 8

example :
    (typical.map (Int.castRingHom (ZMod 5))).coeff 1 =
      (shiftedTypical.map (Int.castRingHom (ZMod 5))).coeff 1 := by
  apply (coeff_map_intCastRingHom_eq_iff_dvd_sub typical shiftedTypical 5 1).mpr
  norm_num [typical, shiftedTypical, Polynomial.coeff_X, Polynomial.coeff_X_pow]

example :
    (edgeZero.map (Int.castRingHom (ZMod 11))).coeff 3 =
      (constantNegative.map (Int.castRingHom (ZMod 11))).coeff 3 := by
  apply (coeff_map_intCastRingHom_eq_iff_dvd_sub edgeZero constantNegative 11 3).mpr
  simp [edgeZero, constantNegative]

example :
    (adversarial.map (Int.castRingHom (ZMod 5))).coeff 8 =
      (shiftedAdversarial.map (Int.castRingHom (ZMod 5))).coeff 8 := by
  apply (coeff_map_intCastRingHom_eq_iff_dvd_sub adversarial shiftedAdversarial 5 8).mpr
  norm_num [adversarial, shiftedAdversarial, Polynomial.coeff_X, Polynomial.coeff_X_pow]

-- Compatibility of prime-power coefficient reductions.

example :
    (typical.map (Int.castRingHom (ZMod (5 ^ (2 + 1))))).map
        (ZMod.castHom (dvd_pow_self 5 (Nat.succ_ne_zero 2)) (ZMod 5)) =
      typical.map (Int.castRingHom (ZMod 5)) :=
  polynomial_map_zmod_pow_succ_to_base typical 5 2

example :
    (edgeZero.map (Int.castRingHom (ZMod (7 ^ (0 + 1))))).map
        (ZMod.castHom (dvd_pow_self 7 (Nat.succ_ne_zero 0)) (ZMod 7)) =
      edgeZero.map (Int.castRingHom (ZMod 7)) :=
  polynomial_map_zmod_pow_succ_to_base edgeZero 7 0

example :
    (adversarial.map (Int.castRingHom (ZMod (3 ^ (3 + 1))))).map
        (ZMod.castHom (dvd_pow_self 3 (Nat.succ_ne_zero 3)) (ZMod 3)) =
      adversarial.map (Int.castRingHom (ZMod 3)) :=
  polynomial_map_zmod_pow_succ_to_base adversarial 3 3

example :
    (typical.map (Int.castRingHom (ZMod (5 ^ (2 + 1))))).map
        (ZMod.castHom (Nat.pow_dvd_pow 5 (Nat.le_succ 2)) (ZMod (5 ^ 2))) =
      typical.map (Int.castRingHom (ZMod (5 ^ 2))) :=
  polynomial_map_zmod_pow_succ_to_pow typical 5 2

example :
    (edgeZero.map (Int.castRingHom (ZMod (7 ^ (0 + 1))))).map
        (ZMod.castHom (Nat.pow_dvd_pow 7 (Nat.le_succ 0)) (ZMod (7 ^ 0))) =
      edgeZero.map (Int.castRingHom (ZMod (7 ^ 0))) :=
  polynomial_map_zmod_pow_succ_to_pow edgeZero 7 0

example :
    (adversarial.map (Int.castRingHom (ZMod (3 ^ (3 + 1))))).map
        (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ 3)) (ZMod (3 ^ 3))) =
      adversarial.map (Int.castRingHom (ZMod (3 ^ 3))) :=
  polynomial_map_zmod_pow_succ_to_pow adversarial 3 3

-- Small Mathlib-side mirrors of executable `Hex.ZPoly` coefficient congruences.

example (n : Nat) :
    (HexPolyMathlib.toPolynomial zpolyTypical).coeff n = zpolyTypical.coeff n :=
  HexPolyMathlib.coeff_toPolynomial zpolyTypical n

example (n : Nat) :
    (HexPolyMathlib.toPolynomial zpolyZero).coeff n = zpolyZero.coeff n :=
  HexPolyMathlib.coeff_toPolynomial zpolyZero n

example (n : Nat) :
    (HexPolyMathlib.toPolynomial zpolyAdversarial).coeff n = zpolyAdversarial.coeff n :=
  HexPolyMathlib.coeff_toPolynomial zpolyAdversarial n

example :
    ((HexPolyMathlib.toPolynomial zpolyTypical).map (Int.castRingHom (ZMod 5))).coeff 2 =
      Int.castRingHom (ZMod 5) (zpolyTypical.coeff 2) := by
  simp [Polynomial.coeff_map]

example :
    ((HexPolyMathlib.toPolynomial zpolyZero).map (Int.castRingHom (ZMod 7))).coeff 4 =
      Int.castRingHom (ZMod 7) (zpolyZero.coeff 4) := by
  simp [Polynomial.coeff_map]

example :
    ((HexPolyMathlib.toPolynomial zpolyAdversarial).map (Int.castRingHom (ZMod 9))).coeff 8 =
      Int.castRingHom (ZMod 9) (zpolyAdversarial.coeff 8) := by
  simp [Polynomial.coeff_map]

end

end HexHenselMathlib
