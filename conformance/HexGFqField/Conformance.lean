/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFqField.Operations
import HexBerlekamp.RabinSoundness

/-!
Core conformance checks for the finite-field wrapper in `HexGFqField`.

Oracle: none
Mode: always
Covered operations:
- `ofQuotient`, `ofPoly`, and `repr`
- `zero` and `one`
- `add`, `mul`, `neg`, and `sub`
- `pow`
- `natCast`, `nsmul`, `intCast`, and `zsmul`
- `inv`, `div`, and `zpow`
- `frob`
Covered properties:
- finite-field representatives are reduced below the modulus degree
- field constructors and operations agree with quotient-ring reduction
- additive, multiplicative, and scalar ring laws are respected through
  the wrapper
- nonzero committed fixtures satisfy `x * x⁻¹ = 1`
- division agrees with multiplication by inverse
- Frobenius agrees with `p`-th power
- characteristic-`p` casts identify values modulo `p`
Covered edge cases:
- zero and one representatives
- already reduced linear and degree-3 representatives
- high-degree inputs reduced modulo `x^4 + 2` over `F_5`
- subtraction and negative integer representatives
- inverse, division, and negative powers on nonzero fixtures
-/

namespace Hex
namespace GFqField

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

/-- Modulus `x^4 + 2`, an irreducible degree-4 polynomial over `F_5`.
Irreducibility is discharged below via an executable
`Berlekamp.IrreducibilityCertificate` whose pow chain and Bezout
witness are checked by the kernel-reducible
`Berlekamp.checkIrreducibilityCertificateLinear`, then routed through
`Berlekamp.rabinTest_imp_irreducible`. -/
private def modulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 0, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem modulus_pos_degree : 0 < FpPoly.degree modulus := by
  decide

private theorem modulus_monic : DensePoly.Monic modulus := by rfl

private instance primeModulusFive : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five

private abbrev Q := GFqRing.PolyQuotient modulus modulus_pos_degree
private abbrev F (hirr : FpPoly.Irreducible modulus) :=
  FiniteField modulus modulus_pos_degree prime_five hirr

section InverseDivisionAutomation

example : ((0 : F modulus_irreducible)⁻¹ = 0) := by
  simp

example {hirr : FpPoly.Irreducible modulus} (x y : F hirr) :
    x / y = x * y⁻¹ := by
  simp

example {hirr : FpPoly.Irreducible modulus} (x : F hirr) :
    x ≠ 0 → x * x⁻¹ = 1 := by
  grind

end InverseDivisionAutomation

private theorem maxProperDiv_4 : Berlekamp.maximalProperDivisors 4 = [2] := by decide

/-- Rabin certificate for `x^4 + 2` over `F_5`.

The pow chain records `X^(5^k) mod (x^4 + 2)` for `k = 0..4`. Using
`X^4 ≡ -2 ≡ 3` and the relation `X^5 ≡ 3 X`, the iterates are
`X, 3X, 4X, 2X, X`. The Bezout witness for the only maximal proper
divisor `d = 2` of `n = 4` certifies `gcd(modulus, X^25 - X mod modulus)`
is a unit: `3 · (x^4 + 2) + 4x^3 · (3x) = 3x^4 + 1 + 2x^4 = 5x^4 + 1 = 1`
in `F_5[x]`. -/
private def modulus_irreducibility_certificate :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 4
  powChain :=
    #[polyFive #[0, 1], polyFive #[0, 3], polyFive #[0, 4],
      polyFive #[0, 2], polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3], right := polyFive #[0, 0, 0, 4] }]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 8000000 in
private theorem modulus_certificate_linear_check :
    Berlekamp.checkIrreducibilityCertificateLinear modulus modulus_monic
        modulus_irreducibility_certificate = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    modulus_irreducibility_certificate,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4,
    modulus, polyFive]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem modulus_irreducible : FpPoly.Irreducible modulus :=
  Berlekamp.rabinTest_imp_irreducible modulus modulus_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      modulus modulus_monic modulus_irreducibility_certificate
      modulus_certificate_linear_check)

private def q (coeffs : Array Nat) : Q :=
  GFqRing.ofPoly modulus modulus_pos_degree (polyFive coeffs)

private def ff (hirr : FpPoly.Irreducible modulus) (coeffs : Array Nat) : F hirr :=
  ofPoly modulus modulus_pos_degree prime_five hirr (polyFive coeffs)

private def reprNats {hirr : FpPoly.Irreducible modulus} (x : F hirr) : List Nat :=
  coeffNats (repr x)

private def conformanceChecks : Bool :=
  let hirr := modulus_irreducible
  -- typical: degree 1
  let a : F hirr := ff hirr #[2, 3]
  -- typical/edge: degree 3, just below modulus degree 4
  let b : F hirr := ff hirr #[4, 1, 0, 1]
  -- generator x
  let xv : F hirr := ff hirr #[0, 1]
  -- adversarial: x^4, exactly at modulus degree, reduces to constant 3
  let high : F hirr := ff hirr #[0, 0, 0, 0, 1]
  [
    decide (reprNats (ofQuotient (q #[2, 3]) : F hirr) = [2, 3]),
    decide ((ofQuotient (q #[2, 3]) : F hirr).toQuotient = q #[2, 3]),
    -- x^4 lifted through ofQuotient reduces to constant 3 (= -2 mod 5)
    decide (reprNats (ofQuotient (q #[0, 0, 0, 0, 1]) : F hirr) = [3]),
    decide (reprNats (ofPoly modulus modulus_pos_degree prime_five hirr (polyFive #[2, 3])) = [2, 3]),
    decide (reprNats (ofPoly modulus modulus_pos_degree prime_five hirr (0 : FpPoly 5)) = []),
    -- x^5 reduces to 3x via x^4 = -2 = 3
    decide (reprNats (ofPoly modulus modulus_pos_degree prime_five hirr (polyFive #[0, 0, 0, 0, 0, 1])) =
      [0, 3]),
    decide (repr (ofPoly modulus modulus_pos_degree prime_five hirr (polyFive #[0, 0, 0, 0, 0, 1])) =
      GFqRing.reduceMod modulus (polyFive #[0, 0, 0, 0, 0, 1])),
    decide (reprNats a = [2, 3]),
    decide (reprNats b = [4, 1, 0, 1]),
    decide (reprNats (0 : F hirr) = []),
    -- x^4 stored representative reduces to 3
    decide (reprNats high = [3]),
    decide (reprNats (zero modulus modulus_pos_degree prime_five hirr) = []),
    decide (reprNats (0 : F hirr) = []),
    decide ((zero modulus modulus_pos_degree prime_five hirr : F hirr) =
      ofPoly modulus modulus_pos_degree prime_five hirr 0),
    decide (reprNats (one modulus modulus_pos_degree prime_five hirr) = [1]),
    decide (reprNats (1 : F hirr) = [1]),
    decide ((one modulus modulus_pos_degree prime_five hirr : F hirr) =
      ofPoly modulus modulus_pos_degree prime_five hirr 1),
    -- (2 + 3x) + (4 + x + x^3) = 1 + 4x + x^3
    decide (reprNats (a + b) = [1, 4, 0, 1]),
    decide (reprNats (a + 0) = [2, 3]),
    -- x^5 + b = 3x + (4 + x + x^3) = 4 + 4x + x^3
    decide (reprNats ((ff hirr #[0, 0, 0, 0, 0, 1]) + b) = [4, 4, 0, 1]),
    decide (repr (a + b) = GFqRing.reduceMod modulus (repr a + repr b)),
    -- (2 + 3x)(4 + x + x^3) = 8 + 14x + 3x^2 + 2x^3 + 3x^4
    --                      ≡ 3 + 4x + 3x^2 + 2x^3 + 3·3 (mod 5, after reducing x^4 = 3)
    --                      = 2 + 4x + 3x^2 + 2x^3
    decide (reprNats (a * b) = [2, 4, 3, 2]),
    decide (reprNats (a * 0) = []),
    -- x^5 · x = x^6 = 3x^2
    decide (reprNats ((ff hirr #[0, 0, 0, 0, 0, 1]) * xv) = [0, 0, 3]),
    decide (repr (a * b) = GFqRing.reduceMod modulus (repr a * repr b)),
    decide (reprNats (-a) = [3, 2]),
    decide (reprNats (-(0 : F hirr)) = []),
    -- -(x^5) reduces to -3x = 2x
    decide (reprNats (-(ff hirr #[0, 0, 0, 0, 0, 1])) = [0, 2]),
    -- (2 + 3x) - (4 + x + x^3) = -2 + 2x - x^3 = 3 + 2x + 4x^3
    decide (reprNats (a - b) = [3, 2, 0, 4]),
    decide (reprNats ((0 : F hirr) - a) = [3, 2]),
    -- b - x^5 = (4 + x + x^3) - 3x = 4 + 3x + x^3
    decide (reprNats (b - ff hirr #[0, 0, 0, 0, 0, 1]) = [4, 3, 0, 1]),
    decide (reprNats (xv ^ 0) = [1]),
    decide (reprNats (xv ^ 2) = [0, 0, 1]),
    decide (reprNats (xv ^ 3) = [0, 0, 0, 1]),
    -- x^4 = 3 by the modulus relation
    decide (reprNats (xv ^ 4) = [3]),
    decide (reprNats ((7 : Nat) : F hirr) = [2]),
    decide (reprNats ((0 : Nat) : F hirr) = []),
    decide (reprNats ((15 : Nat) : F hirr) = []),
    decide (((17 : Nat) : F hirr) = (2 : F hirr)),
    decide (reprNats (nsmul 3 xv) = [0, 3]),
    decide (reprNats (nsmul 0 a) = []),
    -- 8 · (2 + 3x) = 16 + 24x ≡ 1 + 4x
    decide (reprNats (nsmul 8 a) = [1, 4]),
    decide (reprNats ((-1 : Int) : F hirr) = [4]),
    decide (reprNats ((12 : Int) : F hirr) = [2]),
    decide (reprNats ((0 : Int) : F hirr) = []),
    decide (((-3 : Int) : F hirr) = (2 : F hirr)),
    decide (reprNats (zsmul (-2) xv) = [0, 3]),
    decide (reprNats (zsmul 0 xv) = []),
    -- 7 · (2 + 3x) = 14 + 21x ≡ 4 + x
    decide (reprNats (zsmul 7 a) = [4, 1]),
    -- a⁻¹ from extended gcd: (2 + 3x)(1 + x + x^2 + x^3) ≡ 1 (mod x^4 + 2, mod 5)
    decide (reprNats a⁻¹ = [1, 1, 1, 1]),
    -- b⁻¹: (4 + x + x^3)(4x + 3x^2 + 3x^3) ≡ 1 (mod x^4 + 2, mod 5)
    decide (reprNats b⁻¹ = [0, 4, 3, 3]),
    -- x⁻¹ = 2 x^3 since x · 2 x^3 = 2 x^4 = 2·3 = 1
    decide (reprNats xv⁻¹ = [0, 0, 0, 2]),
    decide (a * a⁻¹ = 1),
    decide (b * b⁻¹ = 1),
    decide (xv * xv⁻¹ = 1),
    -- a / b = a · b⁻¹ = 2 + 3x + 3x^2
    decide (reprNats (a / b) = [2, 3, 3]),
    decide (a / b = a * b⁻¹),
    decide (xv / a = xv * a⁻¹),
    decide ((0 : F hirr) / b = 0 * b⁻¹),
    decide (reprNats (zpow xv (-1)) = [0, 0, 0, 2]),
    -- (b⁻¹)^2 = (4x + 3x^2 + 3x^3)^2 reduces to 4 + 4x + 3x^2 + 4x^3
    decide (reprNats (zpow b (-2)) = [4, 4, 3, 4]),
    decide (reprNats (zpow a 3) = reprNats (a ^ 3)),
    -- frob a = a^5 = 2^5 + (3x)^5 = 2 + 3·x^5 = 2 + 3·3x = 2 + 4x
    decide (reprNats (frob a) = [2, 4]),
    -- frob b = b^5 = 4^5 + x^5 + x^15 = 4 + 3x + 2x^3
    decide (reprNats (frob b) = [4, 3, 0, 2]),
    -- frob xv = xv^5 = 3x
    decide (reprNats (frob xv) = [0, 3]),
    decide (frob a = a ^ (5 : Nat)),
    decide (frob b = b ^ (5 : Nat)),
    decide (frob xv = xv ^ (5 : Nat)),
    decide (FpPoly.degree (repr a) < FpPoly.degree modulus),
    decide (FpPoly.degree (repr b) < FpPoly.degree modulus),
    decide (FpPoly.degree (repr (ff hirr #[0, 0, 0, 0, 0, 1])) < FpPoly.degree modulus),
    decide (FpPoly.degree (repr (0 : F hirr)) < FpPoly.degree modulus),
    decide (GFqRing.reduceMod modulus (repr a) = repr a),
    decide (GFqRing.reduceMod modulus (repr b) = repr b),
    decide (GFqRing.reduceMod modulus (repr (ff hirr #[0, 0, 0, 0, 0, 1])) =
      repr (ff hirr #[0, 0, 0, 0, 0, 1])),
    decide (GFqRing.reduceMod modulus (repr high) = repr high),
    decide (reprNats (0 + a) = reprNats a),
    decide (reprNats (a + 0) = reprNats a),
    decide (a + b = b + a),
    decide ((a + b) + xv = a + (b + xv)),
    decide (-a + a = 0),
    decide (a - b = a + -b),
    decide (reprNats (1 * a) = reprNats a),
    decide (reprNats (a * 1) = reprNats a),
    decide (a * b = b * a),
    decide ((a * b) * xv = a * (b * xv)),
    decide (a * (b + xv) = a * b + a * xv),
    decide ((a + b) * xv = a * xv + b * xv),
    decide (nsmul 8 a = ((8 : Nat) : F hirr) * a),
    decide (zsmul 7 a = ((7 : Int) : F hirr) * a),
    decide (zsmul (-2) xv = ((-2 : Int) : F hirr) * xv)
  ].all id

#guard conformanceChecks

end GFqField
end Hex
