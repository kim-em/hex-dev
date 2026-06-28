/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFqRing.Operations

/-!
Core conformance checks for the canonical quotient-ring surface in
`HexGFqRing`.

Oracle: none
Mode: always
Covered operations:
- `reduceMod`
- `ofPoly` and `repr`
- `zero`, `one`, and `const`
- `add`, `mul`, `neg`, and `sub`
- `pow`
- `natCast`, `nsmul`, `intCast`, and `zsmul`
- quotient-ring instance behavior over canonical representatives
Covered properties:
- quotient representatives are reduced below the modulus degree
- `repr (ofPoly f hf g)` agrees with `reduceMod f g`
- reducing an already reduced representative is idempotent
- quotient addition and multiplication agree with reducing polynomial sums
  and products
- additive and multiplicative ring identities, commutativity,
  associativity, distributivity, additive inverses, and subtraction are
  respected by canonical representatives
- natural and integer scalar multiplication agree with multiplication by
  the corresponding quotient constants
Covered edge cases:
- zero, one, and constant representatives
- already reduced linear and degree-3 representatives
- high-degree inputs reduced modulo `x^4 + 2` over `F_5`
- a second concrete quotient `F_7[x] / (x^2 + 1)` exercising
  reduction, ring operations, exponentiation, and scalar/cast at a
  different prime and lower modulus degree
- subtraction and negative integer representatives
- binary-shaped natural and integer scalar multipliers
-/

namespace Hex
namespace GFqRing

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

/-- Modulus `x^4 + 2`, a monic degree-4 polynomial over `F_5`. The
quotient ring `F_5[x] / (x^4 + 2)` has reduction rule
`x^4 ≡ -2 ≡ 3 (mod 5)`. Irreducibility is not needed for the ring-level
conformance checks; the same modulus is used by `HexGFqField` where
irreducibility is verified separately. -/
private def modulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 0, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem modulus_pos_degree : 0 < FpPoly.degree modulus := by
  decide

private abbrev Q := PolyQuotient modulus modulus_pos_degree

private def q (coeffs : Array Nat) : Q :=
  ofPoly modulus modulus_pos_degree (polyFive coeffs)

private def reprNats (x : Q) : List Nat :=
  coeffNats (repr x)

-- typical: degree 1
private def a : Q := q #[2, 3]
-- edge: degree 3, the maximal reduced degree below the modulus
private def b : Q := q #[4, 1, 0, 1]
-- generator x
private def x : Q := q #[0, 1]
-- adversarial raw polynomial x^4, exactly at the modulus degree
private def x4Raw : FpPoly 5 := polyFive #[0, 0, 0, 0, 1]
-- adversarial quotient element from x^4: reduces to constant 3 since x^4 = -2 ≡ 3
private def x4Mod : Q := ofPoly modulus modulus_pos_degree x4Raw
-- adversarial quotient element from x^5: reduces to 3x via x · x^4 = x · 3 = 3x
private def x5 : Q := q #[0, 0, 0, 0, 0, 1]

/-- info: [3] -/
#guard_msgs in
#eval! coeffNats (reduceMod modulus x4Raw)

#guard coeffNats (reduceMod modulus (polyFive #[2, 3])) = [2, 3]
#guard coeffNats (reduceMod modulus (0 : FpPoly 5)) = []
-- x^5 mod (x^4 + 2): quotient x, remainder x^5 - x(x^4 + 2) = -2x ≡ 3x
#guard coeffNats (reduceMod modulus (polyFive #[0, 0, 0, 0, 0, 1])) = [0, 3]

#guard reprNats (ofPoly modulus modulus_pos_degree (polyFive #[2, 3])) = [2, 3]
#guard reprNats (ofPoly modulus modulus_pos_degree (0 : FpPoly 5)) = []
#guard reprNats x4Mod = [3]
#guard repr (ofPoly modulus modulus_pos_degree x4Raw) = reduceMod modulus x4Raw

#guard reprNats a = [2, 3]
#guard reprNats b = [4, 1, 0, 1]
#guard reprNats (0 : Q) = []
#guard reprNats x5 = [0, 3]

#guard reprNats (zero modulus modulus_pos_degree) = []
#guard reprNats (0 : Q) = []
#guard zero modulus modulus_pos_degree = (ofPoly modulus modulus_pos_degree 0 : Q)

#guard reprNats (one modulus modulus_pos_degree) = [1]
#guard reprNats (1 : Q) = [1]
#guard one modulus modulus_pos_degree = (ofPoly modulus modulus_pos_degree 1 : Q)

#guard reprNats (const modulus modulus_pos_degree (ZMod64.ofNat 5 3)) = [3]
#guard reprNats (const modulus modulus_pos_degree (ZMod64.ofNat 5 0)) = []
#guard reprNats (const modulus modulus_pos_degree (ZMod64.ofNat 5 17)) = [2]

-- (2 + 3x) + (4 + x + x^3) = 6 + 4x + x^3 ≡ 1 + 4x + x^3 (mod 5)
/-- info: [1, 4, 0, 1] -/
#guard_msgs in
#eval! reprNats (a + b)

#guard reprNats (a + 0) = [2, 3]
-- x5 + b = 3x + (4 + x + x^3) = 4 + 4x + x^3
#guard reprNats (x5 + b) = [4, 4, 0, 1]
#guard repr (a + b) = reduceMod modulus (repr a + repr b)

-- (2 + 3x)(4 + x + x^3) = 8 + 14x + 3x^2 + 2x^3 + 3x^4
--   ≡ 3 + 4x + 3x^2 + 2x^3 + 3·3 (mod 5, x^4 ≡ 3)
--   = 12 + 4x + 3x^2 + 2x^3 ≡ 2 + 4x + 3x^2 + 2x^3
/-- info: [2, 4, 3, 2] -/
#guard_msgs in
#eval! reprNats (a * b)

#guard reprNats (a * 0) = []
-- x5 * x = x^5 · x = x^6 = x^2 · x^4 ≡ x^2 · 3 = 3x^2
#guard reprNats (x5 * x) = [0, 0, 3]
#guard repr (a * b) = reduceMod modulus (repr a * repr b)

#guard reprNats (-a) = [3, 2]
#guard reprNats (-(0 : Q)) = []
-- -b = -(4 + x + x^3) ≡ 1 + 4x + 4x^3 (mod 5)
#guard reprNats (-b) = [1, 4, 0, 4]

-- (2 + 3x) - (4 + x + x^3) = -2 + 2x - x^3 ≡ 3 + 2x + 4x^3 (mod 5)
#guard reprNats (a - b) = [3, 2, 0, 4]
#guard reprNats ((0 : Q) - a) = [3, 2]
-- b - x4Mod = (4 + x + x^3) - 3 = 1 + x + x^3
#guard reprNats (b - x4Mod) = [1, 1, 0, 1]

#guard reprNats (x ^ 0) = [1]
#guard reprNats (x ^ 2) = [0, 0, 1]
#guard reprNats (x ^ 3) = [0, 0, 0, 1]
-- x^4 ≡ 3 by the modulus relation
#guard reprNats (x ^ 4) = [3]
-- x^5 ≡ 3x
#guard reprNats (x ^ 5) = [0, 3]

#guard reprNats ((7 : Nat) : Q) = [2]
#guard reprNats ((0 : Nat) : Q) = []
#guard reprNats ((15 : Nat) : Q) = []

#guard reprNats (nsmul 3 x) = [0, 3]
#guard reprNats (nsmul 0 a) = []
-- 8 · (2 + 3x) = 16 + 24x ≡ 1 + 4x (mod 5)
#guard reprNats (nsmul 8 a) = [1, 4]

#guard reprNats ((-1 : Int) : Q) = [4]
#guard reprNats ((12 : Int) : Q) = [2]
#guard reprNats ((0 : Int) : Q) = []

#guard reprNats (zsmul (-2) x) = [0, 3]
#guard reprNats (zsmul 0 x) = []
-- 7 · (2 + 3x) = 14 + 21x ≡ 4 + x (mod 5)
#guard reprNats (zsmul 7 a) = [4, 1]

#guard FpPoly.degree (repr a) < FpPoly.degree modulus
#guard FpPoly.degree (repr b) < FpPoly.degree modulus
#guard FpPoly.degree (repr x4Mod) < FpPoly.degree modulus
#guard FpPoly.degree (repr (0 : Q)) < FpPoly.degree modulus

#guard reduceMod modulus (repr a) = repr a
#guard reduceMod modulus (reduceMod modulus x4Raw) = reduceMod modulus x4Raw
#guard reduceMod modulus (repr b) = repr b

#guard reprNats (0 + a) = reprNats a
#guard reprNats (a + 0) = reprNats a
#guard a + b = b + a
#guard (a + b) + x = a + (b + x)
#guard -a + a = 0
#guard a - b = a + -b

#guard reprNats (1 * a) = reprNats a
#guard reprNats (a * 1) = reprNats a
#guard a * b = b * a
#guard (a * b) * x = a * (b * x)
#guard a * (b + x) = a * b + a * x
#guard (a + b) * x = a * x + b * x

#guard nsmul 8 a = ((8 : Nat) : Q) * a
#guard zsmul 7 a = ((7 : Int) : Q) * a
#guard zsmul (-2) x = ((-2 : Int) : Q) * x

/-! ## Second concrete quotient: `F_7[x] / (x^2 + 1)` -/

private instance conformanceBoundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private theorem one_ne_zero_seven : (1 : ZMod64 7) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 7) 1 0).mp h
  simp at hm

private def polySeven (coeffs : Array Nat) : FpPoly 7 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 7 n))

private def coeffNats7 (f : FpPoly 7) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

/-- Modulus `x^2 + 1`, a monic degree-2 polynomial over `F_7`. The
quotient ring `F_7[x] / (x^2 + 1)` has reduction rule
`x^2 ≡ -1 ≡ 6 (mod 7)`. Irreducibility is not needed for the
ring-level conformance checks; `x^2 + 1` is in fact irreducible over
`F_7` since `-1` is not a square mod 7. -/
private def modulus7 : FpPoly 7 :=
  { coeffs := #[(1 : ZMod64 7), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_seven }

private theorem modulus7_pos_degree : 0 < FpPoly.degree modulus7 := by
  decide

private abbrev Q7 := PolyQuotient modulus7 modulus7_pos_degree

private def q7 (coeffs : Array Nat) : Q7 :=
  ofPoly modulus7 modulus7_pos_degree (polySeven coeffs)

private def reprNats7 (x : Q7) : List Nat :=
  coeffNats7 (repr x)

-- typical: linear element 3 + 5x
private def a7 : Q7 := q7 #[3, 5]
-- second linear element 2 + 4x
private def b7 : Q7 := q7 #[2, 4]
-- generator x
private def x7 : Q7 := q7 #[0, 1]
-- adversarial raw polynomial x^2, exactly at the modulus degree
private def x2Raw7 : FpPoly 7 := polySeven #[0, 0, 1]
-- adversarial quotient element from x^2: reduces to constant 6 since x^2 = -1 ≡ 6
private def x2Mod7 : Q7 := ofPoly modulus7 modulus7_pos_degree x2Raw7
-- adversarial quotient element from x^3: reduces to 6x via x · x^2 = x · 6 = 6x
private def x3Seven : Q7 := q7 #[0, 0, 0, 1]

/-- info: [6] -/
#guard_msgs in
#eval! coeffNats7 (reduceMod modulus7 x2Raw7)

#guard coeffNats7 (reduceMod modulus7 (polySeven #[3, 5])) = [3, 5]
#guard coeffNats7 (reduceMod modulus7 (0 : FpPoly 7)) = []
-- x^3 mod (x^2 + 1): x^3 - x(x^2 + 1) = -x ≡ 6x
#guard coeffNats7 (reduceMod modulus7 (polySeven #[0, 0, 0, 1])) = [0, 6]

#guard reprNats7 (ofPoly modulus7 modulus7_pos_degree (polySeven #[3, 5])) = [3, 5]
#guard reprNats7 (ofPoly modulus7 modulus7_pos_degree (0 : FpPoly 7)) = []
#guard reprNats7 x2Mod7 = [6]
#guard repr (ofPoly modulus7 modulus7_pos_degree x2Raw7) = reduceMod modulus7 x2Raw7

#guard reprNats7 a7 = [3, 5]
#guard reprNats7 b7 = [2, 4]
#guard reprNats7 (0 : Q7) = []
#guard reprNats7 x3Seven = [0, 6]

-- (3 + 5x) + (2 + 4x) = 5 + 9x ≡ 5 + 2x (mod 7)
#guard reprNats7 (a7 + b7) = [5, 2]
#guard reprNats7 (a7 + 0) = [3, 5]
#guard repr (a7 + b7) = reduceMod modulus7 (repr a7 + repr b7)

-- (3 + 5x)(2 + 4x) = 6 + 22x + 20x^2
--   ≡ 6 + x + 6x^2 (mod 7)
--   ≡ 6 + x + 6·6 (mod 7, x^2 ≡ 6) = 6 + x + 36 ≡ x (mod 7)
#guard reprNats7 (a7 * b7) = [0, 1]
#guard reprNats7 (a7 * 0) = []
#guard repr (a7 * b7) = reduceMod modulus7 (repr a7 * repr b7)

-- -a7 = -(3 + 5x) ≡ 4 + 2x (mod 7)
#guard reprNats7 (-a7) = [4, 2]
-- a7 - b7 = (3 + 5x) - (2 + 4x) = 1 + x
#guard reprNats7 (a7 - b7) = [1, 1]
-- b7 - x2Mod7 = (2 + 4x) - 6 ≡ 3 + 4x (mod 7)
#guard reprNats7 (b7 - x2Mod7) = [3, 4]

#guard reprNats7 (x7 ^ 0) = [1]
-- x^2 ≡ 6 (mod 7) by the modulus relation
#guard reprNats7 (x7 ^ 2) = [6]
-- x^3 ≡ 6x
#guard reprNats7 (x7 ^ 3) = [0, 6]
-- x^4 = (x^2)^2 ≡ 6^2 = 36 ≡ 1 (mod 7)
#guard reprNats7 (x7 ^ 4) = [1]

#guard reprNats7 ((10 : Nat) : Q7) = [3]
#guard reprNats7 ((7 : Nat) : Q7) = []
#guard reprNats7 ((-1 : Int) : Q7) = [6]

-- -2 · (3 + 5x) = -6 - 10x ≡ 1 + 4x (mod 7)
#guard reprNats7 (zsmul (-2) a7) = [1, 4]

#guard FpPoly.degree (repr a7) < FpPoly.degree modulus7
#guard FpPoly.degree (repr x2Mod7) < FpPoly.degree modulus7

end GFqRing
end Hex
