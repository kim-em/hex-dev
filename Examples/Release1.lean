/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexGF2
public meta import HexGFqField.Operations
public import HexGF2
public import HexGFqField.Operations
public import HexPolyFp.Degree
public import HexPolyFp.Enumeration

public section

/-!
# Release 1: the finite-field constructor

Two fields, built two ways, and both usable as fields the moment they exist.

`GF(2⁸)` is the AES field: `hex-gf2` packs a residue into a single machine
word and ships the Rijndael modulus together with a Rabin certificate that the
kernel replays, so the caller names the field and gets arithmetic.

`F₃[x]/(x² + 1)` is the general constructor: `HexGFqField.FiniteField` turns
*any* modulus into a field once the caller hands over a proof that it is
irreducible. That proof is the release's boundary. Release 1 does **not**
claim to produce irreducibility evidence on demand; here it is discharged by
hand, from the finite enumeration of candidate factors that `HexPolyFp`
already provides. Release 2 adds the engine (`hex-berlekamp`'s Rabin test and
`hex-conway`'s tabulated moduli) that removes the hand work; the field
constructor below is unchanged by that, because it never cared where `hirr`
came from.

Nothing here imports an irreducibility *search*. The imports are exactly the
Release 1 library set: no `hex-berlekamp`, no `hex-conway`, no `hex-gfq`.
`Examples/FiniteFields.lean` covers the same two fields once those are
available, including the canonical Conway presentations; it is a Release 2
artifact and deliberately not the file the release predicate names.
-/

namespace Examples.Release1

open Hex

/-! ## `GF(2⁸)`, the AES field

`hex-gf2` owns its own Rabin test, so the irreducibility argument for the
Rijndael modulus `x⁸ + x⁴ + x³ + x + 1` is already committed as
`GF2Poly.aes_modulus_irreducible`. The field type takes that theorem as a
parameter: a `GF2n` value cannot exist without it. -/

/-- `GF(2⁸)` under the Rijndael modulus, packed into one `UInt64`. -/
abbrev AES : Type :=
  GF2n 8 0x1B (by decide) (by decide) GF2Poly.aes_modulus_irreducible

/-- Reduce a byte into the AES field. -/
def byte (w : UInt64) : AES := GF2n.reduce w

-- Addition is XOR, and every element is its own negative: the field has
-- characteristic two.
#guard (byte 0x57 + byte 0x83).val = 0xD4
#guard (byte 0x57 + byte 0x57).val = 0

-- Multiplication reduces modulo the Rijndael polynomial. These are the
-- FIPS-197 worked values.
#guard (byte 0x57 * byte 0x83).val = 0xC1
#guard (byte 0x57 * byte 0x02).val = 0xAE

-- Associativity and distributivity, spot-checked on concrete bytes. Both are
-- theorems in `hex-gf2` (`GF2n.mul_assoc`, `GF2n.left_distrib`); a release
-- example should also show them *running*.
#guard ((byte 0x57 * byte 0x83) * byte 0x13).val
    = (byte 0x57 * (byte 0x83 * byte 0x13)).val
#guard (byte 0x57 * (byte 0x83 + byte 0x13)).val
    = (byte 0x57 * byte 0x83 + byte 0x57 * byte 0x13).val

-- The inversion step of the AES S-box. `0x53` and `0xCA` are the standard
-- inverse pair, and inversion is `a ↦ a^254` on the nonzero elements.
#guard ((byte 0x53) * (byte 0x53)⁻¹).val = 1
#guard (byte 0x53)⁻¹.val = 0xCA
#guard (byte 0x53 ^ (254 : Nat)).val = 0xCA

-- The multiplicative group has order 255, so `a^255 = 1` for every nonzero
-- `a`, and `a ↦ a²` is the Frobenius endomorphism.
#guard (byte 0x53 ^ (255 : Nat)).val = 1
#guard ((byte 0x57 + byte 0x83) ^ (2 : Nat)).val
    = ((byte 0x57 ^ (2 : Nat)) + (byte 0x83 ^ (2 : Nat))).val

/-- Cancellation is a theorem about every nonzero element, not only the bytes
guarded above. -/
example (a : AES) (h : a ≠ 0) : a * a⁻¹ = 1 :=
  GF2n.mul_inv_cancel a h

/-! ## `F₃[x]/(x² + 1)`, the general constructor

`GFqField.FiniteField f hf hp hirr` is the release's headline type: the
quotient of `Fₚ[x]` by a modulus, carrying the three facts that make the
quotient a field — the modulus is nonconstant, `p` is prime, and the modulus
is irreducible. All three are *supplied by the caller*. -/

/-- Word bounds for the characteristic. -/
instance boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩

/-- The characteristic is prime. -/
theorem prime_three : Hex.Nat.Prime 3 := by decide

instance : ZMod64.PrimeModulus 3 := ZMod64.primeModulusOfPrime prime_three

/-- `x² + 1` over `F₃`. Over `F₃` the element `-1 = 2` is not a square, so
this is the Gaussian-integer analogue: adjoining a square root of `-1`. -/
def modulus : FpPoly 3 := #p[1, 0, 1]

/-- The modulus is nonconstant, which is the second thing the field wrapper
needs beside irreducibility: irreducibility alone admits nonzero constants,
and the quotient by a constant is trivial. -/
theorem modulus_pos_degree : 0 < FpPoly.degree modulus := by decide

/-- No proper factorization of `x² + 1` over `F₃` exists, checked by brute
force over the nine polynomials of degree below two.

This is the whole of the user's obligation, and the whole of what Release 1
declines to automate. The shape of the argument is generic: `FpPoly` is an
integral domain over a prime modulus, so `size` is additive
(`FpPoly.size_mul_eq_add_sub_one`), a factorization of a degree-two modulus
into two nonconstant factors must be a product of two linear polynomials, and
`FpPoly.Enumeration.polysBelowDegree` enumerates those. The kernel then checks
all 81 products. -/
theorem modulus_irreducible : FpPoly.Irreducible modulus := by
  have hmod_ne : modulus ≠ 0 := by decide
  refine ⟨hmod_ne, ?_⟩
  intro a b hab
  -- Neither factor is zero, because their product is not.
  have ha : a ≠ 0 := by
    intro h
    exact hmod_ne (by rw [← hab, h]; simp)
  have hb : b ≠ 0 := by
    intro h
    exact hmod_ne (by rw [← hab, h]; simp)
  -- `size` is additive on nonzero factors, and the modulus has size three.
  have hsize := FpPoly.size_mul_eq_add_sub_one a b ha hb
  rw [hab, show modulus.size = 3 from by decide] at hsize
  have ha_pos : 0 < a.size := FpPoly.size_pos_of_ne_zero ha
  have hb_pos : 0 < b.size := FpPoly.size_pos_of_ne_zero hb
  -- A factor of size one is a nonzero constant, i.e. has degree `some 0`.
  have hconst : ∀ c : FpPoly 3, c.size = 1 → c.degree? = some 0 := by
    intro c hc
    simp [DensePoly.degree?, hc]
  by_cases ha1 : a.size = 1
  · exact Or.inl (hconst a ha1)
  by_cases hb1 : b.size = 1
  · exact Or.inr (hconst b hb1)
  -- Otherwise both factors are linear, so both lie in the nine-element
  -- enumeration of polynomials of degree below two.
  exfalso
  have hdeg : ∀ c : FpPoly 3, 0 < c.size → c.degree?.getD 0 = c.size - 1 := by
    intro c hc
    have hne : c.size ≠ 0 := by omega
    simp [DensePoly.degree?, hne]
  have ha_deg : a.degree?.getD 0 < 2 := by rw [hdeg a ha_pos]; omega
  have hb_deg : b.degree?.getD 0 < 2 := by rw [hdeg b hb_pos]; omega
  have hnone : ∀ u ∈ FpPoly.Enumeration.polysBelowDegree 3 2,
      ∀ v ∈ FpPoly.Enumeration.polysBelowDegree 3 2, u * v ≠ modulus := by
    decide
  exact hnone a (FpPoly.Enumeration.mem_polysBelowDegree_of_degree_getD_lt ha_deg)
    b (FpPoly.Enumeration.mem_polysBelowDegree_of_degree_getD_lt hb_deg) hab

/-- `GF(9)`, presented as `F₃[x]/(x² + 1)`. -/
abbrev GF9 : Type :=
  GFqField.FiniteField modulus modulus_pos_degree prime_three modulus_irreducible

/-- Reduce a polynomial into `GF(9)`. -/
def ff (f : FpPoly 3) : GF9 :=
  GFqField.ofPoly modulus modulus_pos_degree prime_three modulus_irreducible f

/-- The canonical representative, as a coefficient list. -/
def coeffs (x : GF9) : List Nat :=
  (GFqField.repr x).toArray.toList.map ZMod64.toNat

/-- The adjoined square root of `-1`. -/
def i : GF9 := ff #p[0, 1]

-- The defining relation: `i² = -1`, which over `F₃` is the constant `2`.
#guard i * i = -1
#guard coeffs (i * i) = [2]

-- `(a + bi)(a - bi) = a² + b²`, the norm form, at `a = 2`, `b = 1`:
-- `4 + 1 = 5 ≡ 2 (mod 3)`. Note `-1 = 2` and `-i = 2i` in this field.
#guard ff #p[2, 1] * ff #p[2, 2] = ff #p[2]
#guard coeffs (ff #p[2, 1] * ff #p[2, 2]) = [2]

-- Inversion comes from the extended gcd in `F₃[x]`: `i · 2i = 2i² = -2 = 1`.
#guard coeffs i⁻¹ = [0, 2]
#guard i * i⁻¹ = 1
#guard ff #p[2, 1] / ff #p[2, 1] = 1

-- Frobenius `x ↦ x³` fixes the prime subfield `F₃` pointwise and conjugates
-- the square root: `i³ = i² · i = -i`.
#guard GFqField.frob (ff #p[2]) = ff #p[2]
#guard GFqField.frob i = -i
#guard coeffs (GFqField.frob i) = [0, 2]
#guard GFqField.frob (ff #p[2, 1]) = ff #p[2, 2]

-- `frob` really is the `p`-th power map, and being an endomorphism in
-- characteristic three is the freshman's dream.
#guard GFqField.frob (ff #p[2, 1]) = ff #p[2, 1] ^ (3 : Nat)
#guard (i + ff #p[1]) ^ (3 : Nat) = i ^ (3 : Nat) + ff #p[1] ^ (3 : Nat)

-- The multiplicative group of `GF(9)` is cyclic of order eight, and `1 + i`
-- generates it: `(1 + i)⁴ = -1`, so its order is not a proper divisor of `8`.
#guard ff #p[1, 1] ^ (8 : Nat) = 1
#guard ff #p[1, 1] ^ (4 : Nat) = -1

/-- Cancellation here is a theorem too, for every nonzero element. -/
example (a : GF9) (h : a ≠ 0) : a * a⁻¹ = 1 :=
  GFqField.mul_inv_cancel h

end Examples.Release1
