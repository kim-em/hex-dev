/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGFqField
import HexBerlekamp.RabinSoundness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGFqField: executable GF(pⁿ)" =>
%%%
tag := "hex-gfq-field"
%%%

# Introduction
%%%
tag := "hex-gfq-field-intro"
%%%

`HexGFqField` constructs the field `GF(pⁿ) = Fₚ[x] / (f)` for a prime `p`
and an irreducible degree-`n` modulus `f` of type {name}`Hex.FpPoly`. It
builds on the quotient ring documented in
{ref "hex-gfq-ring"}[the `HexGFqRing` chapter]: the field element type
{name}`Hex.GFqField.FiniteField` wraps a single
{name}`Hex.GFqRing.PolyQuotient` value, and every operation delegates to
quotient-ring arithmetic and re-reduces, so the canonical-representative
invariant from `HexGFqRing` carries over unchanged.

What the field adds over the ring is the structure that only exists when
the modulus is irreducible: multiplicative inverses (via the polynomial
extended GCD), division, integer powers, and the Frobenius endomorphism
`a ↦ aᵖ`. Irreducibility is a hypothesis
{name}`Hex.FpPoly.Irreducible` carried in the type of every field
element, discharged in practice by a checkable Rabin certificate from
{ref "hex-gfq-field-cross-references"}[`HexBerlekamp`].

# Field type and constructors
%%%
tag := "hex-gfq-field-core-type"
%%%

A field element is a quotient-ring residue together with the modulus
data and the irreducibility witness, all carried in the type. The
hypotheses `hf : 0 < FpPoly.degree f` and `hirr : FpPoly.Irreducible f`
(plus primality of `p`) appear as explicit arguments so that the field
structure is only available where it is justified.

{docstring Hex.GFqField.FiniteField}

Callers build elements through two smart constructors and read them back
through one projection. {name}`Hex.GFqField.ofQuotient` wraps an existing
quotient residue, {name}`Hex.GFqField.ofPoly` reduces a raw polynomial
into the field, and {name}`Hex.GFqField.repr` recovers the canonical
representative, always of degree strictly below the modulus.

{docstring Hex.GFqField.ofQuotient}

{docstring Hex.GFqField.ofPoly}

{docstring Hex.GFqField.repr}

The projection is canonical: representatives are always reduced below the
modulus degree, and equality of field elements is equality of their
quotient residues.

{docstring Hex.GFqField.degree_repr_lt_degree}

# Field operations
%%%
tag := "hex-gfq-field-operations"
%%%

The ring operations re-use the quotient-ring path directly: each wraps
the corresponding {name}`Hex.GFqRing.PolyQuotient` operation and rewraps
the reduced result.

{docstring Hex.GFqField.add}

{docstring Hex.GFqField.mul}

{docstring Hex.GFqField.neg}

{docstring Hex.GFqField.sub}

{docstring Hex.GFqField.pow}

The constructors for literals reuse the quotient-ring casts, so natural
and integer literals such as `0`, `1`, `7`, and `-3` denote field
elements directly.

{docstring Hex.GFqField.natCast}

{docstring Hex.GFqField.intCast}

The operations that need irreducibility come next. Inversion runs the
polynomial extended GCD on the representative and the modulus, then
normalizes the Bézout coefficient by the constant unit factor of the
gcd; irreducibility is exactly what forces that gcd to be a nonzero
constant for any nonzero element. Division is multiplication by the
inverse, and Frobenius is the `p`-th power map.

{docstring Hex.GFqField.inv}

{docstring Hex.GFqField.div}

{docstring Hex.GFqField.frob}

The standard typeclass instances `Zero`, `One`, `Add`, `Mul`, `Neg`,
`Sub`, `Pow`, `Inv`, and `Div` on {name}`Hex.GFqField.FiniteField` are
backed by these operations, so ordinary field notation
(`x + y`, `x * y`, `-x`, `x - y`, `x ^ n`, `x⁻¹`, and `x / y`) works
over a `FiniteField`.

## Worked example: GF(5⁴) as F₅ modulo x⁴ + 2
%%%
tag := "hex-gfq-field-worked-example"
%%%

The example below builds the same modulus `x⁴ + 2` used in the
{ref "hex-gfq-ring-worked-example"}[`HexGFqRing` worked example], whose
reduction rule is `x⁴ ≡ -2 ≡ 3 (mod 5)`, but now exercises the field
operations: inverses, division, and Frobenius alongside the ring
operations. Irreducibility of the modulus is discharged by a Rabin
{name}`Hex.Berlekamp.IrreducibilityCertificate`, whose pow chain and
Bézout witness are checked by the kernel-reducible
{name}`Hex.Berlekamp.checkIrreducibilityCertificateLinear` and routed to
{name}`Hex.FpPoly.Irreducible` through
{name}`Hex.Berlekamp.rabinTest_imp_irreducible`. Each `#guard` is checked
when the chapter builds.

```lean
open Hex Hex.GFqField

namespace HexGFqFieldChapterExample

private instance : ZMod64.Bounds 5 :=
  ⟨by decide, by decide⟩

private theorem one_ne_zero_five :
    (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm :=
    (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 :=
      Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases :
        m = 0 ∨ m = 1 ∨ m = 2 ∨
        m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private instance : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs
    (coeffs.map (fun n => ZMod64.ofNat 5 n))

/-- Monic degree-4 modulus x⁴ + 2 over F₅. -/
private def modulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 0, 0, 1]
    normalized := by
      right
      decide }

private theorem modulus_pos_degree :
    0 < FpPoly.degree modulus := by decide

private theorem modulus_monic :
    DensePoly.Monic modulus := by rfl

private theorem maxProperDiv_4 :
    Berlekamp.maximalProperDivisors 4 = [2] := by
  decide

/-- Rabin irreducibility certificate for x⁴ + 2. -/
private def cert :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 4
  powChain :=
    #[polyFive #[0, 1], polyFive #[0, 3],
      polyFive #[0, 4], polyFive #[0, 2],
      polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3]
        right := polyFive #[0, 0, 0, 4] }]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 8000000 in
private theorem cert_check :
    Berlekamp.checkIrreducibilityCertificateLinear
        modulus modulus_monic cert = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    cert, Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness,
    Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4, modulus, polyFive]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases :
            x = 0 ∨ x = 1 ∨ x = 2 ∨
            x = 3 ∨ x = 4 := by omega
        rcases hcases with
          rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem modulus_irreducible :
    FpPoly.Irreducible modulus :=
  have h :=
    Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      modulus modulus_monic cert cert_check
  Berlekamp.rabinTest_imp_irreducible
    modulus modulus_monic h

private abbrev F :=
  FiniteField modulus modulus_pos_degree
    prime_five modulus_irreducible

private def ff (coeffs : Array Nat) : F :=
  ofPoly modulus modulus_pos_degree
    prime_five modulus_irreducible (polyFive coeffs)

private def reprNats (x : F) : List Nat :=
  (repr x).toArray.toList.map ZMod64.toNat

private def a : F := ff #[2, 3]
private def b : F := ff #[4, 1, 0, 1]
private def x : F := ff #[0, 1]

-- (2 + 3x) + (4 + x + x³) ≡ 1 + 4x + x³
#guard reprNats (a + b) = [1, 4, 0, 1]
-- (2 + 3x)(4 + x + x³), reduced via x⁴ ≡ 3
#guard reprNats (a * b) = [2, 4, 3, 2]
-- -(2 + 3x) ≡ 3 + 2x
#guard reprNats (-a) = [3, 2]
-- (2 + 3x) - (4 + x + x³) ≡ 3 + 2x + 4x³
#guard reprNats (a - b) = [3, 2, 0, 4]
-- x⁴ ≡ 3, the modulus relation
#guard reprNats (x ^ 4) = [3]
-- a⁻¹ from extended gcd: (2+3x)(1+x+x²+x³) ≡ 1
#guard reprNats a⁻¹ = [1, 1, 1, 1]
#guard a * a⁻¹ = 1
-- x⁻¹ = 2x³ since x·2x³ = 2x⁴ = 2·3 = 1
#guard reprNats x⁻¹ = [0, 0, 0, 2]
-- a / b = a · b⁻¹
#guard reprNats (a / b) = [2, 3, 3]
#guard a / b = a * b⁻¹
-- Frobenius x ↦ x⁵ : (2 + 3x)⁵ = 2 + 4x
#guard reprNats (frob a) = [2, 4]
#guard frob a = a ^ (5 : Nat)

end HexGFqFieldChapterExample
```

# Key correctness theorems
%%%
tag := "hex-gfq-field-key-correctness"
%%%

The proof obligations that promote the wrapper from a ring to a field
are the inverse-cancellation laws. For any nonzero element, the
extended-GCD inverse is a genuine two-sided multiplicative inverse.

{docstring Hex.GFqField.mul_inv_cancel}

{docstring Hex.GFqField.inv_mul_cancel}

Division is definitionally multiplication by the inverse, and the field
is nontrivial (`0 ≠ 1`), which is where irreducibility (hence a
positive-degree modulus) is used.

{docstring Hex.GFqField.div_eq_mul_inv}

{docstring Hex.GFqField.zero_ne_one}

The Frobenius endomorphism is definitionally the `p`-th power map, the
form the rest of the finite-field theory consumes.

{docstring Hex.GFqField.frob_eq_pow}

These laws, together with the ring axioms inherited from `HexGFqRing`,
are bundled into a `Lean.Grind.Field` instance on
{name}`Hex.GFqField.FiniteField`, plus a `Lean.Grind.IsCharP` instance
recording characteristic `p`. That instance is the entry point for
downstream proof automation over the executable finite field.

# Cross-references
%%%
tag := "hex-gfq-field-cross-references"
%%%

`HexGFqField` has two upstream dependencies and serves the
finite-field-valued callers downstream:

* `HexGFqRing` (see {ref "hex-gfq-ring"}[its chapter]) supplies the
  underlying {name}`Hex.GFqRing.PolyQuotient` representation and all of
  the ring arithmetic. A `FiniteField` is a one-field wrapper around a
  `PolyQuotient`, and every field operation reduces through the same
  {name}`Hex.GFqRing.reduceMod`, so the canonical-representative
  invariant documented there carries over verbatim.
* `HexBerlekamp` provides the irreducibility infrastructure. The
  {name}`Hex.FpPoly.Irreducible` hypothesis carried by every field
  element is, in practice, produced from a checkable Rabin
  {name}`Hex.Berlekamp.IrreducibilityCertificate` via
  {name}`Hex.Berlekamp.rabinTest_imp_irreducible`, as shown in the
  worked example above.

Downstream, `HexConway` builds Conway polynomials and canonical GF(pⁿ)
constructions on top of this field, reaching `HexGFqRing`
transitively through `HexGFqField`.

## No Mathlib correspondence library
%%%
tag := "hex-gfq-field-no-mathlib-correspondence"
%%%

Like {ref "hex-gfq-ring-no-mathlib-correspondence"}[`HexGFqRing`],
`HexGFqField` is a purely computational library with *no* paired
`*Mathlib` correspondence: there is no `HexGFqFieldMathlib`, and
this chapter therefore carries no "computational vs. Mathlib
correspondence" cross-reference. The canonical mathematical home of
GF(pⁿ) is Mathlib's `GaloisField` / `AdjoinRoot` construction; a
correspondence between {name}`Hex.GFqField.FiniteField` and those
structures is deferred to a downstream library if and when a
Mathlib-valued caller needs it.
