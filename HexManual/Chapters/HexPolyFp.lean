import VersoManual

import HexPolyFp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyFp: prime-field dense polynomials" =>
%%%
tag := "hex-poly-fp"
%%%

# Introduction
%%%
tag := "hex-poly-fp-intro"
%%%

`HexPolyFp` specializes the executable dense-polynomial layer to the
prime-field candidate `Hex.ZMod64 p`. Where {ref "hex-poly"}[`HexPoly`]
is generic over any coefficient type with a `Zero` and a `DecidableEq`,
`HexPolyFp` fixes the coefficients to machine-word residues modulo a
prime `p` and adds the operations that only make sense over `` `Fₚ` ``:
modular exponentiation and composition in `` `Fₚ[x] / (f)` ``, the
Frobenius-power maps `X ↦ X^(pᵏ)`, square-free (Yun) decomposition, and
the quotient-by-modulus surface that becomes a field exactly when the
modulus is irreducible.

The core type {name}`Hex.FpPoly` is a thin `abbrev` over
{name}`Hex.DensePoly`, so the entire constructor, arithmetic, and
Euclidean API documented in the {ref "hex-poly"}[`HexPoly` chapter] is
available unchanged; this chapter covers only what the prime-field
specialization adds on top. `HexPolyFp` is Mathlib-free; it depends on
{ref "hex-poly"}[`HexPoly`] for the representation and on
{ref "hex-mod-arith"}[`HexModArith`] for the `ZMod64 p` coefficient
arithmetic. See {ref "hex-poly-fp-cross-references"}[Cross-references].

# Core type
%%%
tag := "hex-poly-fp-core-type"
%%%

A prime-field polynomial is a dense polynomial whose coefficients are
`ZMod64 p` residues. The `ZMod64.Bounds p` instance carries the proof
that `p` fits in a machine word, so arithmetic stays in the fast path.

{docstring Hex.FpPoly}

Because {name}`Hex.FpPoly` unfolds to {name}`Hex.DensePoly`, the
`HexPolyFp` namespace re-exports the constructors and queries a caller
needs at the specialized type — {name}`Hex.FpPoly.ofCoeffs` builds a
polynomial from a coefficient array, {name}`Hex.FpPoly.X` is the
indeterminate, and {name}`Hex.FpPoly.modByMonic` reduces modulo a monic
divisor. The irreducibility predicate the field surface is gated on is
also stated here.

{docstring Hex.FpPoly.Irreducible}

# Principal operations
%%%
tag := "hex-poly-fp-operations"
%%%

The headline operations all work in the quotient ring
`` `Fₚ[x] / (f)` `` for a monic modulus `f`. Modular exponentiation
raises a base to a power and reduces, and modular composition
substitutes one polynomial into another and reduces — both by
Horner-style loops that re-reduce at every step, so intermediate
results never grow past the modulus degree.

{docstring Hex.FpPoly.powModMonic}

{docstring Hex.FpPoly.composeModMonic}

The Frobenius-power maps are the engine of finite-field irreducibility
and factorization tests. {name}`Hex.FpPoly.frobeniusXMod` computes the
basic generator `X^p mod f`, and {name}`Hex.FpPoly.frobeniusXPowMod`
iterates it to `X^(pᵏ) mod f` for arbitrary `k`.

{docstring Hex.FpPoly.frobeniusXMod}

{docstring Hex.FpPoly.frobeniusXPowMod}

Square-free decomposition runs Yun's algorithm over `` `Fₚ` ``. The
result bundles a scalar unit with a list of square-free factors and
their multiplicities; the two record types name those pieces.

{docstring Hex.FpPoly.SquareFreeFactor}

{docstring Hex.FpPoly.SquareFreeDecomposition}

{docstring Hex.FpPoly.squareFreeDecomposition}

The inverse operation reassembles a polynomial from a decomposition by
raising each factor to its multiplicity and multiplying — useful both
as documentation of the record's meaning and as the reconstruction side
of the correctness laws below.

{docstring Hex.FpPoly.weightedProduct}

# The quotient-by-modulus surface
%%%
tag := "hex-poly-fp-quotient"
%%%

`HexPolyFp` packages the quotient `` `Fₚ[x] / (g)` `` as a type of
canonical representatives: each element stores the unique polynomial of
degree below the modulus, together with a proof of that bound.

{docstring Hex.FpPoly.Quotient}

The quotient is unconditionally a commutative ring. It becomes a
*field* only when `g` is irreducible — and `HexPolyFp` parametrizes
over that fact rather than deciding it. There is no unconditional
`Field` instance; instead the field-promoting axioms are theorems that
take `FpPoly.Irreducible g` as an explicit hypothesis. A downstream
caller supplies an irreducibility witness (in practice a checkable
Rabin certificate from `HexBerlekamp`), and only then are inverses
available. The inverse-cancellation laws are stated in
{ref "hex-poly-fp-key-correctness"}[Key correctness theorems].

## Worked example: arithmetic over F₅
%%%
tag := "hex-poly-fp-worked-example"
%%%

The block below works over `FpPoly 5`. It fixes the monic quadratic
modulus `x² + 2` (whose reduction rule is `x² ≡ -2 ≡ 3 (mod 5)`) and a
linear modulus `x + 3`, then exercises modular exponentiation,
Frobenius, composition, weighted products, and square-free
decomposition. The helper `coeffNats` reads a polynomial back as a list
of natural-number coefficients. Each `#guard` is checked when the
chapter is built, so the expected coefficient lists are guaranteed to
match what the executable implementation produces — these values are
the same ones pinned by the library's conformance suite.

```lean
open Hex Hex.FpPoly

namespace HexPolyFpChapterExample

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

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def sfFactorFive
    (coeffs : Array Nat) (multiplicity : Nat) :
    SquareFreeFactor 5 :=
  { factor := polyFive coeffs, multiplicity }

private def sfSummary
    (d : SquareFreeDecomposition 5) :
    Nat × List (List Nat × Nat) :=
  (d.unit.toNat,
    d.factors.map
      (fun sf => (coeffNats sf.factor, sf.multiplicity)))

private def sfReconstruction
    (d : SquareFreeDecomposition 5) : FpPoly 5 :=
  DensePoly.C d.unit * weightedProduct d.factors

-- Monic modulus x² + 2 over F₅, with x² ≡ 3.
private def quadModulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem quadModulus_monic :
    DensePoly.Monic quadModulus := by rfl

-- Monic linear modulus x + 3 over F₅.
private def linearModulus : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem linearModulus_monic :
    DensePoly.Monic linearModulus := by rfl

-- (x + 1)³ mod (x² + 2) ≡ x.
#guard
  coeffNats
    (powModMonic (polyFive #[1, 1]) quadModulus
      quadModulus_monic 3) = [0, 1]
-- Exponent zero is the quotient-ring identity 1.
#guard
  coeffNats
    (powModMonic (polyFive #[0, 0, 1]) quadModulus
      quadModulus_monic 0) = [1]
-- Frobenius generator X⁵ mod (x² + 2) ≡ 4x.
#guard
  coeffNats
    (frobeniusXMod quadModulus quadModulus_monic)
      = [0, 4]
-- X⁵ mod (x + 3) ≡ 2, a constant.
#guard
  coeffNats
    (frobeniusXMod linearModulus linearModulus_monic)
      = [2]
-- frobeniusXPowMod _ _ 0 reduces X.
#guard
  coeffNats
    (frobeniusXPowMod quadModulus quadModulus_monic 0)
      = [0, 1]
-- Compose (3 + 2x + x²) with (1 + x) mod (x² + 2).
#guard
  coeffNats
    (composeModMonic (polyFive #[3, 2, 1])
      (polyFive #[1, 1]) quadModulus quadModulus_monic)
      = [4, 4]
-- The weighted product of (x + 1)² is x² + 2x + 1.
#guard
  coeffNats
    (weightedProduct [sfFactorFive #[1, 1] 2])
      = [1, 2, 1]
-- The empty product is the constant 1.
#guard
  coeffNats
    (weightedProduct
      ([] : List (SquareFreeFactor 5)))
      = [1]
-- Square-free decomposition: x² + 2x + 1 = (x + 1)².
#guard
  sfSummary
    (squareFreeDecomposition prime_five
      (polyFive #[1, 2, 1]))
      = (1, [([1, 1], 2)])
-- The decomposition reconstructs its input.
#guard
  let f := polyFive #[1, 2, 1]
  coeffNats
    (sfReconstruction
      (squareFreeDecomposition prime_five f))
      = coeffNats f

end HexPolyFpChapterExample
```

# Key correctness theorems
%%%
tag := "hex-poly-fp-key-correctness"
%%%

The executable operations are pinned to their mathematical meaning.
Modular composition agrees with the spelled-out "compose then take the
remainder" definition, and the Frobenius iterate reduces to the
absolute monomial it represents — the identity Rabin's irreducibility
test relies on.

{docstring Hex.FpPoly.composeModMonic_eq_mod}

{docstring Hex.FpPoly.frobeniusXPowMod_mod_eq_monomial_mod}

Square-free decomposition is correct in two senses: every emitted
factor is genuinely square-free, and the unit-times-weighted-product
reconstructs the original polynomial. The multiplicities are positive,
so the factor list carries no padding.

{docstring Hex.FpPoly.squareFreeDecomposition_factors_squareFree}

{docstring Hex.FpPoly.squareFreeDecomposition_weightedProduct}

{docstring Hex.FpPoly.squareFreeDecomposition_multiplicity_pos}

The field-promoting laws on the quotient are the inverse-cancellation
theorems. Each carries `FpPoly.Irreducible g` as a hypothesis: for an
irreducible modulus every nonzero quotient element has a genuine
two-sided multiplicative inverse, which is exactly what fails for a
reducible modulus (where a nonzero zero-divisor has no inverse).

{docstring Hex.FpPoly.Quotient.mul_inv_cancel}

{docstring Hex.FpPoly.Quotient.inv_mul_cancel}

# Cross-references
%%%
tag := "hex-poly-fp-cross-references"
%%%

`HexPolyFp` sits one level above the base polynomial layer and supplies
the prime-field specialization the finite-field stack is built on:

* {ref "hex-poly"}[`HexPoly`] is the generic dense-polynomial layer.
  {name}`Hex.FpPoly` is an `abbrev` over {name}`Hex.DensePoly`, so every
  constructor, arithmetic, evaluation, and Euclidean operation
  documented in that chapter is inherited at the specialized type; the
  concrete `DivModLaws`/`GcdLaws` the generic Euclidean laws are stated
  under are discharged here for `ZMod64 p`.
* {ref "hex-mod-arith"}[`HexModArith`] supplies the `ZMod64 p`
  coefficient arithmetic — the machine-word modular add, multiply, and
  inverse that every operation in this chapter ultimately calls, along
  with the `ZMod64.Bounds`/`ZMod64.PrimeModulus` instances the
  prime-field surface requires.

Downstream, the finite-field libraries consume `HexPolyFp` directly:
`HexGFqRing` builds the quotient ring `` `Fₚ[x] / (g)` `` and
{ref "hex-gfq-field"}[`HexGFqField`] promotes it to a field using the
irreducibility-gated inverse laws documented above, with the
{name}`Hex.FpPoly.Irreducible` witness produced by a checkable Rabin
certificate from `HexBerlekamp`.
