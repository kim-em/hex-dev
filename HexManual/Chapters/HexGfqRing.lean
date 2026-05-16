import VersoManual

import HexGfqRing

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGfqRing: executable Fₚ quotient ring" =>
%%%
tag := "hex-gfq-ring"
%%%

# Introduction
%%%
tag := "hex-gfq-ring-intro"
%%%

`HexGfqRing` is the canonical executable quotient-ring layer for
`Fₚ[x] / (f)` over a fixed nonconstant polynomial modulus `f` of type
{name}`Hex.FpPoly`. Elements are reduced polynomial representatives —
{name}`Hex.FpPoly` values of degree strictly below
{name}`Hex.FpPoly.degree` of `f` — and every ring operation normalizes
through {name}`Hex.GFqRing.reduceMod`, so equality of quotient elements
coincides with equality of canonical representatives.

The modulus `f` is not required to be irreducible: when `f` is reducible
the quotient is still a ring, used downstream wherever a fixed-modulus
polynomial ring is needed. When `f` is irreducible, the same underlying
representation supports a field structure, supplied by the `HexGfqField`
layer; see {ref "hex-gfq-ring-cross-references"}[Cross-references] below.

# Core types
%%%
tag := "hex-gfq-ring-core-types"
%%%

The two primitive notions are {name}`Hex.GFqRing.reduceMod` — canonical
remainder modulo `f` — and {name}`Hex.GFqRing.PolyQuotient` — the
subtype of reduced representatives.

{docstring Hex.GFqRing.reduceMod}

{docstring Hex.GFqRing.IsReduced}

{docstring Hex.GFqRing.PolyQuotient}

Two further definitions complete the user-facing surface: the smart
constructor {name}`Hex.GFqRing.ofPoly` and the projection
{name}`Hex.GFqRing.repr`. Callers never manage reduction by hand —
`ofPoly` runs the canonical reduction and `repr` reads back the stored
representative.

{docstring Hex.GFqRing.ofPoly}

{docstring Hex.GFqRing.repr}

# Principal operations
%%%
tag := "hex-gfq-ring-principal-operations"
%%%

Ring operations on {name}`Hex.GFqRing.PolyQuotient` lift the
corresponding operations on representatives and re-reduce the result.

{docstring Hex.GFqRing.zero}

{docstring Hex.GFqRing.one}

{docstring Hex.GFqRing.const}

{docstring Hex.GFqRing.add}

{docstring Hex.GFqRing.mul}

{docstring Hex.GFqRing.neg}

{docstring Hex.GFqRing.sub}

{docstring Hex.GFqRing.pow}

Exponentiation uses square-and-multiply on the exponent bits, costing
`O(log n)` quotient-ring multiplications. The natural and integer
scalar maps below use the same binary-decomposition shape — the
textbook `n + 1 ↦ pred + 1` recursion is forbidden in this library
because its cost would be linear in the scalar.

{docstring Hex.GFqRing.natCast}

{docstring Hex.GFqRing.nsmul}

{docstring Hex.GFqRing.intCast}

{docstring Hex.GFqRing.zsmul}

The standard typeclass instances `Zero`, `One`, `Add`, `Mul`, `Neg`,
`Sub`, and `Pow` on {name}`Hex.GFqRing.PolyQuotient` are defined by the
corresponding operations above, so ring-literal notation such as
`0`, `1`, `x + y`, `x * y`, `-x`, `x - y`, and `x ^ n` works over
`PolyQuotient f hf` out of the box.

## Worked example: F₅ modulo x⁴ + 2
%%%
tag := "hex-gfq-ring-worked-example"
%%%

The reduction rule for this quotient is `x⁴ ≡ -2 ≡ 3 (mod 5)`. The
example below builds the modulus, three reduced representatives `a`,
`b`, and `x`, then exercises addition, multiplication, negation,
subtraction, and exponentiation. Each `#guard` is checked when the
chapter is built, so the expected coefficient lists are guaranteed
to match what the executable implementation produces.

```lean
open Hex Hex.GFqRing

namespace HexGfqRingChapterExample

private instance : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

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

private instance : ZMod64.PrimeModulus 5 := ⟨prime_five⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have :=
    (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at this

/-- Monic degree-4 polynomial x⁴ + 2 over F₅. -/
private def modulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 0, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem modulus_pos_degree :
    0 < FpPoly.degree modulus := by decide

private def q (coeffs : Array Nat) :
    PolyQuotient modulus modulus_pos_degree :=
  ofPoly modulus modulus_pos_degree
    (FpPoly.ofCoeffs
      (coeffs.map (fun n => ZMod64.ofNat 5 n)))

private def reprNats
    (x : PolyQuotient modulus modulus_pos_degree) :
    List Nat :=
  (repr x).toArray.toList.map ZMod64.toNat

private def a : PolyQuotient modulus modulus_pos_degree :=
  q #[2, 3]
private def b : PolyQuotient modulus modulus_pos_degree :=
  q #[4, 1, 0, 1]
private def x : PolyQuotient modulus modulus_pos_degree :=
  q #[0, 1]

-- (2 + 3x) + (4 + x + x³) ≡ 1 + 4x + x³ (mod 5)
#guard reprNats (a + b) = [1, 4, 0, 1]

-- (2 + 3x)(4 + x + x³) reduced through x⁴ ≡ 3.
#guard reprNats (a * b) = [2, 4, 3, 2]

-- -(2 + 3x) ≡ 3 + 2x (mod 5)
#guard reprNats (-a) = [3, 2]

-- (2 + 3x) - (4 + x + x³) ≡ 3 + 2x + 4x³ (mod 5)
#guard reprNats (a - b) = [3, 2, 0, 4]

-- Powers of x exercising x⁴ ≡ 3.
#guard reprNats (x ^ 3) = [0, 0, 0, 1]
#guard reprNats (x ^ 4) = [3]
#guard reprNats (x ^ 5) = [0, 3]

end HexGfqRingChapterExample
```

# Key correctness theorems
%%%
tag := "hex-gfq-ring-key-correctness"
%%%

The library's exit criterion at the proof layer is a small set of
laws connecting representatives to canonical reduction. The first two
establish that the representation is canonical: a quotient element is
exactly its reduced representative, and that representative has
degree strictly below the modulus.

{docstring Hex.GFqRing.repr_ofPoly}

{docstring Hex.GFqRing.degree_repr_lt_degree}

Reduction is idempotent, so calling `reduceMod` on something already
reduced is a no-op, and the modulus reduces to zero:

{docstring Hex.GFqRing.reduceMod_idem}

{docstring Hex.GFqRing.reduceMod_self}

Reduction commutes with addition and multiplication in the strong
sense that reducing either operand before combining does not change
the final canonical representative — the laws that justify lifting
addition and multiplication to the quotient.

{docstring Hex.GFqRing.reduceMod_add_reduceMod_congr}

{docstring Hex.GFqRing.reduceMod_mul_reduceMod_congr}

The full ring axioms over canonical representatives are bundled into
the `Lean.Grind.CommRing` instance on
{name}`Hex.GFqRing.PolyQuotient`, which is the entry point for
downstream proof automation. Its existence is the gate that promotes
`HexGfqRing` to a Phase 6 grind-clean state.

# Cross-references
%%%
tag := "hex-gfq-ring-cross-references"
%%%

`HexGfqRing` sits between an upstream polynomial-arithmetic dependency
and a downstream finite-field consumer:

* `HexPolyFp` provides the `Hex.FpPoly` representation that
  {name}`Hex.GFqRing.reduceMod` operates on, together with the
  `Hex.DensePoly.divMod` and `Hex.DensePoly.mod` surface from which
  `reduceMod` is built. The univariate polynomial division laws
  packaged there are what make the canonical-representative invariant
  meaningful.
* `HexGfqField` specializes the same quotient to an irreducible
  modulus and adds the field structure. The `FiniteField` type in
  `HexGfqField` is a thin wrapper carrying a
  {name}`Hex.GFqRing.PolyQuotient` value plus the irreducibility
  hypothesis, so every operation in `HexGfqField` reduces through the
  same `reduceMod` and the same canonical-representative invariant
  documented in this chapter. Downstream consumers such as `HexConway`
  reach `HexGfqRing` transitively through `HexGfqField`.

## No Mathlib bridge library
%%%
tag := "hex-gfq-ring-no-mathlib-bridge"
%%%

Some `hex-*` libraries pair the computational layer with a `*Mathlib`
bridge library that re-exports the executable API as theorems about
the corresponding Mathlib structures. `HexGfqRing` has *no* such
bridge library: there is no `HexGfqRingMathlib`, and the chapter
therefore does not contain the "computational vs. Mathlib bridge"
cross-reference that future chapters will include for libraries that
have one.

For `HexGfqRing` the canonical mathematical home of the quotient is
Mathlib's `AdjoinRoot` or `Polynomial.quotient` construction; a
bridge between {name}`Hex.GFqRing.PolyQuotient` and those constructions
is deferred to a downstream library if and when a Mathlib-valued
consumer needs it.
