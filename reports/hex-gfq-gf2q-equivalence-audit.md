# HexGFq GF2q Equivalence Audit

## Summary

The packed-to-generic `GF2q` surface is split across three layers:

- `HexGFq/Basic.lean` exposes executable Mathlib-free constructors,
  representative projections, and the one-way map `GF2q.toGFq`.
- `HexGFq/CrossCheck.lean` gives executable packed-vs-generic operation
  checks for ad-hoc binary moduli at degrees 4, 8, 16, and 32.
- `HexGFqMathlib/GF2q.lean` already contains the intended named bridge
  surface, `Hex.GF2q.equivGFq`, but its proof and supporting transport
  lemmas still contain `sorry`.

So the missing work is not designing a new API from scratch. It is finishing
the existing bridge-layer equivalence proof and the upstream proof obligations
it depends on.

## Mathlib-Free Surface

`HexGFq/Basic.lean` defines the generic Conway-backed constructor API in
namespace `Hex.GFq`:

- `GFq.modulus`
- `GFq.ofPoly`
- `GFq.repr`
- `GFq.ext`
- representative lemmas for `0`, `1`, addition, multiplication, negation,
  subtraction, casts, powers, inverse, and division

The optimized binary constructor is:

- `abbrev GF2q (n : Nat) [h : Conway.PackedGF2Entry n]`

Its local namespace exposes the packed Conway data and representative surface:

- `GF2q.supportedEntry`
- `GF2q.lower`
- `GF2q.modulus`
- `GF2q.conway_eq_packed`
- `GF2q.gfq_modulus_eq_packedFpPoly`
- `GF2q.degree_pos`
- `GF2q.degree_lt_word`
- `GF2q.modulus_irreducible`
- `GF2q.ofWord`
- `GF2q.repr`
- `GF2q.wordFpPoly`
- `GF2q.reprFpPoly`
- `GF2q.toGFq`
- `GF2q.toGFq_eq_ofPoly`
- `GF2q.toGFq_ofWord`
- `GF2q.toGFq_repr`
- `GF2q.ext`
- representative lemmas for packed arithmetic

This is a good Mathlib-free boundary: it gives an executable map from packed
values into the canonical generic `GFq 2 n h.entry` model without importing
Mathlib's equivalence hierarchy.

## Cross-Checks

`HexGFq/CrossCheck.lean` is an executable fast-vs-fast comparison, not a proof
of equivalence. It constructs matching packed and generic finite-field models
for selected binary moduli and checks the same input stream through both.

The checked operations are:

- addition via `matchesAdd`
- multiplication via `matchesMul`
- inverse via `matchesInv`
- Frobenius via `matchesFrob`

The checked degrees are:

- `N4`
- `N8`
- `N16`
- `N32`

Each namespace uses `streamSize := 100` and four `#guard` checks. The file is
valuable as an executable regression guard, but it does not expose reusable
theorems for `GF2q.equivGFq`.

## Existing Equivalence Infrastructure

`HexGF2Mathlib/Basic.lean` defines project-local equivalence records:

- `HexGF2Mathlib.TypeEquiv`
- `HexGF2Mathlib.RingEquiv`
- notation for `RingEquiv`
- `RingEquiv.symm`

It also defines the packed-polynomial conversion layer:

- `HexGF2Mathlib.GF2Poly.toFpPoly`
- `HexGF2Mathlib.GF2Poly.ofFpPoly`
- `HexGF2Mathlib.GF2Poly.equiv`
- finite-index helpers such as `toNat` and `ofNatBelowDegree`

`HexGF2Mathlib/Field.lean` lifts that polynomial correspondence to packed
binary extension fields:

- `HexGF2Mathlib.GF2n.modulusFpPoly`
- `HexGF2Mathlib.GF2n.GenericFiniteField`
- `HexGF2Mathlib.GF2n.toGeneric`
- `HexGF2Mathlib.GF2n.ofGeneric`
- `HexGF2Mathlib.GF2n.equiv`
- `HexGF2Mathlib.GF2n.finEquiv`
- analogous `GF2nPoly` definitions for arbitrary packed moduli

This is the right reusable infrastructure for the `GF2q` bridge. It already
targets the generic `GFqField.FiniteField` model over the packed modulus viewed
as an `FpPoly 2`.

## Current Bridge Surface

`HexGFqMathlib/GF2q.lean` is the file that directly answers the SPEC sketch.
It imports `HexGFqMathlib.Basic`, `HexGF2Mathlib.Field`, and
`Mathlib.Algebra.Ring.Equiv`, then defines:

- `Hex.GF2q.modulusFpPoly_eq_conway`
- `Hex.GF2q.genericField_eq_conway`
- private `Hex.GF2q.genericEquivGFq`
- `Hex.GF2q.equivGFq : RingEquiv (GF2q n) (GFq 2 n h.entry)`

The name `GF2q.equivGFq` therefore exists, but it is not finished. The file
still has `sorry` in the cast compatibility lemmas, modulus identification,
generic-field type identification, and the final equivalence laws.

`HexGFqMathlib/Basic.lean` supplies the generic `GFq` Mathlib bridge:

- `FiniteField.field`
- `FiniteField.reducedRepEquiv`
- `FiniteField.finEquiv`
- `GFq.fintype`
- `GFq.fintype_card`
- `GFq.modulus_degree`
- `GFq.fintype_card_eq_pow`
- `GFq.equivGaloisField`

It also still contains `sorry` in reduced-representative indexing,
representative equivalence, and `GFq.modulus_degree`. Those are blockers for
fully closing the Mathlib bridge but are separate from the public shape of
`GF2q.equivGFq`.

## Blockers

The narrow blockers for `GF2q.equivGFq` are bridge-layer proof gaps:

- `HexGF2Mathlib/Basic.lean`: `RingEquiv.symm` and the polynomial
  conversion/equivalence lemmas are still sorry-backed.
- `HexGF2Mathlib/Field.lean`: `GF2n.modulusFpPoly_degree_pos`,
  `GF2n.modulusFpPoly_irreducible`, inverse laws, and operation preservation
  for `GF2n.equiv` are still sorry-backed.
- `HexGFqMathlib/GF2q.lean`: the final Conway-modulus transport and composed
  `GF2q.equivGFq` laws are still sorry-backed.
- `HexGFqMathlib/Basic.lean`: generic finite-field reduced-representative
  indexing and `GFq.modulus_degree` are still sorry-backed, affecting the
  broader GFq Mathlib bridge.

There is no evidence that `HexGFq/Basic.lean` should import Mathlib or host a
Mathlib `RingEquiv`. The Mathlib-free file should keep `GF2q.toGFq` and its
representative lemmas; the equivalence belongs in the bridge.

## Recommended Next Issue

Recommended issue:

Title: `HexGFqMathlib: finish GF2q.equivGFq bridge proof`

Target files:

- `HexGFqMathlib/GF2q.lean`
- as needed, prerequisite proof gaps in `HexGF2Mathlib/Basic.lean` and
  `HexGF2Mathlib/Field.lean`

Expected deliverables:

- Prove `Hex.GF2q.modulusFpPoly_eq_conway`.
- Prove `Hex.GF2q.genericField_eq_conway`.
- Finish private `Hex.GF2q.genericEquivGFq`.
- Finish `Hex.GF2q.equivGFq : RingEquiv (GF2q n) (GFq 2 n h.entry)`.
- Remove all `sorry` from `HexGFqMathlib/GF2q.lean`.

Dependencies:

- Existing `HexGF2Mathlib.GF2n.equiv` should be made sorry-free first, or the
  issue should explicitly include the prerequisite `GF2n` equivalence proof
  gaps from `HexGF2Mathlib/Field.lean`.
- If the final theorem needs Mathlib's `RingEquiv` instead of the project-local
  `HexGF2Mathlib.RingEquiv`, add a separate follow-up after the project-local
  bridge is complete.

Layer:

- Bridge-layer / Mathlib-side. Do not move this into Mathlib-free `HexGFq`.

Verification:

- `lake build HexGFqMathlib`
- `python3 scripts/check_dag.py`
- `git diff --check`
- Forbidden-token grep over touched Lean files finds no added `sorry`,
  `axiom`, `native_decide`, `TODO`, or `FIXME`.
