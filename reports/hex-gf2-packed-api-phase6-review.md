# HexGF2 Packed Polynomial API Phase 6 Review

## Scope

Reviewed the public packed-polynomial and quotient-field surface in:

- `HexGF2/Basic.lean`
- `HexGF2/Clmul.lean`
- `HexGF2/Multiply.lean`
- `HexGF2/Euclid.lean`
- `HexGF2/Field.lean`
- `HexGF2/Irreducibility.lean`
- `HexGF2/RabinSoundness.lean`

The review focused on Phase 6 API quality: characterizing lemmas, automation
annotations, docstrings, import and namespace hygiene, representation
encapsulation, and whether downstream code can reason through `GF2Poly`
operations without unfolding packed-word implementations.

## Summary

`HexGF2` is close to a Phase 6-quality computational API. The main
packed-polynomial operations have stable executable definitions and theorem
coverage at the right abstraction boundary: coefficients for construction,
addition, shifts, multiplication, division/remainder, gcd/xgcd, Rabin
irreducibility checks, and quotient-field operations are all characterized by
public lemmas. The irreducibility certificate path is also materially stronger
than the older module comment suggests: `RabinSoundness.lean` now composes the
certificate checker with Rabin soundness to produce `GF2Poly.Irreducible`.

The remaining Phase 6 work is polish rather than a missing correctness layer.
Two local follow-ups are worth doing before declaring the packed API fully
polished:

1. Promote the headline operation laws to a coherent `simp`/`grind` surface.
2. Audit `Field.lean` proof-helper declarations and hide or namespace helpers
   that are not intended as downstream API.

## Checked API Clusters

### Packed representation and coefficients

`Basic.lean` has the expected foundation:

- `GF2Poly`, `ofWords`, `ofUInt64`, `monomial`, `toWords`, `wordCount`,
  `isZero`, `IsZero`, `coeff`, `degree?`, and `degree`.
- coefficient extensionality through `ext_coeff`;
- normalization preservation through `coeffWords_normalizeWords`;
- zero, addition, monomial, and shift coefficient lemmas.

This is the strongest part of the API. Downstream callers can normally reason
with `coeff`, `degree?`, and `isZero` rather than unfolding `words` or the
normalization invariant. Docstring coverage is good, and the raw word helpers
that remain public are plausibly shared implementation API for the packed
modules.

### Carry-less multiplication

`Clmul.lean` documents the trusted extern boundary and exposes logical
reference lemmas:

- `clmul_eq_pureClmul`;
- zero laws for both `pureClmul` and `clmul`;
- one-hot and XOR-linearity lemmas.

This is an appropriate boundary: proof users can rewrite runtime `clmul` to
the pure definition when needed, while executable code keeps the extern hook.

### Multiplication

`Multiply.lean` exposes the right headline facts:

- `coeff_mul`;
- `ofUInt64_mul_ofUInt64`;
- `degree?_mul_of_degree?_eq_some`;
- `left_distrib`, `right_distrib`, `mul_comm`, `mul_assoc`;
- monomial shift laws and identity/zero laws.

The main gap is automation consistency. Only the identity and zero laws are
currently marked `[simp]`; the coefficient and algebraic characterization
lemmas are unannotated. That is conservative, but it means downstream proof
automation still has to name the headline lemmas explicitly for common goals
such as reducing `(p * q).coeff n`, distributing multiplication over packed
addition, or normalizing monomial products.

### Division, gcd, and inverses

`Euclid.lean` has a useful public surface:

- `divMod_spec`;
- `[simp]` projections and zero-divisor behavior for `divMod`, `/`, and `%`;
- `mod_degree_lt`;
- `xgcd_bezout`;
- `gcd_dvd_left`, `gcd_dvd_right`, and `dvd_gcd`;
- congruence lemmas such as `mod_add_mul_right_eq_mod`,
  `mod_eq_self_of_reduced`, and `mod_eq_of_eq_add_mul_right`;
- inverse-support lemmas for irreducible reduced residues and the packed
  single-word path.

`div_mul_add_mod` is already tagged `[grind =]`, which is the right kind of
automation anchor. The rest of the Euclidean API is usable but similarly
conservative on annotations. In particular, reduced-remainder and gcd/divisory
facts are likely to be useful to downstream Berlekamp or quotient-field code
through `grind`.

### Irreducibility checker and Rabin soundness

`Irreducibility.lean` and `RabinSoundness.lean` expose the expected Boolean
checker stack:

- `xpow2kMod`, `frobeniusDiffMod`, `rabinDividesTest`,
  `rabinCoprimeTest`, `rabinWitnesses`, and `rabinTest`;
- `IrreducibilityCertificate` and its pow-chain/Bezout checker;
- quadratic and linear pow-chain checker variants;
- checker-to-`rabinTest` soundness;
- `rabinTest_imp_irreducible`;
- checker-to-`GF2Poly.Irreducible` soundness for both checker variants.

The theorem surface satisfies the Phase 6 requirement that irreducibility
claims be backed by Lean-checked evidence. One documentation nit remains:
`Irreducibility.lean`'s module comment and the docstring on
`checkIrreducibilityCertificate_rabinTest` still describe Rabin soundness as a
future follow-up, while `RabinSoundness.lean` now provides it. This does not
break callers, but it can mislead API users reading the local module.

### Quotient-field wrappers

`Field.lean` covers both packed single-word `GF2n` and arbitrary-degree
`GF2nPoly` quotients. The public API includes reduction, value lemmas,
addition, multiplication, powers, inverses, division, Frobenius iteration,
enumeration of quotient elements, root-count support, and the finite-field
exponent/Frobenius facts needed by Rabin soundness.

The quotient APIs are usable without unfolding representation fields:
`mul_val`, `add_val`, `zero_val`, `one_val`, `sub_val`, `reducePoly_*`,
`frobeniusIter_*`, inverse cancellation, and nonzero multiplication lemmas are
available. The concern is surface size. Several proof-engineering helpers are
public from `Hex.GF2Poly`, including Boolean coefficient-list enumeration,
`ofBoolList`, divided-difference helpers, root-list helpers, `linearPow`, and
list-product helpers. Some are legitimate proof APIs for `RabinSoundness`, but
the current file does not clearly separate consumer-facing quotient operations
from internal finite-enumeration/root-count machinery.

## Follow-Up Recommendations

### HexGF2: tune packed operation automation annotations

Add a narrow Phase 6 issue to audit and tune `[simp]`/`[grind]` annotations for
the headline packed operation laws in `Basic.lean`, `Multiply.lean`,
`Euclid.lean`, and the quotient value lemmas in `Field.lean`. Candidate lemmas
include `coeff_mul`, `coeff_shiftLeft`, `coeff_mulXk`, `mul_monomial`,
`monomial_mul`, `degree?_mul_of_degree?_eq_some`, `mod_eq_self_of_reduced`,
`mod_add_mul_right_eq_mod`, `xgcd_bezout`, `mul_val`, `add_val`, `one_val`,
and `zero_val`.

The goal should be a tested automation contract, not blanket annotations.
Small examples should demonstrate that downstream callers can normalize common
coefficient, remainder, and quotient-value goals without unfolding executable
packed-word definitions.

### HexGF2: encapsulate quotient-field proof helpers

Add a narrow Phase 6 issue for `Field.lean` surface hygiene. Decide which of
the finite-enumeration and root-count helpers are intended public API, then
make purely local helpers `private` or move them under a clearly named internal
namespace. Candidate declarations for audit include `boolCoeffValues`,
`coeffBoolLists`, `ofBoolListFrom`, `ofBoolList`, `elements`,
`rootsOfCoeffList`, `dividedDifferenceCoeffs`, `dividedDifference`,
`linearPow`, and `listProd`.

The deliverable should preserve the public quotient-field facts used by
Rabin soundness while reducing accidental API exposure.

### HexGF2: refresh irreducibility checker documentation

Add a small documentation issue or fold it into the automation pass: update the
`Irreducibility.lean` module comment and checker docstrings so they point to
`RabinSoundness.lean` for the completed
`checkIrreducibilityCertificate*_imp_irreducible` theorems instead of implying
that Rabin soundness is still future work.

## Phase 6 Verdict

The packed `GF2Poly` surface is coherent and downstream-usable, and no broad
redesign is needed. Phase 6 should remain open until the automation and
surface-hygiene follow-ups are handled, with the documentation refresh as a
small cleanup item.
