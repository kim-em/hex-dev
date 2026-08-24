# hex-resultant-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib companion for
[`hex-resultant`](https://github.com/leanprover/hex-resultant). It proves
that the executable subresultant algorithm computes `Polynomial.resultant`,
together with the chain-level and specialization facts consumed by the
number-field libraries. It depends on `hex-resultant`,
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib), and
Mathlib.

# Quickstart

```toml
[[require]]
name = "hex-resultant-mathlib"
git = "https://github.com/leanprover/hex-resultant-mathlib.git"
rev = "main"
```

```lean
import HexResultantMathlib

open Hex

example (f g : DensePoly ℤ) :
    DensePoly.resultant f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0) :=
  DensePoly.toPolynomial_resultant f g
```

# Functionality

The proof-facing API centres on the headline correspondence and its
consumer surface:

- `Hex.DensePoly.toPolynomial_resultant`: exact agreement of the executable
  resultant with Mathlib's, values rather than mere simultaneous vanishing,
  with no monicity, coprimality, or nonzero hypotheses.
- `Hex.DensePoly.resultant_eq_zero_iff_common_root`: vanishing characterizes
  a common root over a splitting field, the form used by number-field
  eliminants.
- Evaluation and specialization lemmas for resultants of mapped and
  evaluated polynomials, and the discriminant correspondence.
- Transport lemmas for pseudo-division and the subresultant minors
  (`SubresultantMinor.det_eq_matrixDet` and its relatives), which carry the
  Brown--Traub chain across the dense-polynomial correspondence.

# Verification

Everything in this package is proved; it contains no executable code of its
own. The typeclass context of the headline theorem is the executable
algorithm's own (`CommRing R`, `IsDomain R`, `DecidableEq R`, `Div R`,
`Hex.ExactDivLaws R`), so the correspondence applies to every instantiation
the computational package supports. The computational library stays
Mathlib-free; algebraic semantics live here. See the
[SPEC](SPEC/hex-resultant-mathlib.md) for the full public theorem list and
the proof architecture.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
