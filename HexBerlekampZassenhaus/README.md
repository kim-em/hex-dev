# hex-berlekamp-zassenhaus

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Executable factorization of dense univariate polynomials over `ℤ`, written in
Lean 4 and independent of Mathlib.

The library implements the full production cascade:

- content, sign, powers of `X`, and multiplicities are normalized first;
- Berlekamp factorization supplies modular factors;
- multifactor Hensel lifting raises them to a reconstruction precision;
- classical size-ordered recombination handles small modular factor counts;
- CLD/LLL recombination handles larger counts; and
- exact trial division is the unconditional total backstop.

The public result separates the signed scalar from primitive polynomial
factors and records multiplicities explicitly. This matches the conventions of
FLINT, Sage, and SymPy and avoids treating integer content as a polynomial
factor.

# Quickstart

Add the released package to a Lake project, pinning a tag or commit:

```toml
[[require]]
name = "hex-berlekamp-zassenhaus"
git = "https://github.com/leanprover/hex-berlekamp-zassenhaus.git"
rev = "main"
```

Then import the supported umbrella:

```lean
import HexBerlekampZassenhaus
```

The package uses native code supplied transitively by `hex-lll`; consumers do
not need Mathlib. Projects that want the correspondence theorems or tactics for
`Polynomial ℤ` should use
[`hex-berlekamp-zassenhaus-mathlib`](https://github.com/leanprover/hex-berlekamp-zassenhaus-mathlib).

# Functionality

```lean
open Hex

def f : ZPoly :=
  DensePoly.ofCoeffs #[1000, 1] *
  DensePoly.ofCoeffs #[-2003, 1] *
  DensePoly.ofCoeffs #[1, 0, 1]

def result : Factorization := f.factorize

#eval result.scalar
#eval result.factors.size
```

The stable entry points are:

```lean
Hex.ZPoly.factorize       -- ZPoly → Factorization, total
Hex.ZPoly.factors         -- ZPoly → Array (ZPoly × Nat)
Hex.factorClassical       -- classical recombination, Option-valued
Hex.factorLattice         -- lattice recombination, Option-valued
Hex.factorTrial           -- exact total fallback
Hex.Factorization.product -- reconstruct the input
```

`factorize` is the normal user API. The tier-specific operations are exposed
for benchmarking, diagnosis, and clients with a known workload.

# Verification

The computational package returns executable data. Its checkers, records, and
Mathlib-free irreducibility notion are designed so a proof layer can certify
that data without trusting search. The complete product, irreducibility,
normalization, and uniqueness theorems live in the Mathlib bridge.

The public cascade is total because `factorTrial` does not depend on finding an
admissible modular prime. The stronger claim that lattice recombination
succeeds without the exponential fallback is intentionally separate and
conditional on its explicit admissibility and precision hypotheses.

# Tactics

Importing this package extends the shared `factor_poly` and `irreducibility`
elaborators to `Hex.ZPoly`. Search runs in compiled code at elaboration time;
the generated term contains small product and irreducibility-certificate
checks, not a replay of the factorizer.

```lean
open Hex

def g : ZPoly := DensePoly.ofCoeffs #[1, 0, 1]

noncomputable def gFactored := factor_poly g
theorem gIrreducible : ZPoly.Irreducible g := irreducibility g
```

The Mathlib bridge adds `Polynomial ℤ`, multi-prime irreducibility
certificates, and deliberately marked `factor_poly!` / `irreducibility!`
fallbacks for small inputs outside the ordinary certificate languages.

# Reference manual

- [SPEC](SPEC/hex-berlekamp-zassenhaus.md) — algorithms, contracts, edge cases,
  performance policy, and trust model.
- The Hex manual's factor-tactics chapter — checked end-to-end examples.
- `bench/HexBerlekampZassenhaus/` — deterministic benchmark drivers.
- `conformance/HexBerlekampZassenhaus/` — fixture emission and conformance
  checks against python-flint.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
