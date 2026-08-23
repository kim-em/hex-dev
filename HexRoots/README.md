# hex-roots

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified complex-root isolation for dense integer polynomials, implemented in
Lean 4 without Mathlib.

Each result is a dyadic square plus an exact certificate that its selected
region contains one simple root. The driver supports two certificate forms:
Newton--Kantorovich contraction on a square and Pellet/Rouché root counting on
a circumscribed disc. Search may use approximate placement hints, but every
accepted atom is rechecked with exact dyadic arithmetic.

# Quickstart

```toml
[[require]]
name = "hex-roots"
git = "https://github.com/leanprover/hex-roots.git"
rev = "main"
```

```lean
import HexRoots
```

# Functionality

```lean
import HexRoots

open Hex

def p : ZPoly := DensePoly.ofCoeffs #[-1, -1, 0, 1]

def roots : Option (Array (DyadicRootIsolation p)) :=
  if h : HasOnlySimpleRoots p then
    isolate p h 32 .nkThenPellet
  else
    none
```

`Hex.isolate p h precision strategy` returns pairwise-disjoint atoms for a
polynomial whose roots are simple. A nonzero constant returns an empty array;
the zero polynomial returns `none`. The simple-root test is executable and
decidable.

Use `.nkThenPellet` for the general strategy, `.nk` to select only the
Newton--Kantorovich certificate, or `.pellet` to select only Pellet. Returned
atoms can be refined independently with
`Hex.DyadicRootIsolation.refineTo?`.

The option type is an honest computational boundary: the core package does not
silently assume completeness. The companion package
[`hex-roots-mathlib`](https://github.com/leanprover/hex-roots-mathlib) proves
that every nonzero squarefree input succeeds and offers a none-free wrapper.

# Verification

- polynomial and Taylor arithmetic is exact;
- centres, widths, and comparisons are dyadic;
- no floating-point value appears in a certificate;
- connected components are glued by exact square adjacency; and
- the kernel checks the final witness, not the subdivision search.

The Mathlib bridge supplies the semantic statements over `Polynomial ℂ`:
existence and uniqueness inside each region, exact root count, pairwise
separation, full coverage, and preservation under refinement.

# Reference manual

- [SPEC](SPEC/hex-roots.md) — data model, algorithms, fuel, precision, and
  performance budgets.
- The Hex manual chapter “HexRoots: certified complex-root isolation”.
- `bench/HexRoots/` — deterministic degree and separation families.
- `conformance/HexRoots/` — fixtures checked against python-flint.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
