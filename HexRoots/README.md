# hex-roots

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. The aim is fast executable code, fully verified, built with
spec-driven development.

Certified complex-root isolation for dense integer polynomials, built on
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z) without Mathlib. Each
dyadic square carries an exact Newton--Kantorovich or Pellet certificate; the
[`hex-roots-mathlib`](https://github.com/leanprover/hex-roots-mathlib)
companion proves its semantic root-count guarantees.

# Quickstart

```toml
[[require]]
name = "hex-roots"
git = "https://github.com/leanprover/hex-roots.git"
rev = "main"
```

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

# Functionality

- `Hex.isolate p h precision strategy` returns pairwise-disjoint atoms for a
  polynomial whose roots are simple. A nonzero constant returns an empty
  array; the zero polynomial returns `none`.
- `Hex.HasOnlySimpleRoots` is an executable, decidable precondition.
- `.nkThenPellet` is the general strategy; `.nk` and `.pellet` select a single
  certificate form.
- `Hex.DyadicRootIsolation.refineTo?` refines one returned atom independently.

The option type is an honest computational boundary: the core package does not
silently assume completeness. The companion package proves that every nonzero
squarefree input succeeds and offers a none-free wrapper.

# Verification

- polynomial and Taylor arithmetic is exact;
- centres, widths, and comparisons are dyadic;
- no floating-point value appears in a certificate;
- connected components are glued by exact square adjacency; and
- the kernel checks the final witness, not the subdivision search.

The Mathlib bridge supplies the semantic statements over `Polynomial ℂ`:
existence and uniqueness inside each region, exact root count, pairwise
separation, full coverage, and preservation under refinement.

Reference material:

- [SPEC](SPEC/hex-roots.md) — data model, algorithms, fuel, precision, and
  performance budgets.
- The Hex manual chapter “HexRoots: certified complex-root isolation”.
- The benchmark families and the python-flint conformance fixtures, in
  [`hex-dev`](https://github.com/kim-em/hex-dev).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
