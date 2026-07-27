# hex-roots-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Soundness, completeness, and proof-facing APIs for
[`hex-roots`](https://github.com/leanprover/hex-roots).

The package connects exact dyadic certificates to `Polynomial ℂ`. It proves
Newton--Kantorovich and Pellet atom soundness, cluster root counts, Mahler
separation, refinement preservation, pairwise disjointness, full root coverage,
and termination of the production driver on every nonzero squarefree input.

# Quickstart

```toml
[[require]]
name = "hex-roots-mathlib"
git = "https://github.com/leanprover/hex-roots-mathlib.git"
rev = "main"
```

```lean
import HexRootsMathlib
```

# Functionality

`HexRootsMathlib.isolate!` removes the executable `Option` when the caller has
the hypotheses required by completeness:

```lean
open Hex HexRootsMathlib

def p : ZPoly := DensePoly.ofCoeffs #[-1, -1, 0, 1]

-- Supply proofs once for a named polynomial.
variable (hsimple : HasOnlySimpleRoots p) (hnonzero : p ≠ 0)

noncomputable def roots : Array (DyadicRootIsolation p) :=
  isolate! p hsimple hnonzero 32
```

The associated theorems are the main consumption surface:

```lean
isolate!_eq     -- the array is the successful Hex.isolate result
isolate!_count  -- one atom per complex root
isolate!_roots  -- selected semantic roots equal p.roots.toFinset
isolate!_prec   -- every square meets the requested precision
isolate!_disjoint -- distinct squares have disjoint circumscribed discs
```

Clients that already have a successful `Hex.isolate` call can instead use
`isolate_sound`, `isolate_count`, `isolate_disjoint`, and the atom-level
semantic root API.

# Verification

The load-bearing developments are deliberately specialized to polynomials:

- a Newton--Kantorovich contraction theorem over the sup norm;
- an argument principle and Rouché theorem for polynomials on circles;
- Pellet's root-count criterion; and
- a discriminant/Mahler separation bound for integer polynomials.

This avoids a general meromorphic or contour-winding API while proving exactly
what the executable certificates need. The computational library remains
Mathlib-free; analytic and algebraic semantics live here.

See the [SPEC](SPEC/hex-roots-mathlib.md) and the Hex manual's complex-roots
chapter for the theorem chain and a complete `x³ - x - 1` example.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
