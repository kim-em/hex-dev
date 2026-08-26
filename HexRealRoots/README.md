# hex-real-roots

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified real-root isolation for dense integer polynomials, implemented in
Lean 4 without Mathlib.

Every result is a sorted half-open dyadic interval `(lo, hi]` carrying an exact
Sturm-count witness that it contains one root. A complete output additionally
certifies that the intervals are pairwise disjoint and that their number equals
the total real-root count.

# Quickstart

```toml
[[require]]
name = "hex-real-roots"
git = "https://github.com/leanprover/hex-real-roots.git"
rev = "main"
```

```lean
import HexRealRoots
```

# Functionality

```lean
open Hex

def p : ZPoly := DensePoly.ofCoeffs #[-2, 0, 0, 0, 1]

#eval (isolate? p).map (fun roots => roots.isolations.size)
```

The stable executable API is:

```lean
Hex.isolate?          -- Descartes search, certified by Sturm; Sturm fallback
Hex.isolateSturm?     -- direct Sturm bisection
Hex.isolateDescartes? -- Descartes-only search, still Sturm-certified
Hex.rootCount         -- exact total real-root count
Hex.sturmCount        -- exact count in one half-open interval
```

`isolate?` rejects the zero polynomial and, at the core level, expects a
squarefree positive-degree input. Nonzero constants produce an empty result.
The Mathlib bridge's `isolate_roots` elaborator automatically passes through
the squarefree core, so end users normally do not manage repeated roots
themselves.

# Verification

Descartes' rule of signs gives a fast search heuristic. Sturm counts provide
the trust boundary and the total fallback. Every candidate interval—regardless
of which engine found it—is accepted only after an exact Sturm check, and the
final array is checked against the exact total count. Descartes contributes
speed, not trust.

All endpoint evaluation is exact dyadic Horner arithmetic. There are no floats,
numerical tolerances, or interval-arithmetic assumptions in the certificate.

# Reference manual

- [SPEC](SPEC/hex-real-roots.md) — Sturm convention, engines, totality, and
  performance budgets.
- The Hex manual chapter “HexRealRoots: certified real-root isolation”.
- `bench/HexRealRoots/` — deterministic real-root workloads.
- `conformance/HexRealRoots/` — fixtures checked against python-flint.

For semantic theorems and the user-facing elaborator, use
[`hex-real-roots-mathlib`](https://github.com/leanprover/hex-real-roots-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
