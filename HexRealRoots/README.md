# hex-real-roots

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. The aim is fast executable code, fully verified, built with
spec-driven development.

Certified real-root isolation for dense integer polynomials, built on
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z) without Mathlib. Each
half-open dyadic interval carries an exact Sturm-count witness; the
[`hex-real-roots-mathlib`](https://github.com/leanprover/hex-real-roots-mathlib)
companion proves the semantic isolation guarantees and provides `isolate_roots`.

# Quickstart

```toml
[[require]]
name = "hex-real-roots"
git = "https://github.com/leanprover/hex-real-roots.git"
rev = "main"
```

```lean
import HexRealRoots

open Hex

def p : ZPoly := DensePoly.ofCoeffs #[-2, 0, 0, 0, 1]

#eval (isolate? p).map (fun roots => roots.isolations.size)
```

# Functionality

- `Hex.isolate?` tries the Descartes search first and falls back to Sturm.
- `Hex.isolateSturm?` runs direct Sturm bisection.
- `Hex.isolateDescartes?` runs only the Descartes search, while still
  certifying every emitted interval with Sturm.
- `Hex.rootCount` computes the exact total real-root count.
- `Hex.sturmCount` computes the exact count in one half-open interval.

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

Reference material:

- [SPEC](SPEC/hex-real-roots.md) — Sturm convention, engines, totality, and
  performance budgets.
- The Hex manual chapter “HexRealRoots: certified real-root isolation”.
- The real-root benchmark workloads and the python-flint conformance
  fixtures, in [`hex-dev`](https://github.com/kim-em/hex-dev).

For semantic theorems and the user-facing elaborator, use the companion
package linked above.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
