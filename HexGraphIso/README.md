# hex-graph-iso

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Canonical labelling and isomorphism of finite simple undirected graphs with
ordered vertex colours, compatible with the pinned dense configuration of
nauty 2.9.3, plus a `graph_iso` tactic that closes positive and negative
goals through the kernel. It builds on
[`hex-basic`](https://github.com/leanprover/hex-basic) and
[`hex-matrix`](https://github.com/leanprover/hex-matrix), and ships the
one-file `HexGraph` graph representation it is specified against.
Correspondence with Mathlib's `SimpleGraph` lives in
[`hex-graph-iso-mathlib`](https://github.com/leanprover/hex-graph-iso-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-graph-iso"
git = "https://github.com/leanprover/hex-graph-iso.git"
rev = "main"
```

```lean
import HexGraphIso

open Hex Hex.GraphIso

def p3 : Graph 3 := Graph.ofEdges [(0, 1), (1, 2)]
def p3' : Graph 3 := Graph.ofEdges [(0, 1), (0, 2)]
def k3 : Graph 3 := Graph.ofEdges [(0, 1), (1, 2), (0, 2)]

#eval Graph.Checked.isIso p3 p3'

example : Graph.Isomorphic p3 p3' := by graph_iso
example : ¬ Graph.Isomorphic p3 k3 := by graph_iso

-- and the same on ordered colours, where an isomorphism preserves
-- each colour index
def p3c : Colored 3 1 := p3.singleColor
def k3c : Colored 3 1 := k3.singleColor

example : ¬ Isomorphic p3c k3c := by graph_iso
```

# Functionality

- `Graph n` is a finite simple undirected graph on `Fin n` with executable
  symmetric irreflexive adjacency, the checked edge-list builder `ofEdges?`,
  neighbour arrays, and relabelling. `Colored n k` adds an ordered,
  surjective colouring by `Fin k`; an isomorphism preserves each colour index
  and never permutes cells.
- The public surface has two tiers. The names `canonicalize`, `canon`,
  `label`, `findIso`, and `isIso` are the fast tier: the checked-label
  transcription of the pinned nauty search. The same names under
  `Checked` are the certified tier, validated through the proven
  certificate checker.
- Every operation and every theorem is available uncoloured, on a bare
  `Graph n`: `Graph.Isomorphic`, `Graph.canon`, `Graph.findIso`,
  `Graph.Checked.isIso` and the rest. `Graph.singleColor` is the
  one-cell view they read, and `Graph.isomorphic_singleColor_iff` the
  equivalence they are transported along.
- `findIso?`, `checkIso?`, and `canon?` are the resource-bounded certified
  operations. `SearchLimits` bounds the search (`maxNodes`, `maxCertNodes`)
  and `ReplayLimits` bounds kernel replay (`maxCheckerSteps`). Exhaustion
  returns `none` and is never evidence of non-isomorphism.
- `CanonCert` and `checkCanon` certify a canonical form; `DiffCert` and
  `checkDiff` certify non-isomorphism. Both are replayed by the kernel.
- `graph_iso` closes closed goals of the form `Isomorphic G H` and
  `¬ Isomorphic G H`, coloured or uncoloured, accepting
  `(maxNodes := ...)`, `(maxCertNodes := ...)`, and
  `(maxCheckerSteps := ...)` overrides.
- `Hex.GraphIso.Reference` is an independent exhaustive canonical form kept
  as a cross-check of the production pipeline.

# Verification

The certified tier carries the full theorem surface: canonical forms are
isomorphism-invariant and isomorphism is exactly equality of canonical
forms. The search itself is an untrusted producer; only the certificate
checker and its proofs establish the result, so no theorem depends on the
transcription being faithful to nauty.

```lean
theorem Checked.iso_iff_canon_eq (G : Colored n k) (H : Colored n k) :
    Isomorphic G H ↔ Checked.canon G = Checked.canon H

theorem Checked.findIso_isSome_iff (G H : Colored n k) :
    (Checked.findIso G H).isSome = true ↔ Isomorphic G H

theorem checkCanon_sound {limits : ReplayLimits} {G : Colored n k}
    {cert : CanonCert n k} {result : CanonResult n k}
    (h : checkCanon limits G cert = some result) :
    result.form = Checked.canon G ∧ G.relabel result.label = result.form
```

The fast tier deliberately proves less: `relabel_label`, `findIso_sound`, and
`isomorphic_of_isIso` are structural, while completeness of a `false` answer
and invariance of the fast form under isomorphism are pinned by conformance
rather than proved. Agreement of the two tiers is a theorem under the
hypothesis that the certificate replay accepts
(`canonicalize_eq_checked`).

Compatibility with nauty is a conformance property, not a theorem: an oracle
pins canonical labels, canonical bits, and visited-node counts against the
real nauty 2.9.3 on committed fixtures. That suite, and the benchmarks that
time this library against nauty, run in
[`hex-dev`](https://github.com/kim-em/hex-dev); they need a vendored nauty
build, which is why they are not part of this repository. See the
[SPEC](SPEC/hex-graph-iso.md) for the exact trust, budget, and compatibility
contracts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
