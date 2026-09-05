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

#eval Graph.isIso p3 p3'

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
- `canonicalize`, `canon`, `label`, `findIso`, and `isIso` are the
  public surface: the checked-label transcription of the pinned nauty
  search, carrying the full theorem surface.
- Every operation and every theorem is available uncoloured, on a bare
  `Graph n`: `Graph.Isomorphic`, `Graph.canon`, `Graph.findIso`,
  `Graph.isIso` and the rest. `Graph.singleColor` is the one-cell view
  they read, and `Graph.isomorphic_singleColor_iff` the equivalence
  they are transported along.
- `autos` reports the automorphism generators the pinned traversal
  discovers, in discovery order, with the vertex orbits, the orbit
  count and the group order; `Graph.autos` is the uncoloured mirror.
  Every returned generator is proved to be an automorphism
  (`autos_isIso`) and vertices sharing an orbit representative are
  proved to lie in one orbit (`autos_sameOrbit`). That the generators
  generate the whole group is not yet proved, so the orbit count and
  the group order are conformance-pinned rather than theorems.
- `Aut.gens`, `Aut.orbits`, `Aut.numOrbits` and `Aut.order` are the four
  fields on their own, for a caller who wants one of them and not the
  traversals the others cost.
- `checkIso?` is the replay-bounded permutation check. `ReplayLimits`
  bounds kernel replay by `maxKernelSteps`, and exhaustion returns
  `none`, never evidence of non-isomorphism.
- `Nauty.certifyKey?` produces a canonical-key certificate and
  `Nauty.checkCanon` replays it against the graph. `Nauty.checkDiff`
  reports that two replayed keys differ, which is what refutes
  isomorphism.
- `graph_iso` closes closed goals of the form `Isomorphic G H` and
  `¬ Isomorphic G H`, coloured or uncoloured. A positive goal closes by
  the relabel shortcut when one graph is syntactically a relabelling of
  the other, and otherwise by a literal transporter the kernel checks
  through `Kernel.checkIso`. A negative goal closes by the root
  refinement codes when they already differ (`Kernel.rootCode`), and
  otherwise by replaying one canonical-key certificate per graph
  (`Kernel.checkKey`). `set_option trace.graph_iso true` names the route
  a call took. The limits `(maxSearchNodes := ...)`,
  `(maxCertRecords := ...)` and `(maxKernelSteps := ...)` may be given
  in any order and default to `100000`, `100000` and `5000000`.

# Verification

The public surface carries the full theorem surface: canonical forms are
isomorphism-invariant and isomorphism is exactly equality of canonical
forms. The anchor is the declarative canonical form `Nauty.specCanon`,
the maximum leaf key of the unpruned individualization-refinement tree,
and `canon_eq_specCanon` identifies the public form with it. The pruned
search is proved to compute that key
(`Nauty.canonSpecKey_eq_tracedKey`), so the certificate checker accepts
the search's own answer on every input (`Nauty.certifyCanon?_isSome`)
and no certificate is produced or replayed on the answer path. No
theorem depends on the search being faithful to nauty.

```lean
theorem iso_iff_canon_eq (G : Colored n k) (H : Colored n k) :
    Isomorphic G H ↔ canon G = canon H

theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true ↔ Isomorphic G H

theorem Nauty.checkCanon_sound {G : Colored n k} {cert : Nauty.CertNode}
    {B : Nauty.Key n} {lab : Array Nat} {res : CanonResult n k}
    (h : Nauty.checkCanon G cert B lab = some res) :
    Nauty.canonSpecKey G = B ∧ res.form = G.relabel res.label ∧
      Isomorphic G res.form ∧
      B.rows = Nauty.leafRows { g := Nauty.rowsOf G } lab
```

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
