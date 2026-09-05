<!--
Template for the README of the leanprover/hex aggregate.

This file is the source of truth: `scripts/release/sync_released.py` renders
it and publishes the result as the aggregate's README.md, replacing the
region between the LIBRARIES markers with a table generated from
`released.yml`. Never hand-edit README.md in the released repo; edit this
template (for the prose) or `released.yml` (for the table) instead.

`scripts/release/check_released_manifest.py` requires every aggregated
computational library to carry a `component:` label, so a newly released
library cannot be missing from the table.
-->
# hex

Verified computational algebra in Lean 4: an aggregator for the released
`hex` libraries.

- Manual: <https://kim-em.github.io/hex-dev/>
- API documentation: <https://leanprover.github.io/hex/docs>

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex"
git = "https://github.com/leanprover/hex.git"
rev = "main"
```

Then `import Hex` re-exports every library in the table below at a single
coherent pinned set:

```lean
import Hex

open Hex

-- Exact, fraction-free integer determinant.
def M : Matrix Int 3 3 := #m[2, 1, 1; 1, 2, 1; 1, 1, 2]
#eval M.det   -- 4

-- LLL: reduce an integer lattice basis and read off a provably short vector.
-- The `by decide` arguments discharge the reduction-factor side conditions.
def L : Matrix Int 3 3 := #m[1, 1, 1; 1, 0, 2; 3, 5, 6]
#eval lllNative.firstShortVector L (3 / 4) (by decide +kernel) (by decide +kernel) (by decide)
```

To depend on just one piece, require that library directly (for example
[`hex-lll`](https://github.com/leanprover/hex-lll) for the Mathlib-free LLL
core) instead of the aggregator.

# Libraries

Each computational library is Mathlib-free; its Mathlib correspondence proofs
and Mathlib-facing API, where they exist, live in a separate `*-mathlib`
library. A library whose subject is a Mathlib-facing tactic, such as
`hex-rcf`, has no computational half and appears only in the Mathlib column.

<!-- LIBRARIES:BEGIN (generated from released.yml; do not edit by hand) -->
<!-- LIBRARIES:END -->

# Announcements

<!-- ANNOUNCEMENTS:BEGIN (generated from released.yml; do not edit by hand) -->
<!-- ANNOUNCEMENTS:END -->

Development of the full project (including unreleased libraries) happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo.
