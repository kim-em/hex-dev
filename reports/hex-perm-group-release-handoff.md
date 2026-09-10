# HexPermGroup Release Handoff

This change prepares release integration and stops before publication.

The manifest order is `hex-perm-group`, `hex-perm-group-mathlib`,
`hex-graph-iso`, then `hex-graph-iso-mathlib`. The computational package pins
`hex-basic`; the companion pins `hex-basic` and `hex-perm-group`. Both graph
packages now declare the permutation packages in their published dependency
closures, and the aggregate pins and umbrella import the pair before graph
isomorphism. `HexPermGroupMathlib.Tests` is a released regression target.

The two managed CI entries each contain one Ubuntu job. The computational job
asserts that the package stays Mathlib-free; the companion fetches the Mathlib
cache and builds its public library and regression target. Development-only
fixtures, GAP oracle, benchmarks, measurements, profiles, and figures remain in
`hex-dev` and are absent from the generated mirrors.

The network-free manifest check passes with 57 source repositories plus the
aggregate:

```text
release manifest: 57 split repositories + 1 aggregate; paths, CI, pins,
import closure, test targets, and topological constraints valid
```

Local generated layouts were produced with `sync_released.apply_paths` from
the two manifest entries, then checked with `validate_skeleton` and
`validate_external_imports`. The resulting library-only trees built as follows
on Lean 4.34.0-rc2:

```text
lake build HexPermGroup
Build completed successfully (132 jobs).

lake build HexPermGroupMathlib HexPermGroupMathlibTests
Build completed successfully (2659 jobs).
```

The local skeleton used the released `hex-basic` checkout and the monorepo's
pinned Mathlib checkout, so these builds validate the copied source boundary
and dependency graph without creating or modifying a remote repository.

The current release-baseline parser compatibility issue described in #10126 is
resolved in this checkout: `python3 scripts/release/check_released_manifest.py`
reads the current baseline and completes successfully. No baseline branch was
advanced.

A read-only sync dry run cannot yet progress past remote preflight because
`leanprover/hex-perm-group` and `leanprover/hex-perm-group-mathlib` do not exist.
The observed failure is `Repository not found` while checking the shared
version tag. Before a later release, an organization owner must create both
repositories with their unmanaged Lake skeletons, add them to one publishing
token with Contents and Workflows write access, and approve that token scope.
Those external setup actions were deliberately not performed here.

After setup, run the sync with `--dry-run` and inspect every copied path,
deletion, pin rewrite, and managed workflow. The dependency-first order ensures
the permutation tag exists before the companion and graph packages resolve it.
The uncoordinated-commit guard must remain enabled: if any mirror `main` differs
from the recorded `release-sync-baseline`, re-seed the monorepo and rebuild the
graph before proceeding. Do not use `--force` to bypass an unexplained
divergence. A real sync, tags, releases, remote baseline advance, and all other
publication steps require a separate instruction.
