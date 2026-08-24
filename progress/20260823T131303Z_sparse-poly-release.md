# hex-sparse-poly + companion: release-tail preparation

## Accomplished

- `scripts/release/released.yml`: the `leanprover/hex-sparse-poly`
  entry (component label, kernel-probe test_modules, bench,
  conformance with fixtures and the SymPy oracle pair, pins
  [hex-basic, hex-poly, hex-arith, hex-mod-arith]) placed after
  hex-mod-arith, and the `leanprover/hex-sparse-poly-mathlib` entry
  ahead of the other *-mathlib repos; both added to the aggregate
  `leanprover/hex` pin list.
- New manifest field `conformance_pins` in
  `check_released_manifest.py`: a repo's conformance project may pin
  libraries its published library does not (here hex-arith and
  hex-mod-arith for the ZMod64 zero-divisor and characteristic cases,
  exactly as the library SPEC records); the checker now accepts the
  declared additions and rejects redundant declarations.
- `HexSparsePoly.KernelTests` moved into the `HexReleaseTests` globs
  to match the manifest's test_modules; `HexSparsePolyTests` remains
  as the monorepo-only lint target.
- `HexAggregateCheck.lean` mirrors the new aggregate pins; the manual
  chapter moved from the draft section to the released side of
  `HexManual.lean` (include level 2 to 0), and
  `check_manual_split.py`, `check_released_manifest.py`,
  `check_trust_surface.py`, the sync unit tests, `check_dag.py`, and
  the factor-sweep freshness check all pass; full build green.

## Current frontier

The PR is prepared as a draft: it must merge only after the ops step
that creates `leanprover/hex-sparse-poly` and
`leanprover/hex-sparse-poly-mathlib` (Lake skeletons) and widens a
`hex-publishing*` fine-grained token to include them, which needs
org-owner approval. `sync_released.py` preflights and refuses
otherwise, so an early merge cannot silently publish, but the ordering
in PLAN/Releases.md puts the ops step first.

## Next step

After the ops step: mark the PR ready, merge the stack bottom-up, then
`workflow_dispatch` of sync-released.yml as dry-run, inspect, and run
with dry_run=false.

## Blockers

Repo creation and token widening are Kim's (org-owner approval).
