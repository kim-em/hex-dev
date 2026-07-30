# HexMvPoly release frontier

## Accomplished

- Refined the release plan around publishing both `HexMvPoly` and
  `HexMvPolyMathlib`.
- Confirmed that the current combined SPEC has not yet been moved into the
  per-library release layout.
- Found that the native benchmark imports
  `bench/HexMvPolyBench/Corpus.lean`, which is outside the conventional
  `bench/HexMvPoly/` managed path and must be reorganized or explicitly
  published.
- Confirmed that the Mathlib bridge conformance driver is self-contained,
  while the kernel proof-probe corpus can remain monorepo-only.

## Current frontier

The Lean implementations and consumer evidence are complete. The remaining
work is a focused release-preparation change: per-library SPECs, benchmark
layout, release-backed kernel tests, two manifest entries and aggregate pins,
followed by destination-repository bootstrap and the first sync.

## Next step

Prepare the monorepo release PR, choosing a single managed benchmark layout,
then bootstrap the two repository skeletons and execute the documented dry
run / real sync / fresh-clone validation sequence.

## Blockers

The destination repositories must exist and be writable by the release-sync
token. They are not currently resolvable from this session's GitHub identity.
