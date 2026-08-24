# hex-sparse-poly + companion: Phase-7 documentation

## Accomplished

- `HexManual/Chapters/HexSparsePoly.lean`: the Verso reference chapter
  (representation, arithmetic with the measured multiplication
  selection, conversions with the recorded crossovers, evaluation and
  substitution, the Euclidean layer) with the required
  `# The Mathlib correspondence` section documenting the companion
  inside the parent chapter, wired into `HexManual.lean` under the
  draft sections; `lake build HexManual` green; `check_phase7.py`
  passes.
- `HexSparsePoly/README.md` and `HexSparsePolyMathlib/README.md` per
  `SPEC/readme.md`'s five-section shape, both quickstart snippets
  build-checked through `lake env lean`.
- `done_through: 7` for both libraries.

## Current frontier

Both libraries complete through Phase 7. All that remains of the plan
is the release tail, plus shepherding the open PR stack into main
(#9380 is retargeted to main with auto-merge armed; each successor gets
the same treatment as its base merges).

## Next step

Release tail per PLAN/Releases.md: Kim/ops creates
leanprover/hex-sparse-poly{,-mathlib} with Lake skeletons and widens a
hex-publishing token; then released.yml entries (pins incl. the
conformance-only hex-mod-arith), moving KernelTests into
HexReleaseTests + test_modules at split time, the manual-split flip of
the chapter, and the sync dry-run.

## Blockers

The release-tail repo creation and token widening need Kim (org-owner
approval); everything up to that point is PR-able from here.
