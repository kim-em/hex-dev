# Independent rebase review

I found no defects introduced by the rebase. The four libraries' source, the target wiring and upstream's CI, cache and consumer changes all came through intact. I have one low-severity follow-up on stale evidence pointers. Everything here comes from reading source and diffs. I couldn't build anything or run Python, and `git range-diff` and process-substitution diffs were denied, so I compared the patches file by file instead.

## What I checked in the source

**The branch patch is unchanged.**
- `git diff --stat` of the old tip against its base and of HEAD against `293d981ea` match: the same 367 files, +79111/−146.
- `git diff 04c922403 HEAD`, limited to the branch's own paths, shows only upstream-owned files. That covers the four libraries, the conformance, bench and adapter directories, the reports, the sweep and oracle scripts, the status files and the bench results. So the ceiling, square-root and Sturm source is byte-identical to the reviewed tip.
- Upstream didn't touch any file of the four libraries, and `lean-toolchain` and `lake-manifest.json` didn't change. The Mathlib lemmas used in `Rounding.lean` and `Rational.lean` therefore still exist.

**The automatically merged files are correct.**
- Our hunks in `lakefile.lean`, `libraries.yml`, `scripts/check_dag.py` and `scripts/libgraph.py` are the same as before the rebase.
- The removal of `HexSturmTheory.Conformance` and `.submodules HexSturmTheory.Replay` now sits inside upstream's new parked-library filter on `HexConformance`, and it composes correctly.
- Our two `HexQuerySemantics` globs merged alongside upstream's additions without clashing.

**`ci.yml` keeps everything from upstream.** That includes:
- the removed tactic-probe and sweep unit tests, the new sign-determination allocation test, and the dropped rank plot;
- the cache key with run ID and attempt, the extra restore key, the early main-only save step (conditioned on `!cancelled()`), and the removal of the late save step;
- `hexarith_extgcd_tests` and `hexsigndet_field_checks`;
- HexInterval's removal from the bench list and its interval canaries;
- the new upstream library targets (including `RealClosureConsumer`) and `hexrealclosure_codec_bytes`.

On top of that, ours adds:
- the `test_check_sturm_fixtures.py` unit test;
- `HexSturmTheoryTests` and `HexRealAlgebraicTheoryTests`;
- `hexrealalgebraic_bench`;
- the `HexRealAlgebraic=hexrealalgebraic_bench` pair.

The interval executables still in `HEX_EXE_TARGETS` are exactly what main has.

**The bench-budget test is consistent.** Counting `ci.yml:499-528` by hand gives 57 pairs. The test's new split marker is the HexSignDet `if [ -z "$HEX_LIBRARY_FILTER" ]` at `ci.yml:529`, immediately after the list.

**No compatibility problems for the four libraries.**
- `ceil_eq` moved into the theory companion, and `FloorRing` now supplies `ceil` directly. Nothing in the tree uses either, including upstream's new `RealClosureConsumer` and HexRCF.
- `sqrt?` is now defined as `sqrtRoot?`, which keeps the `a < 0` check. So the `#guard`s in the HexManual chapter (`sqrt? (-1) == none`) still hold.
- `examples/RealClosureConsumer/Query.lean` calls `query_count`, `check_sound` and `countPrepared_sound` positionally. This branch only adds `query_spec` to `Soundness.lean` and doesn't change those signatures.
- The sweep scripts still find every name they import from `fresh_module_sweep`. Upstream only swapped that file's internal `acquire_cpu` import.

## Findings

**1. The Phase-3 evidence points at commits that no longer exist on the branch (Low).**
- **Where:** `reports/bench-results/prerequisite-phase3-verification.json` (`ci.source_commit` is `54fd06b…`, `local.source_commit` is `8545f2012`, plus `benchmark_verification`) and `reports/hex-real-algebraic-performance.md:20-22,31-32`.
- **Why:**
  - After the rebase, `git branch -a --contains 54fd06b` returns nothing, so these provenance links will rot.
  - The figure of 336 s with 24 s of headroom was measured on the old base. That base still had `HexInterval=hexinterval_decision_bench` and the three interval canaries in the bench step, which upstream has since removed, and upstream's other bench changes are also new. The headroom on this base is unknown in both directions.
- **Fix:** when required CI finishes on `63bc71637`, take its bench wall-clock breakdown. Either update the JSON and report (the rebased counterpart of `54fd06b` is `05879c013`), or record the new run and headroom in the PR description. The earlier attestation finding about bench-cap headroom is still the open item; the rebase neither caused it nor fixed it.

**2. Named-admission scan not reported as run (Info).**
- **Where:** `ci.yml:126` runs `scripts/ci/check_named_admissions.py`.
- **Why:** upstream added `RealClosureConsumer.Query` as a scan root, and its imports pull in `adapters/HexSturmTheory/Soundness.lean`, which this branch extends. `HexSturmTheory/Rational.lean` also gains a `ChainCorrespond` import, and the scan already reaches that file through `adapters/HexRealClosureTheory/Canonical.lean`.
- **Fix:** none expected. A grep of our Lean files finds `axiom`/`stop`/`sorry`-like words only in comments, which the scanner ignores. The check takes about a second, so it's worth running locally next to `check_dag.py`, since your list of local checks didn't mention it.

## Still to run (not done by me)

- The full `lake build`, including the default targets `HexManual`, `HexSturmTheoryTests`, `HexRealAlgebraicTheoryTests` and `RealClosureConsumer`.
- Required CI on the rebased head, and the bench-verify total on the new base, which is what decides finding 1.
- The Python unit tests and `check_named_admissions.py`.
- Reading the PR body.

Phase 3 only is what's recorded (`done_through: 3` for all four libraries), and the reports and evidence JSON still say Phase 4 is incomplete.


## Response and verification

The historical captures retain their original source commits. A separate rebase-verification record preserves the newer 217/360-second result and the failed rebased CI run; no historical timing is asserted as current-base headroom. The full default Lake build passes with 15,525 jobs, the owned build with 10,851 jobs, and all 19 pinned oracle regression tests pass without skips. The named-admission scan exposed main’s stale import of a removed sign-determination conformance module. The conformance-only correction subsequently merged through PR #10641 and is inherited from main; no sign-determination or tower implementation or conformance hunk remains in this PR. Full conformance passes with 14,772 jobs. Required CI must pass on the corrected revision before merge.

The named-admission scan passes after that correction. The completed fresh emitter matches the committed fixture byte for byte, and all 83 fresh exact-oracle cases pass with zero skipped components.
