# Compiled repeated-factor stage costs

The [registered protocol](source/protocol.md) was committed at
`bd5e4f10826060517b465c3759bb4795d095baf2` before collecting any observations.
The unmodified lean-bench fixed runner collected all 24 measurements in six
trial-major rounds on automatically leased CPU 80. Every command exited zero;
every expected-hash check passed. Raw exports and logs are retained in
[capture/](capture/metadata.json); [analysis.json](analysis.json) retains every
per-call observation and its inner-repeat count. No rerun was collected.

| Inclusive operation | Median ms | Full range ms |
| --- | ---: | ---: |
| `runYun`: Zero extraction and Yun | 0.061351 | 0.060400–0.061667 |
| `runAssembly`: Yun and factor isolation/assembly | 0.199789 | 0.197195–0.201286 |
| `runRoots`: Complete roots, including comparisons and sorting | 8.894096 | 8.806132–9.066227 |
| `runNativeRoots`: Native complete roots, including selected child construction | 10.193454 | 10.117255–10.242732 |

The common input is `-3 X² (X² - 2)³ (X - 3)⁵`. Its ordered distinct
roots are `[-√2, 0, √2, 3]` with multiplicities `[3, 2, 3, 5]`.
The bodies retrieve inputs from runtime `IO.Ref`s. Setup is outside their
timer; each measured body checks the producer result and returns hash 1.
Each child auto-tunes its batch to at least 0.2 seconds. Per-call values are
`total_nanos / inner_repeats`; process startup is excluded by lean-bench.

The native boundary runs the generic pipeline over the tower-base coefficient
wrapper and signature type, rather than rational coefficients and a `Nat`
context. Its difference from `runRoots` mixes those costs with selected-child
construction; child construction is not isolated by this capture. The
[current protocol description](protocol.md) states these distinct boundaries.

These are inclusive fixed-input observations, rather than an asymptotic
claim. Do not subtract the stages to infer exclusive costs. In particular,
the complete-root boundary is much more expensive than assembly in this
family, but the observations do not separately attribute query production,
BKR solving, coefficient signs or comparison/reencoding. Those measurements,
serialization and ordinary-kernel replay, and the remaining Phase 4 families
are still required. Host activity is recorded as context and no completed
sample is excluded.

## Source and executable binding

- Compiled executable SHA-256: `88d50c5d65f58d882ebe51de4cacc745ac8d0c304323f8eb8890a1f1db166958`.
- [Build binding](build-binding.json) verifies the retained binary/source hashes
  and lists every change between the build and protocol source. This check
  occurred after capture; the build log contains no contemporaneous git/hash command.
- [Build log](build.log): `lake build hexrealclosure_bench`, 1674 jobs PASS.
- [Registration source](source/Bench.lean.txt), [Lean toolchain](source/lean-toolchain)
  and [Lake manifest](source/lake-manifest.json) retain the compiler/library pins.
- The executable was compiled at `eb48afe43af9b801c9dc3115ce3f22b2df771998`.
  Between that source and the protocol commit only the central report, protocol
  and Python orchestration/analysis files changed; every compiled Lean input
  remained unchanged. The runner records the executable hash before collection.
- Reproduce collection with `python3 scripts/bench/collect_real_closure_stages.py DEST`
  from the committed protocol source, choosing a new destination outside the
  worktree. Validate with `python3 scripts/bench/analyze_real_closure_stages.py DEST`.
  Reproduction is a new retained experiment, not a replacement for this capture.
