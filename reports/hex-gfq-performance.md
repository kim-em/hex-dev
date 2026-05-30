# HexGfq Performance Report

## Bench Targets

- `Hex.GfqBench.runGenericModulusChecksum`: fixed benchmark for the selected generic Conway modulus helper.
- `Hex.GfqBench.runPackedModulusChecksum`: fixed benchmark for the selected packed Conway modulus helper.
- `Hex.GfqBench.runGF2qOfWordReprChecksum`: fixed benchmark for packed `GF2q.ofWord` plus `GF2q.repr` on the committed `GF2q 1` entry.
- `Hex.GfqBench.runGF2qOfWordReprProfileChecksum`: parametric profiling companion for packed `GF2q.ofWord` plus `GF2q.repr` on the committed `GF2q 1` entry.
- `Hex.GfqBench.runGFqOfPolyReprChecksum`: `n`, generic `GFq.ofPoly` plus `GFq.repr` on deterministic degree-`n` binary representatives for the committed `GFq 2 1` entry.
- `Hex.GfqBench.runPackedGenericSharedChecksum`: `n`, shared packed/generic constructor-projection checksum on the same deterministic binary representative family.

## Verdicts

Scientific run at commit `33b7f720dcce514b455e26d27c402b415c192cd8` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexgfq_bench run Hex.GfqBench.runPackedGenericSharedChecksum Hex.GfqBench.runGFqOfPolyReprChecksum Hex.GfqBench.runGF2qOfWordReprChecksum Hex.GfqBench.runGenericModulusChecksum Hex.GfqBench.runPackedModulusChecksum --export-file reports/bench-results/hex-gfq-33b7f720dcce.json
```

The run used deterministic benchmark inputs from `HexGfq/Bench.lean`; random
seeds are not involved. The harness recorded `33b7f72-dirty` because this
worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-gfq-33b7f720dcce.json`.

- `Hex.GfqBench.runPackedGenericSharedChecksum`: consistent with declared
  complexity (`β=-0.098`, parameters `4..256`, final hash
  `0x1ce80893b9144788`).
- `Hex.GfqBench.runGFqOfPolyReprChecksum`: consistent with declared
  complexity (`β=-0.008`, parameters `4..256`, final hash
  `0x0`).
- `Hex.GfqBench.runGF2qOfWordReprChecksum`: fixed run, median `125 ns`, min
  `41 ns`, max `167 ns`, observed hash `0x1`, expected hash matched.
- `Hex.GfqBench.runGenericModulusChecksum`: fixed run, median `125 ns`, min
  `125 ns`, max `417 ns`, observed hash `0x3403d2eb08b5d5fc`,
  expected hash matched.
- `Hex.GfqBench.runPackedModulusChecksum`: fixed run, median `208 ns`, min
  `125 ns`, max `292 ns`, observed hash `0x1ce80893b914478a`,
  expected hash matched.

Smoke wiring was also checked with:

```sh
lake exe hexgfq_bench list
lake exe hexgfq_bench verify
```

`verify` passed all five registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-gfq.md` does not name an external Phase-4 performance
comparator for `HexGfq`. The meaningful internal common-domain comparison is
covered by `Hex.GfqBench.runPackedGenericSharedChecksum`, which exercises the
packed and generic p = 2 constructor/projection surfaces in one registered
target and hashes their combined result. There are no external comparator
ratios to record.

## Profile

Profiles were recorded with `scripts/profile/run_profile.sh`, which wraps
`samply record --save-only --no-open --rate 999 --unstable-presymbolicate` and
filters the Firefox Profiler JSON to the bench thread's `warm-loop` timed
regions. The runs used commit `3bc24c50fbe57487776c433106894ee544a6d656` on
`carica` (Apple M2 Ultra, arm64, macOS 14.6.1), Lean
`leanprover/lean4:4.30.0-rc2`, lean-bench
`91412dba8350c29ddf52c9ace56f8a3d2240b6c7`, samply `0.13.1`, and deterministic
benchmark inputs from `HexGfq/Bench.lean`; random seeds are not involved. The
harness recorded `git_dirty: true` because the profile-compatible packed target
and the report were being edited in this worktree. The raw filtered
`*.json.gz` artefacts are developer-local under `/tmp` and are not committed.

### `generic-constructor-projection`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench Hex.GfqBench.runGFqOfPolyReprChecksum 256 5000000000
```

Representative case: deterministic binary polynomial representative, parameter
`n=256`, no seed. Leaf cost in the filtered profile was Lean runtime/Std 51.0%,
Hex Lean code 38.7%, other compiler/system leaves 4.0%, allocation/free 3.6%,
and GMP 2.7%. Inclusive Hex cost was led by
`Hex.GfqBench.runGFqOfPolyReprChecksum` (99.9%), `GFqRing.reduceMod` (98.9%),
`DensePoly.divModArray` (86.0%), `DensePoly.divModArrayAux` (39.3%), and
`DensePoly.arrayDegreeAux` (27.2%). The dominant work is the generic
constructor's reduction modulo the committed Conway polynomial and maps to the
registered generic constructor/projection target.

Diagnostics:

```text
bench thread:       name='Thread <4847760>' tid=4847760
regions:            9, total timed = 2907.6 ms
expected samples:   ~2905 on bench thread
retained samples:   2904 on bench thread (9 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runGFqOfPolyReprChecksum-256.json.gz
```

### `packed-constructor-projection`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench Hex.GfqBench.runGF2qOfWordReprProfileChecksum 63 5000000000
```

Representative case: deterministic single-word packed representative,
parameter `n=63`, no seed. This uses the parametric
`runGF2qOfWordReprProfileChecksum` companion because lean-bench's fixed-child
path does not emit timed-region sidecars; the measured operation is the same
`GF2q.ofWord` plus `GF2q.repr` surface as the fixed
`runGF2qOfWordReprChecksum` verdict target. Leaf cost was Lean runtime/Std
39.5%, Hex Lean code 34.7%, allocation/free 15.0%, other compiler/system leaves
10.8%, and GMP 0.1%. Inclusive Hex cost was led by `GF2n.reduce` (98.9%),
`GF2Poly.packedReduceWord` (97.8%), `GF2Poly.mod` (97.6%), `GF2Poly.add`
(27.6%), `GF2Poly.degree?` (22.1%), and `GF2Poly.divModAux` entries up to
20.3%. The dominant packed reduction work is attributable to the registered
packed constructor/projection family; no new audit-found issue is needed.

Diagnostics:

```text
bench thread:       name='Thread <4847067>' tid=4847067
regions:            12, total timed = 4264.9 ms
expected samples:   ~4261 on bench thread
retained samples:   4260 on bench thread (9 rejected outside windows)
other-thread noise: 0 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runGF2qOfWordReprProfileChecksum-63.json.gz
```

### `packed-generic-shared-bridge`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfq_bench Hex.GfqBench.runPackedGenericSharedChecksum 256 5000000000
```

Representative case: shared deterministic binary representative, parameter
`n=256`, no seed. Leaf cost was Lean runtime/Std 46.7%, Hex Lean code 40.4%,
GMP 5.8%, allocation/free 3.6%, and other compiler/system leaves 3.6%.
Inclusive Hex cost was led by `Hex.GfqBench.runPackedGenericSharedChecksum`
(92.6%), `GFqRing.reduceMod` (92.2%), `DensePoly.divModArray` (87.9%),
`DensePoly.divModArrayAux` (35.7%), `DensePoly.arrayDegreeAux` (24.1%), and the
packed side through `GF2n.reduce` / `GF2Poly.packedReduceWord` at 6.8% / 6.7%.
The profile shape matches the benchmark declaration: the generic degree-`n`
representative scan dominates, while the fixed packed projection remains a
small component of the shared bridge.

Diagnostics:

```text
bench thread:       name='Thread <4848957>' tid=4848957
regions:            8, total timed = 3876.2 ms
expected samples:   ~3872 on bench thread
retained samples:   3872 on bench thread (9 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runPackedGenericSharedChecksum-256.json.gz
```

## Concerns
