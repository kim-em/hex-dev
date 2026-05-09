# HexGfq Performance Report

## Bench Targets

- `Hex.GfqBench.runGenericModulusChecksum`: fixed benchmark for the selected generic Conway modulus helper.
- `Hex.GfqBench.runPackedModulusChecksum`: fixed benchmark for the selected packed Conway modulus helper.
- `Hex.GfqBench.runGF2qOfWordReprChecksum`: fixed benchmark for packed `GF2q.ofWord` plus `GF2q.repr` on the committed `GF2q 1` entry.
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

Profiles were recorded with `samply record --save-only
--unstable-presymbolicate` at the same commit on `carica` (Apple M2 Ultra,
macOS 14.6.1), at the default 1 kHz sampling rate. Commands invoked the built
benchmark executable directly to avoid profiling the Lake wrapper. The raw
Firefox Profiler JSON and `*.syms.json` artefacts are developer-local and are
not committed.

### `generic-constructor-projection`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gfq-generic-constructor-33b7f720dcce.json -- .lake/build/bin/hexgfq_bench run Hex.GfqBench.runGFqOfPolyReprChecksum
```

Representative case: deterministic binary polynomial representatives,
parameters `4..256`, no seed. The sampled run is dominated by harness/process
I/O and idle waits because this committed wrapper surface is very small; after
excluding blocking wait leaves, leaf cost was other system/read path 74.1%,
Lean runtime 13.9%, allocation/free 6.5%, own Hex/bench code 3.8%, and GMP
1.6%. Inclusive Hex cost was led by
`Hex.GfqBench.runGFqOfPolyReprChecksum` and its generated benchmark loop
(23.3%), then `GFqRing.reduceMod` (23.2%), `DensePoly.divModArray` (22.8%),
and `DensePoly.divModArrayAux` (20.4%). The dominant algorithmic work maps to
the registered generic constructor/projection target.

### `packed-constructor-projection`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gfq-packed-constructor-33b7f720dcce.json -- .lake/build/bin/hexgfq_bench run Hex.GfqBench.runGF2qOfWordReprChecksum
```

Representative case: fixed packed `GF2q 1` word representative, no seed. The
target is sub-microsecond and the profile is therefore mostly harness shape:
after excluding blocking wait leaves, leaf cost was other system/read path
81.0%, Lean runtime 12.9%, allocation/free 5.2%, GMP 0.5%, and own Hex/bench
code 0.3%. Inclusive Hex cost was led by initialization for `HexGfq.Basic` and
`HexGfq.Bench` (4.5% each) and `HexGF2`/`HexGF2.Clmul` initialization (3.3%
each), with the actual packed operation too small to dominate. This matches the
fixed benchmark warning that the committed packed Conway surface is genuinely
tiny.

### `packed-generic-shared-bridge`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gfq-shared-bridge-33b7f720dcce.json -- .lake/build/bin/hexgfq_bench run Hex.GfqBench.runPackedGenericSharedChecksum
```

Representative case: shared deterministic binary representative family,
parameters `4..256`, no seed. After excluding blocking wait leaves, leaf cost
was other system/read path 74.8%, Lean runtime 13.5%, allocation/free 5.2%,
own Hex/bench code 4.6%, and GMP 1.9%. Inclusive Hex cost was led by
`Hex.GfqBench.runPackedGenericSharedChecksum` and its generated benchmark loop
(22.3%), `GFqRing.reduceMod` (13.7%), `DensePoly.divModArray` (13.6%),
`DensePoly.divModArrayAux` (12.5%), `GF2n.reduce` (8.4%), and
`GF2Poly.packedReduceWord` (8.3%). The dominant generic and packed costs map
to the registered shared bridge target.

## Concerns
