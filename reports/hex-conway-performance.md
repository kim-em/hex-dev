# HexConway Performance Report

## Bench Targets

- `Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum`: `tier1LookupComplexity ordinal`
- `Hex.ConwayBench.runConwayPolySupported_2_1Checksum`: fixed canonical `SupportedEntry` recovery for `C(2, 1)`
- `Hex.ConwayBench.runTier1Irreducibility_2_1Checksum`: fixed Rabin irreducibility check for imported `C(2, 1)`
- `Hex.ConwayBench.runTier1Irreducibility_2_6Checksum`: fixed Rabin irreducibility check for imported `C(2, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_3_6Checksum`: fixed Rabin irreducibility check for imported `C(3, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_5_6Checksum`: fixed Rabin irreducibility check for imported `C(5, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_7_6Checksum`: fixed Rabin irreducibility check for imported `C(7, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_11_6Checksum`: fixed Rabin irreducibility check for imported `C(11, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_13_6Checksum`: fixed Rabin irreducibility check for imported `C(13, 6)`

The current `HexConway` implementation advertises the Tier 1 committed-table
surface only. Tier 2 full Conway compatibility verification and Tier 3
on-demand Conway search are not implemented API surfaces in this phase slice,
so they are not included in `HexConway.phase4.input_families` and have no
Phase-4 bench targets yet.

## Verdicts

Scientific run at commit `e7bf7c23bbb5` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexconway_bench run \
    Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum \
    Hex.ConwayBench.runTier1Irreducibility_2_1Checksum \
    Hex.ConwayBench.runTier1Irreducibility_2_6Checksum \
    Hex.ConwayBench.runTier1Irreducibility_3_6Checksum \
    Hex.ConwayBench.runTier1Irreducibility_5_6Checksum \
    Hex.ConwayBench.runTier1Irreducibility_7_6Checksum \
    Hex.ConwayBench.runTier1Irreducibility_11_6Checksum \
    Hex.ConwayBench.runTier1Irreducibility_13_6Checksum \
    Hex.ConwayBench.runConwayPolySupported_2_1Checksum \
    --export-file reports/bench-results/hex-conway-e7bf7c23bbb5.json
```

The run used the committed deterministic Luebeck table slice for primes
`2, 3, 5, 7, 11, 13` and degrees `1..6`; no random seeds are involved.
The harness recorded `e7bf7c2-dirty` because this worktree carried an
unrelated pre-existing `.claude/CLAUDE.md` modification. Export artefact:
`reports/bench-results/hex-conway-e7bf7c23bbb5.json`, SHA-256
`2d7ca6c152577adb9418b4cfe82b62714520fac56aa4b9ba931b97e4d6b5bd15`.

- `Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum`: consistent
  with declared complexity (`cMin=311.335, cMax=826.105, β=+0.029`,
  parameters `1..36`, final hash `0x837443a59caa5094`).
- `Hex.ConwayBench.runTier1Irreducibility_2_1Checksum`: fixed median
  `8.042 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runTier1Irreducibility_2_6Checksum`: fixed median
  `128.417 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runTier1Irreducibility_3_6Checksum`: fixed median
  `248.750 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runTier1Irreducibility_5_6Checksum`: fixed median
  `447.292 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runTier1Irreducibility_7_6Checksum`: fixed median
  `616.667 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runTier1Irreducibility_11_6Checksum`: fixed median
  `738.875 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runTier1Irreducibility_13_6Checksum`: fixed median
  `812.958 us`, hash `0xb`, expected hash matched.
- `Hex.ConwayBench.runConwayPolySupported_2_1Checksum`: fixed median
  `459 ns`, hash `0x8d105cfbb68da744`, expected hash matched.

Smoke wiring was also checked at the same commit with:

```sh
python3 scripts/check_dag.py
lake exe hexconway_bench list
lake exe hexconway_bench verify
```

`verify` passed all nine registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-conway.md` does not name an external Phase-4
performance comparator for the Tier 1 committed-table surface, so there
are no `phase4.comparators` ratios to record. The Lübeck table is an input
source rather than an executable comparator, and the current API surface has
no alternative Tier 1 implementation to register as a `compare` group.

## Profile

The `tier1-committed-table` profile was recorded at commit
`e7bf7c23bbb5` on `carica` (Apple M2 Ultra, macOS 14.6.1) with a 1 kHz
sampling rate. `samply record --save-only --unstable-presymbolicate`
successfully ran the benchmark child but produced zero sampled frames on
this macOS host, so attribution below uses `/usr/bin/sample` against the
same long-running LeanBench child process. The raw text profile is
developer-local at
`/tmp/hex-profiles/hex-conway-lookup-sample-e7bf7c23bbb5.txt` and is not
committed.

### `tier1-committed-table`

Command:

```sh
.lake/build/bin/hexconway_bench _child \
    --bench Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum \
    --param 36 --target-nanos 10000000000 --cache-mode warm
```

Sample command:

```sh
sample $pid 3 -file \
    /tmp/hex-profiles/hex-conway-lookup-sample-e7bf7c23bbb5.txt
```

Representative case: committed Luebeck table ordinal `36`, corresponding
to `C(13, 6)`, no seed. Child row: `inner_repeats=8388608`,
`per_call_nanos=877.881785`, `result_hash=0x837443a59caa5094`.
The profiler sampled `2044` worker-thread stacks during the timed child.

Leaf cost is overwhelmingly Lean runtime dispatch, refcounting, and
allocation/free inside a tiny table materialisation path; no GMP frames were
present. The inclusive own-code ranking is
`Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum` (`1153/2044`
samples, 56.4%) →
`Hex.Conway.luebeckConwayPolynomial?` (`643/2044`, 31.5%) →
`Hex.Conway.luebeckConwayPolynomialOfCoeffs` and its coefficient-mapping
closure under `Array.mapMUnsafe.map` (visible below the lookup frame).
The remaining visible hot frames are Lean closure application
(`lean_apply_1`, `lean_apply_2`, `lean_apply_4`), refcount cold paths
(`lean_dec_ref_cold`), and the bundled allocator (`mi_malloc*`,
`mi_free*`). The dominant cost maps directly to the registered
`runLuebeckConwayPolynomialLookupChecksum` target and reflects rebuilding
the small `FpPoly` row from committed coefficient data on each lookup,
which is the expected Tier 1 table path.

## Concerns

