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

The `tier1-committed-table` profile was regenerated at commit
`3bc24c50fbe57487776c433106894ee544a6d656` on `carica` (Apple M2 Ultra,
macOS 14.6.1, arm64) with `samply 0.13.1` at a 999 Hz sampling rate,
using the lean-bench-samply timed-region filter at commit
`602da96df3537341b50de9add2f137b0a75a68df`. The harness reported
`git_dirty=true` because this worktree carried an unrelated pre-existing
`.claude/CLAUDE.md` modification. The filtered raw profile is
developer-local at
`/tmp/hex-profile-runLuebeckConwayPolynomialLookupChecksum-36.json.gz`
and is not committed.

### `tier1-committed-table`

Command:

```sh
scripts/profile/run_profile.sh \
    ./.lake/build/bin/hexconway_bench \
    Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum \
    36 1000000000
```

Representative case: committed Luebeck table ordinal `36`, corresponding
to `C(13, 6)`, no seed. Child row: `inner_repeats=1048576`,
`per_call_nanos=876.204252`, `result_hash=0x837443a59caa5094`.

Diagnostics block:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='Thread <4419428>' tid=4419428
regions:            14, total timed = 925.9 ms
expected samples:   ~925 on bench thread
retained samples:   924 on bench thread (10 rejected outside windows)
other-thread noise: 1 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runLuebeckConwayPolynomialLookupChecksum-36.json.gz
```

The diagnostics JSON records the calibration anchors
`spawn_anchor_wall_ns=1780141890664575000`,
`spawn_anchor_mono_ns=329924577328833`,
`sidecar_mono_anchor_ns=329925512083500`, and
`samply_meta_start_time_ms=1780141890671.813`.

Across the 924 retained bench-thread samples, flat leaf cost is:

- Lean runtime / standard-library dispatch and compiler-outlined helper
  frames: `612/924` samples (`66.2%`);
- allocation / free, mostly `mi_malloc*`, `mi_free*`, and array allocation
  paths: `243/924` (`26.3%`);
- Hex own code: `69/924` (`7.5%`);
- GMP big-integer arithmetic: `0/924`.

The inclusive own-code ranking is
`Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum` (`535/924`,
57.9%) →
`Hex.Conway.luebeckConwayPolynomial?` (`530/924`, 57.4%) →
`Hex.ConwayBench.checksumLookup` (`360/924`, 39.0%) →
`Hex.DensePoly.trimTrailingZeros` (`92/924`, 10.0%). Lower entries include
`Hex.ConwayBench.checksumPoly` (`51/924`, 5.5%) and
`Hex.Conway.luebeckConwayPolynomialOfCoeffs` (`45/924`, 4.9%).

The dominant cost remains attributable to the registered
`Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum` target. The
profile is the expected tiny Tier 1 committed-table path: select the stored
coefficient row for `C(13, 6)`, rebuild the small `FpPoly`, trim the dense
polynomial representation, and checksum the result. No newly dominant cost
falls outside the registered bench target, so no Attribution-rule follow-up
is required.

## Concerns
