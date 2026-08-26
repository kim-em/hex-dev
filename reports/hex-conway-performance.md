# HexConway Performance Report

## Bench Targets

- `Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum`: `tier1LookupComplexity ordinal`
  (parameter domain widened from `1..36` to `1..38` when the binary column was
  extended to degree 8; the verdict below predates that and needs a re-run on
  `carica` before it can be cited for the current table)
- `Hex.ConwayBench.runConwayPolySupported_2_1Checksum`: fixed canonical `SupportedEntry` recovery for `C(2, 1)`
- `Hex.ConwayBench.runTier1Irreducibility_2_1Checksum`: fixed Rabin irreducibility check for imported `C(2, 1)`
- `Hex.ConwayBench.runTier1Irreducibility_2_6Checksum`: fixed Rabin irreducibility check for imported `C(2, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_3_6Checksum`: fixed Rabin irreducibility check for imported `C(3, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_5_6Checksum`: fixed Rabin irreducibility check for imported `C(5, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_7_6Checksum`: fixed Rabin irreducibility check for imported `C(7, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_11_6Checksum`: fixed Rabin irreducibility check for imported `C(11, 6)`
- `Hex.ConwayBench.runTier1Irreducibility_13_6Checksum`: fixed Rabin irreducibility check for imported `C(13, 6)`
- `Hex.ConwayBench.runTier2Compat_2_3_6Checksum`: fixed Tier 2 compatibility check for `C(2, 3)` inside `C(2, 6)`
- `Hex.ConwayBench.runTier2Compat_2_4_8Checksum`: fixed Tier 2 compatibility check for `C(2, 4)` inside `C(2, 8)`
- `Hex.ConwayBench.runTier2Compat_13_1_6Checksum`: fixed Tier 2 compatibility check for `C(13, 1)` inside `C(13, 6)`

`HexConway` now advertises two implemented tiers: the Tier 1 committed-table
surface, and Tier 2 divisor compatibility. Both appear in
`HexConway.phase4.input_families` as `tier1-committed-table` and
`tier2-divisor-compatibility`. Tier 3 on-demand Conway search remains
unimplemented and has no bench targets; Tier 2 primitivity is likewise
unimplemented and is not covered by the `tier2-divisor-compatibility` family,
which measures only the compatibility check.

## Tier 2 divisor compatibility

Measured on `chungus2` (Linux, x86_64, lean 4.33.0-rc1), five repeats each,
medians:

| Target | Pair | Frobenius factors | Median |
|---|---|---:|---:|
| `runTier2Compat_2_3_6Checksum` | `C(2, 3)` in `C(2, 6)` | 2 | 26.086 µs |
| `runTier2Compat_2_4_8Checksum` | `C(2, 4)` in `C(2, 8)` | 2 | 48.880 µs |
| `runTier2Compat_13_1_6Checksum` | `C(13, 1)` in `C(13, 6)` | 6 | 77.773 µs |

For scale, the Tier 1 Rabin check on the same largest entry
(`runTier1Irreducibility_13_6Checksum`) is 131.070 µs, and on `C(2, 6)` it is
19.349 µs. So a compatibility check costs less than the irreducibility check
for the same entry, which is the expected shape: compatibility runs `n / m`
Frobenius steps at one modular composition apiece plus a final evaluation,
while the Rabin test runs a pow chain over the maximal proper divisors of the
degree.

The three targets span the axes that matter. `2_3_6` and `2_4_8` share the
factor count and differ in degree, and the cost roughly doubles with degree.
`13_1_6` has the deepest chain in the committed table at six factors, over the
largest prime; it is the worst case and is still under 80 µs.

This is the runtime cost. The kernel-replay cost, which is what actually
bounds the committed table, is separate: the fifty-two `decide`-discharged
compatibility theorems together add about seventeen seconds to a
`lake build HexConway`, against minutes for the Tier 1 certificates.

## Tier 1 proof budget

`HexConway/SPEC/hex-conway.md` sizes the committed slice by proof-checking cost
rather than by mathematical coverage: include as much of the Lübeck table as
possible subject to the generated Tier 1 correctness theorems still checking in
"only a few minutes". That cost is elaboration time, not runtime, so it is not
one of the bench verdicts below; it is recorded here because it is the number
that decides how wide the table may be.

Method: delete `.lake/build/{lib/lean,ir}/HexConway`, then `lake build
HexConway` on an otherwise warm dependency tree, reading the per-module times
Lake reports. Single run per scope, so these are indicative rather than
distributions. AMD EPYC 9455, Linux x86_64, Lean 4.33.0-rc1. This is not
`carica`, so the figures are not comparable with the scientific runs below;
they are useful only as a ratio between scopes.

| Scope | Entries | `Table` | `Certificates` | `Api` |
|---|---|---|---|---|
| `2:6, 3:6, 5:6, 7:6, 11:6, 13:6` | 36 | 2.6s | 28s | 2.8s |
| `2:8, 3:6, 5:6, 7:6, 11:6, 13:6` | 38 | 2.7s | 31s | 3.0s |

Almost all of the cost is kernel `decide`: 37 certificate replays in
`HexConway/Certificates.lean` at 8M heartbeats each, four of them at 20M, plus
the degree-one check in `HexConway/Table.lean`. Adding `C(2, 7)` and `C(2, 8)`
cost about 3s between them, so the binary column is cheap: its residues are
single bits and its certificates are correspondingly small.

Cost grows with both the prime and the degree, which is why the committed scope
carries a maximum degree per prime rather than one bound for all of them,
matching the `SLICE` in `scripts/oracle/update_luebeck_conway_cache.py`. The
compiled Rabin checks in the verdicts below show the degree-6 spread across
primes directly: `128.417 us` at `C(2, 6)` against `812.958 us` at `C(13, 6)`,
a factor of about 6.3 that the kernel replay inherits.

**What this measurement does and does not settle.** It settles that the
committed scope is affordable: 31s against a "few minutes" rule leaves
substantial headroom. It does not settle that degree 8 is the right frontier.
The binary column was extended to 8 because `GF(2^8)` is the smallest field
where the packed representation is interesting and because the cost was known
to be small, not because degree 9 was measured and found too expensive. Calling
this the budget-selected maximum would overstate it; it is an initial widening
with the budget confirmed to accommodate it.

Establishing the actual frontier means measuring successive candidates until
the rule bites, per prime. That is now mechanical:
`rebuild_luebeckConwayPolynomial?` regenerates the coefficient table and
`#conway_entry_source` emits the per-entry literal, lemmas, and certificate for
a cached pair. The odd-prime columns are where the cost is, so that is where
the next measurement should start.

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
