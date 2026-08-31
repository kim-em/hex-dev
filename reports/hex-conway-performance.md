# HexConway Performance Report

## Bench Targets

- `Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum`: mode 1,
  two-sided constant-time lookup by table ordinal, over all 38 committed keys.
- `Hex.ConwayBench.runTier1Irreducibility_13_6Checksum`: mode 3, fixed Rabin
  verification of `C(13, 6)` under a 2 ms operation-scoped ceiling.
- `Hex.ConwayBench.runTier2Compat_13_1_6Checksum`: mode 3, fixed compatibility
  verification of `C(13, 1)` inside `C(13, 6)` under a 1 ms
  operation-scoped ceiling.
- `runConwayPolySupported_2_1Checksum`, the other six fixed Tier 1 checks, and
  the other two fixed Tier 2 checks are expected-hash anchors. They make no
  complexity claim and do not discharge performance coverage.

`HexConway` now advertises two implemented tiers: the Tier 1 committed-table
surface, and Tier 2 divisor compatibility. Both appear in
`HexConway.phase4.input_families` as `tier1-committed-table` and
`tier2-divisor-compatibility`. Tier 3 on-demand Conway search remains
unimplemented and has no bench targets. Tier 2 primitivity is implemented, but
the declared `tier2-divisor-compatibility` family measures only the
compatibility check.

## Tier 2 divisor compatibility

The earlier cross-case run on `chungus2` (Linux, x86_64, Lean 4.33.0-rc1),
five repeats each, established which committed pair is the canonical hard
case:

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
largest prime; it is the worst case. The current scientific run below measures
it at 76.065 µs under its enforced 1 ms ceiling.

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

### Ordered mode selection

The committed-table lookup remains mode 1. Its parameter is only an ordinal
selecting a row from a finite generated table; the ordinal does not size the
work, and the degree is bounded by the declared committed slice. The
independently derived model is therefore constant in the ordinal. The current
38-rung run passes in both directions.

Tier 1 irreducibility and Tier 2 divisor compatibility select mode 3. Mode 1
was attempted first on controlled families drawn entirely from the current
committed table:

- Tier 1 used all `C(2, n)`, `n = 1..8`. At fixed prime, Rabin's dense
  Frobenius remainder supplies the independently derived cubic degree model
  already used by HexBerlekamp. The current table is too short and its
  polynomial/divisor shapes too discrete for a stable wall model: the run was
  inconclusive, with `C` ranging from `32.529` to `195.888` on the verdict
  rungs.
- Tier 2 used compatibility of `C(2, 1)` inside `C(2, n)`, `n = 2..8`.
  There are `n` norm-accumulator steps; each contains a dense degree-`n`
  modular composition, giving the independently derived quartic model at fixed
  coefficient width and prime. This run was also inconclusive, with `C`
  ranging from `10.845` to `81.088`.

The clean mode-selection artifact is
`reports/bench-results/hex-conway-mode-audit-4896db30a-chungus2.json`
(SHA-256 `744dc31aa02efa00ea10d2ae7c7e001a258105cc834c89c261758530356d4e3d`).
These results rule out mode 1 without fitting a weaker exponent to the short
transition range. Mode 2 is unavailable: HexConway has no external comparator,
and no published wall-time upper bound covers the compiled Rabin or modular-
composition phase that controls these registrations. The mathematical
operation counts in the SPEC and source do not supply the cited, dominant-
phase wall bound that mode 2 requires.

Mode 3 deliberately gives up asymptotic regression detection for these two
finite committed-table verification operations. The canonical hard inputs are
`C(13, 6)` for Tier 1 and compatibility of `C(13, 1)` inside `C(13, 6)` for
Tier 2: they combine the largest committed prime with degree 6, and the latter
also has the deepest six-factor Frobenius chain. `budgetedBool` times only the
registered operation and returns `false` on a ceiling violation; the required
`expectedHash = hash true` therefore makes the 2 ms and 1 ms ceilings fail
closed. `maxSecondsPerCall = 2 s` remains only the child-process safety cap.

The Tier 1 ceiling is a measured-baseline ceiling with cross-machine margin:
2 ms is 13.7× the clean 146.576 µs calibration maximum on `chungus2` and
2.46× the earlier 812.958 µs median on `carica`. The Tier 2 ceiling is 1 ms,
11.5× its clean 87.061 µs calibration maximum. Both are operation-specific
regression gates rather than inherited harness defaults.

### Current scientific run

The clean acceptance run at commit `cf08a8247` on `chungus2` (AMD EPYC 9455,
Linux x86-64, Lean 4.34.0-rc2) used:

```sh
lake exe hexconway_bench run \
    Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum \
    Hex.ConwayBench.runTier1Irreducibility_13_6Checksum \
    Hex.ConwayBench.runTier2Compat_13_1_6Checksum \
    --export-file \
      reports/bench-results/hex-conway-mode3-cf08a8247-chungus2.json
```

The deterministic lookup run now includes ordinals 37 and 38, the `C(2, 7)`
and `C(2, 8)` rows. It is **consistent with declared complexity** over all 38
entries (`cMin=185.049`, `cMax=509.870`, `β=+0.130`); ordinal 38 measured
481.347 ns and produced the expected final hash `0x837443a59caa5094`.
Tier 1 measured a 127.283 µs median against its 2 ms ceiling, and Tier 2 a
76.065 µs median against its 1 ms ceiling. All five repeats completed within
their operation budgets and matched expected hash `0xb`.

The export artifact has SHA-256
`3dbd2185ea916a7e9de02a2a7564f2639b772167e1d1ba904bb07e658995f30f`.

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
