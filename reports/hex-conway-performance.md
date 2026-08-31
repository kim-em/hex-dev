# HexConway Performance Report

## Bench Targets

- `Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum`: mode 1,
  two-sided affine lookup/materialization/checksum cost over all 38 committed
  table keys.
- `Hex.ConwayBench.runTier1Irreducibility_13_6Checksum`: mode 3, fixed Rabin
  verification of `C(13, 6)` under a 2 ms operation-scoped ceiling.
- `Hex.ConwayBench.runTier2Compat_13_1_6Checksum`: mode 3, fixed compatibility
  verification of `C(13, 1)` inside `C(13, 6)` under a 1 ms
  operation-scoped ceiling.
- `runConwayPolySupported_2_1Checksum`, the other six fixed Tier 1 checks, and
  the other two fixed Tier 2 checks are expected-hash anchors. They make no
  complexity claim and do not discharge performance coverage.

`HexConway` advertises the implemented `tier1-committed-table` and
`tier2-divisor-compatibility` input families. Tier 3 on-demand Conway search
is unimplemented. Tier 2 primitivity exists, but is not a separate declared
Phase-4 input family; the Tier 2 family here is specifically compatibility.

## Tier 1 proof budget

`HexConway/SPEC/hex-conway.md` sizes the committed slice by proof-checking cost:
include as much of the Luebeck table as possible while the generated Tier 1
correctness theorems still check in only a few minutes. That elaboration and
kernel-replay cost is separate from runtime benchmarking.

On a warm dependency tree, after deleting the built `HexConway` Lean and IR
outputs, one `lake build HexConway` on AMD EPYC 9455, Linux x86-64, and Lean
4.33.0-rc1 gave:

| Scope | Entries | `Table` | `Certificates` | `Api` |
|---|---:|---:|---:|---:|
| `2:6, 3:6, 5:6, 7:6, 11:6, 13:6` | 36 | 2.6 s | 28 s | 2.8 s |
| `2:8, 3:6, 5:6, 7:6, 11:6, 13:6` | 38 | 2.7 s | 31 s | 3.0 s |

These are single scope measurements, not distributions. They establish that
the committed 38-entry scope remains affordable; they do not claim that degree
8 is a measured maximal frontier. The binary column was extended to 8 because
the proof cost was small and `GF(2^8)` is relevant to the packed
representation. A true frontier study would measure successive candidates per
prime.

## Verdicts

### Ordered mode selection

The committed lookup selects mode 1 with model `degree + 2`. An ordinal lookup
performs fixed finite-key dispatch, materializes `degree + 1` coefficients, and
`checksumPoly` walks those coefficients. The benchmark therefore recovers the
entry degree from each ordinal and uses the independently derived affine model
rather than calling the ordinal itself constant-sized. The 38-rung acceptance
run passes in both directions.

Tier 1 irreducibility and Tier 2 compatibility select mode 3. Controlled mode-1
ladders were attempted first from a clean source state at commit `bab1fa3c6`:

- Tier 1 used `C(2, n)` for `n = 1..8`. At fixed prime, the Rabin test's
  degree-many dense Frobenius/remainder work supplies a cubic degree model.
  Five outer trials were inconclusive (`cMin=34.371`, `cMax=227.532`; beta
  unavailable).
- Tier 2 used compatibility of `C(2, 1)` inside `C(2, n)` for `n = 2..8`.
  `normX` takes `n` Frobenius/product steps and each dense modular operation is
  quadratic in degree, again giving a cubic model. Five outer trials were
  inconclusive (`cMin=114.169`, `cMax=260.906`; beta unavailable).

The clean audit artifact is
`reports/bench-results/hex-conway-mode-audit-bab1fa3c6-chungus2.json`
(SHA-256 `51ea7b4033f076be278b04c8dd4b1fe5c097a990b8869dcb6841420c58fae770`).
The temporary ladder registrations exist at that cited commit and were removed
after the audit because an inconclusive ladder cannot remain advertised as
Phase-4 performance evidence. Their complete schedules and benchmark
configuration remain in the commit and artifact.

Mode 2 is unavailable: HexConway has no external executable comparator and no
published dominant-phase wall-time bound for compiled Rabin verification or
modular composition. Mathematical operation counts alone do not provide the
cited wall-time bound that mode 2 requires.

Mode 3 therefore uses the canonical hard committed inputs. `C(13, 6)` combines
the largest committed prime with degree 6 for Tier 1. Compatibility of
`C(13, 1)` inside `C(13, 6)` additionally uses the deepest six-factor
Frobenius chain for Tier 2. With `HEXCONWAY_ENFORCE_BUDGETS=1`, `withBudget`
times every auto-tuned invocation and throws immediately if the operation
exceeds 2 ms or 1 ms. The scientific run sets this variable; CI `verify`
deliberately leaves it unset so a noisy hosted runner does not assert timing.
`expectedHash = hash true` separately fails correctness regressions, and
`maxSecondsPerCall = 2 s` remains only the child-process safety cap.

The current conservative margins use the largest per-call value in the clean
acceptance run: the Tier 1 ceiling is 15.3 times 130.692 us, and the Tier 2
ceiling is 13.0 times 77.218 us. No invocation threw, so the operation-scoped
ceiling held throughout every auto-tuned batch, including iterations whose
result is not retained as the repeat hash.

### Current scientific run

The clean acceptance source commit is `ba8d354f8` on `chungus2` (AMD EPYC
9455, Linux x86-64, Lean 4.34.0-rc2). It ran every HexConway registration with
five outer trials for the parametric lookup and the registrations' five fixed
repeats:

```sh
HEXCONWAY_ENFORCE_BUDGETS=1 \
  ./.lake/build/bin/hexconway_bench run \
  --filter Hex.ConwayBench --outer-trials 5 \
  --export-file \
    reports/bench-results/hex-conway-mode3-ba8d354f8-chungus2.json
```

The lookup is consistent with its declared affine complexity over all 38
entries (`cMin=59.109`, `cMax=63.621`, `beta=-0.015`). Ordinal 38, `C(13, 6)`,
had a 484 ns median; every row's hash agreed across its five trials.

The fixed registrations measured:

| Target suffix | Median | Maximum | Expected hash |
|---|---:|---:|---:|
| `runConwayPolySupported_2_1Checksum` | 87 ns | 87 ns | `0x8d105cfbb68da744` |
| `runTier1Irreducibility_2_1Checksum` | 1.176 us | 1.217 us | `0xb` |
| `runTier1Irreducibility_2_6Checksum` | 19.057 us | 19.375 us | `0xb` |
| `runTier1Irreducibility_3_6Checksum` | 37.676 us | 38.821 us | `0xb` |
| `runTier1Irreducibility_5_6Checksum` | 68.489 us | 70.289 us | `0xb` |
| `runTier1Irreducibility_7_6Checksum` | 93.672 us | 98.116 us | `0xb` |
| `runTier1Irreducibility_11_6Checksum` | 113.984 us | 115.828 us | `0xb` |
| `runTier1Irreducibility_13_6Checksum` | 130.367 us | 130.692 us | `0xb` |
| `runTier2Compat_2_3_6Checksum` | 25.698 us | 25.981 us | `0xb` |
| `runTier2Compat_2_4_8Checksum` | 47.836 us | 49.098 us | `0xb` |
| `runTier2Compat_13_1_6Checksum` | 75.997 us | 77.218 us | `0xb` |

All repeats agreed with their expected hashes. The artifact is
`reports/bench-results/hex-conway-mode3-ba8d354f8-chungus2.json` (SHA-256
`9849ef75a1eb01ce0f902b8e560f7fe12ced86f33fe1fdb6c4999fa7384f3bc2`).

`lake exe hexconway_bench verify` also passes all 12 shipped registrations.
Verification is a deterministic registration/hash smoke gate; the scientific
command above is the operation-budget evidence.

## Comparator Ratios

`HexConway/SPEC/hex-conway.md` names no external Phase-4 performance comparator
for the Tier 1 committed-table surface, so there are no
`phase4.comparators` ratios. The Luebeck table is an input source, not an
executable comparator, and the current API has no alternative Tier 1
implementation to register as a `compare` group.

## Profile

### `tier1-committed-table`

The Tier 1 lookup profile was captured at commit
`3bc24c50fbe57487776c433106894ee544a6d656` on `carica` (Apple M2 Ultra,
macOS 14.6.1, arm64), using `samply 0.13.1` at 999 Hz and the
lean-bench-samply timed-region filter at commit
`602da96df3537341b50de9add2f137b0a75a68df`:

```sh
scripts/profile/run_profile.sh \
  ./.lake/build/bin/hexconway_bench \
  Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum \
  36 1000000000
```

The representative `C(13, 6)` case retained 924 bench-thread samples. Flat
cost was 66.2% Lean runtime/outlined helpers, 26.3% allocation/free, and 7.5%
Hex own code. Inclusive attribution was the registered lookup (57.9%), table
lookup (57.4%), checksum (39.0%), and dense-polynomial trimming (10.0%). This
is the expected stored-row materialization and checksum path; no attribution
follow-up is needed.

### `tier2-divisor-compatibility`

The canonical Tier 2 profile was captured from clean commit `045ffb12e` on
`chungus2` with `samply` at 999 Hz and lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. The profile-only pure probe used a
runtime-derived zero constant term at parameter one. This preserves the exact
`C(13, 1)` in `C(13, 6)` operation while preventing native compilation from
reducing the closed successful check. The probe was removed after capture and
is not part of the shipped registration surface.

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply-9813 \
  scripts/profile/run_profile.sh \
  ./.lake/build/bin/hexconway_bench \
  Hex.ConwayBench.profileTier2Compat 1 1000000000
```

The child ran 8192 inner repeats at 80.642 us per call with hash `0xb`.
Filtering retained 654 of approximately 665 expected bench-thread samples,
rejected 7 outside timed regions, found no other-thread samples in the windows,
and passed both calibration (0.746 ms residual under the 5 ms limit) and the
plus/minus 5 ms sensitivity test.

Flat samples were 32.42% allocation, 28.59% Lean/Hex own code, 34.56% Lean
runtime, and 4.43% other. Inclusive Hex attribution was
`Hex.Conway.compatCheck` (99.85%), `Hex.Conway.normX` (99.54%),
`Hex.Conway.normAux` (90.21%), `Hex.FpPoly.composeModMonicImpl` (76.30%),
`Hex.Conway.frobeniusIter` (75.99%), and `Hex.DensePoly.mulImpl` (48.32%). The
dominant samples are therefore inside the registered compatibility operation,
principally norm construction, modular composition, dense multiplication, and
reduction. No attribution-rule follow-up is required.

## Concerns
