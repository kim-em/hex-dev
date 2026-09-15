# Rank-locus proof performance

## Preregistered measurements

`scripts/bench/rank_locus_sweep.py` registers eight fresh-module probes from the
`symbolic` family in `bench/HexGenericRank/Bench.lean`, restricted to thresholds
`r ≤ 3`. The checked-in literals expand that family's triangular and factorized
matrices. The selected rungs cover dimensions 2, 4 and 8; one and two variables;
degrees one and two; support caps one and four; and both full and low generic
rank. These are structured inputs, not a claim about worst-case expression growth.

Each case has six adjacent import-baseline/candidate pairs, with alternating
AB/BA order. The full-build ceiling is **30 seconds**, with a **120 second**
cleanup timeout. All completed samples are retained on the shared host, pinned
to one automatically selected CPU. The baseline imports exactly the same modules
as the candidates. Comparator: **no-comparable-surface-in-named-comparator**;
Mathlib has no tactic that produces a symbolic rank-locus statement.

The term-form probes certify the entire generator list. Lean's profiler records
batch reflection, compiled enumeration (including quotation), and the synchronous
kernel declaration check of `detIdealGensList` separately. Nested profiling is
disabled inside the batch and declaration-check categories. The full-build time
also includes entry and display proofs, theorem construction, imports, startup,
linting and serialization. No probe or provider reads an in-process clock.

Every accepted result must depend only on `propext`, `Classical.choice` and
`Quot.sound`. The runner records proof nodes, artifact sizes, source hashes,
compiler output, host activity and signed baseline differences.

The default `minorWork` limit is 50,000 Laplace work units. These probes use
at most 18,816 units. The next 8×8, support-one rung at `r = 4` requires
117,600 units and is rejected before enumeration, as the tactic tests verify.
Runtime also includes canonical polynomial operations and duplicate comparisons.



## Results

Measured source: `5a18a47eb37fa0b20d4b64786552abeb22a37467`; `leanprover/lean4:v4.34.0`. Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 1. The checkout and dependency checkouts were clean and unchanged throughout the sweep.

All 48 pairs (96 fresh builds) completed and are retained in the [raw record](data/hex-determinantal-ideal-mathlib-probes-5a18a47eb.json.gz). The shared harness accepted the sweep, including the preregistered ceiling and axiom checks. These absolute times describe this shared host; they do not establish a speedup.

| Probe | Baseline median (s) | Candidate median / max (s) | Batch (ms) | Enumeration (ms) | Kernel (ms) | Proof nodes | `.olean` (KiB) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Full2R1 | 2.708 | 2.819 / 2.839 | 5.17 | 0.19 | 5.37 | 1527 | 100.4 |
| Full2R2 | 2.714 | 2.875 / 2.949 | 8.42 | 0.21 | 7.41 | 2303 | 128.7 |
| Low2R1 | 2.703 | 2.815 / 2.916 | 6.15 | 0.19 | 6.15 | 1659 | 106.2 |
| Full4R3 | 2.703 | 2.929 / 2.988 | 7.64 | 0.51 | 31.75 | 2080 | 125.0 |
| Low4R2 | 2.705 | 4.133 / 4.265 | 21.50 | 1.94 | 311.00 | 12325 | 481.5 |
| Low4R3 | 2.706 | 3.411 / 3.433 | 21.45 | 2.91 | 380.50 | 2006 | 100.5 |
| Full8R3 | 2.715 | 7.310 / 7.330 | 16.55 | 41.90 | 4050.00 | 3313 | 176.7 |
| Low8R3 | 2.715 | 11.485 / 11.747 | 22.50 | 61.05 | 6990.00 | 16398 | 645.6 |

Profile columns are medians of Lean profiler totals. The raw record also includes the private/server artifact sizes, individual signed baseline differences, peak memory, compiler output, source hashes, and host-activity context. Every candidate in every round reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

The complete sweeps at
[`7e5dcc687`](data/hex-determinantal-ideal-mathlib-probes.json.gz) and
[`0ce48bca6`](data/hex-determinantal-ideal-mathlib-probes-0ce48bca6.json.gz)
are also retained. They measured earlier public result types; the table above
uses the implementation whose ideal payload supports fields in every universe
through `IdealData.vanishing`. All three sweeps met their ceilings and axiom
checks; no completed samples were discarded.

From a clean checkout of the measured source, with the pinned dependencies:

```bash
lake build HexDeterminantalIdealMathlibProofProbe
python3 scripts/bench/rank_locus_sweep.py --shared-host \
  --cpu "$(python3 scripts/bench/idle_core.py)" \
  --output /tmp/rank-locus-probes.json
```
