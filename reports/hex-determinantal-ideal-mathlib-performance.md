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


## Results

Measured source: `0ce48bca65b2627b95b4734133534d0f1910ed54`; `leanprover/lean4:v4.34.0`. Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 2. The checkout and dependency checkouts were clean and unchanged throughout the sweep.

All 48 pairs (96 fresh builds) completed and are retained in the [raw record](data/hex-determinantal-ideal-mathlib-probes-0ce48bca6.json.gz). The shared harness accepted the sweep, including the preregistered ceiling and axiom checks. These absolute times describe this shared host; they do not establish a speedup.

| Probe | Baseline median (s) | Candidate median / max (s) | Batch (ms) | Enumeration (ms) | Kernel (ms) | Proof nodes | `.olean` (KiB) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Full2R1 | 2.710 | 2.807 / 2.835 | 5.23 | 0.20 | 5.36 | 1527 | 100.4 |
| Full2R2 | 2.709 | 2.875 / 2.940 | 8.34 | 0.21 | 7.28 | 2303 | 128.7 |
| Low2R1 | 2.708 | 2.875 / 2.914 | 6.07 | 0.20 | 6.33 | 1659 | 106.2 |
| Full4R3 | 2.713 | 2.925 / 3.005 | 7.64 | 0.52 | 31.55 | 2080 | 125.0 |
| Low4R2 | 2.711 | 4.120 / 4.643 | 21.40 | 1.93 | 311.00 | 12325 | 481.5 |
| Low4R3 | 2.731 | 3.486 / 3.661 | 21.65 | 2.93 | 390.00 | 2006 | 100.5 |
| Full8R3 | 2.702 | 7.419 / 7.538 | 16.60 | 42.10 | 4140.00 | 3313 | 176.7 |
| Low8R3 | 2.699 | 11.525 / 11.720 | 22.50 | 60.55 | 7015.00 | 16398 | 645.6 |

Profile columns are medians of Lean profiler totals. The raw record also includes the private/server artifact sizes, individual signed baseline differences, peak memory, compiler output, source hashes, and host-activity context. Every candidate in every round reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

The [earlier complete sweep](data/hex-determinantal-ideal-mathlib-probes.json.gz)
at `7e5dcc687fa89f058d4a66a45854ab3d39f43f54` is also retained in full.
It preceded the API change allowing an independent field-point universe;
the table above measures the updated source. Both sweeps met their ceilings
and axiom checks; no completed samples were discarded.

From a clean checkout of the measured source, with the pinned dependencies:

```bash
lake build HexDeterminantalIdealMathlibProofProbe
python3 scripts/bench/rank_locus_sweep.py --shared-host \
  --cpu "$(python3 scripts/bench/idle_core.py)" \
  --output /tmp/rank-locus-probes.json
```
