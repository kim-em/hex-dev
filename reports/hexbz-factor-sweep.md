# HexBZ Cross-System Factorization Sweep

This page records the current reproducible measurements for the public
factorization entry point and external comparators.

## Systems

- `hex-factor`: public Hex production factorization at clean revision
  `1a78e196b3e75f83d23eb4b7d8679750f788249b`
- `flint`: python-flint 0.9.0
- `pari`: PARI/GP 2.17.2 through cypari2 2.2.4
- `ntl`: NTL 11.6.0 `ZZXFactoring`
- `isabelle-bz`: Isabelle2025-2 extraction from AFP
  `Berlekamp_Zassenhaus`, AFP 2026-05-29
- `isabelle-lll`: Isabelle2025-2 extraction from AFP
  `LLL_Factorization`, AFP 2026-05-29

The external toolchains came from transient nixpkgs environments. Isabelle
session and Haskell-export builds completed before timed calls. Hex includes
its restored fast polynomial dispatchers and guarded Hensel ordered-product
tree; the executable hash and source fingerprint accompany its record.

## Method

- Host: `chungus2`, AMD EPYC 9455, Linux x86-64, Lean `4.35.0-rc3` for Hex.
- CPU placement: Hex harness and service pinned to automatically leased CPU 33.
  Shared-host load averages at the start were 167.64, 129.63, and 77.49;
  at the end they were 39.99, 95.76, and 71.59. Every completed sample is
  retained. The external record used CPU 0 on the same shared host.
- Corpus: `bench/corpus/hexbz-factor-corpus.jsonl`, all 392 rows.
- Corpus SHA-256:
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Per-call cutoff: 10 seconds.
- Repeats: median of five when the first call is below one second; one call
  otherwise.
- Early termination disabled: every row was attempted, and all nine Hex
  timeouts were retained. The external record also attempted every row.
- Cross-check: committed expected factor degrees where available, and
  agreement with the separately recorded external answers otherwise.
- Summary quantiles: the usual median; p10 and p90 are the observations at
  zero-based indices `n // 10` and `(9 * n) // 10` after sorting the solved
  times. Paired comparisons require each measurement to strictly exceed
  ten times its own protocol overhead.

The per-system protocol overheads were 31.397 us for Hex, 15.493 us for
FLINT, 11.027 us for NTL, 18.006 us for PARI, 18.628 us for Isabelle BZ,
and 18.848 us for Isabelle LLL. Reported service times do not subtract them.

## Artifacts

The plotting tool selects the newest current-corpus record for each system:

- `reports/bench-results/hexbz-factor-sweep-1a78e196-fast-kernels-chungus2.json`
  supplies Hex; SHA-256
  `91d728908c8ecfaa878303c1ff9931b2e7626839c4c475b80bca9570ada7b2f8`.
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  supplies FLINT, NTL, PARI, Isabelle BZ, and Isabelle LLL; SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`.

Both records use a clean worktree, the current corpus hash, the same host,
cutoff, and repetition policy. All answering systems agree. They are
observations from separate shared-host runs; these figures do not isolate the
performance effect of restoring the dispatchers.

## Current summary

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 383 | 9 | 283.710 us | 7.961 ms | 3.934 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

## Regeneration

Build the Hex service and run from a clean source revision:

```sh
lake build hexbz_factor_service
python3 - <<'PYTHON'
import os
import subprocess
import sys
from scripts.bench.cpu_lease import cpu_lease

cpu, lease = cpu_lease()
os.sched_setaffinity(0, {cpu})
print(f"CPU {cpu}, shared-host load {os.getloadavg()}", flush=True)
subprocess.run([
    sys.executable, "scripts/bench/factor_sweep.py",
    "--systems", "hex-factor", "--cutoff", "10", "--no-early-terminate",
    "--output", "/tmp/hexbz-factor-sweep-hex.json",
], check=True)
PYTHON
```

Retain the result, record its source fingerprint with
`scripts/bench/check_factor_sweep_freshness.py --record <sweep.json>`, and
reproduce the tables with:

```sh
python3 scripts/bench/factor_sweep_table.py
```

Regenerate and verify every plot with:

```sh
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```

CI runs `scripts/bench/check_factor_sweep_freshness.py` and the plot `--check`.
Relevant factorization, corpus, harness, or comparator changes require fresh
data and all 25 SVGs. External curves retain their own recorded measurements.

Exact sorted and paired ranks come from the same selected records:

```sh
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 145
```
