# HexBZ Cross-System Factorization Sweep

This page records the current reproducible measurement, not a history of old
algorithm variants.

## Systems

- `hex-factor`: public Hex production factorization at clean revision
  `acb930159913e8e6c04a271e4e9aa0d227ea0e7b`
- `flint`: python-flint 0.9.0
- `pari`: PARI/GP 2.17.2 through cypari2 2.2.4
- `ntl`: NTL 11.6.0 `ZZXFactoring`
- `isabelle-bz`: Isabelle2025-2 extraction from AFP
  `Berlekamp_Zassenhaus`, AFP 2026-05-29
- `isabelle-lll`: Isabelle2025-2 extraction from AFP
  `LLL_Factorization`, AFP 2026-05-29

The external toolchains came from transient nixpkgs environments. Isabelle
session and Haskell-export builds completed before timed calls.

## Method

- Host: `chungus2`, AMD EPYC 9455, Linux x86-64
- CPU placement: harness and each service pinned to CPU 0
- Corpus: `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows
- Corpus SHA-256:
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`
- Per-call cutoff: 10 seconds
- Repeats: median of five when the first call is below one second; one call
  otherwise
- Early termination: disabled; every row was attempted by every system
- Cross-check: committed expected factor degrees where available, pairwise
  agreement otherwise

The per-system protocol overheads were 21.472 us for Hex, 15.493 us for FLINT,
11.027 us for NTL, 18.006 us for PARI, 18.628 us for Isabelle BZ, and 18.848 us
for Isabelle LLL. Reported service times do not subtract them.

## Artifacts

The plotting tool selects the newest valid record for each system:

- `reports/bench-results/hexbz-factor-sweep-acb93015-hex-chungus2.json`
  supplies Hex; SHA-256
  `42b69d970e0cba7336091b16e512d89e9aed4383bdb661edbd6cc97e96f56138`.
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  supplies FLINT, NTL, PARI, Isabelle BZ, and Isabelle LLL; SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`.

Both records use a clean worktree, the current corpus hash, the same host and
protocol, and no early termination. The Hex executable SHA-256 is
`ec2875103bb4e520947d952889df69df27805d10115e6ee2f24ed814c9098e47`.
All answering systems agree.

## Current summary

| System | OK | Timeout | p50 solved | p90 solved | Slowest solved |
|---|---:|---:|---:|---:|---:|
| Hex public factor | 376 | 16 | 367.114 us | 7.503 ms | 7.866 s |
| FLINT | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

## Regeneration

Build the Hex service, stage the desired external services, then run:

```sh
lake build hexbz_factor_service
taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor,flint,ntl,pari,isabelle-bz,isabelle-lll \
  --cutoff 10 --no-early-terminate --output /tmp/hexbz-factor-sweep.json
```

Regenerate and verify every plot with:

```sh
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```

CI runs `scripts/bench/check_factor_sweep_freshness.py` and the plot `--check`.
Relevant factorization, corpus, harness, or comparator changes therefore make a
PR fail until its data and all 25 SVGs are refreshed.
