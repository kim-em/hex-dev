# HexBZ Cross-System Factorization Sweep

This page records the current reproducible measurement, not a history of old
algorithm variants.

## Systems

- `hex-factor`: public Hex production factorization at clean revision
  `39cc3126`
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
- CPU placement: harness and each service pinned to one core. The committed
  external record used CPU 0; the current Hex record used verified-idle CPU 2.
  Other work shares this host, so regeneration selects a verified-idle core
  rather than assuming that CPU 0 is free; record the chosen core with any new
  result. The CPU 0/70 control in
  [hexbz-support-traversal.md](hexbz-support-traversal.md) checks that an idle
  core is interchangeable with CPU 0 on this host.
- Corpus: `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows
- Corpus SHA-256:
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`
- Per-call cutoff: 10 seconds
- Repeats: median of five when the first call is below one second; one call
  otherwise
- Summary quantiles: the usual median; p10 and p90 are the observations at
  one-indexed ranks `floor(0.1 n) + 1` and `floor(0.9 n) + 1` after sorting the
  `n` solved times. Paired comparisons retain a row only when both measurements
  strictly exceed ten times their own protocol overhead.
- Early termination: the external record attempted every row. The Hex record
  groups every family by increasing degree, but only stops a designated
  monotonic family after three consecutive timeouts. This reordered the calls
  and skipped only `hoeij_F630`, recording the timeout the cactus plot assigns
  it.
- Cross-check: committed expected factor degrees where available, pairwise
  agreement otherwise

The per-system protocol overheads were 22.914 us for Hex, 15.493 us for FLINT,
11.027 us for NTL, 18.006 us for PARI, 18.628 us for Isabelle BZ, and 18.848 us
for Isabelle LLL. Reported service times do not subtract them.

## Artifacts

The plotting tool selects the newest valid record for each system:

- `reports/bench-results/hexbz-factor-sweep-39cc3126-hex-chungus2-cpu2.json`
  supplies Hex; SHA-256
  `2043b223de4d1243e97fa79f09e143091669273c78ae1b859509f48b19cd37f3`.
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  supplies FLINT, NTL, PARI, Isabelle BZ, and Isabelle LLL; SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`.

The older `hexbz-factor-sweep-d27e0bf2-hex-chungus2.json` remains available for
audit but is not publishable: its 43.976 us protocol overhead and a matching
inflated band of short cyclotomic calls show that its fixed call cost was
contaminated by host contention.

Both records use a clean worktree, the current corpus hash, the same host,
cutoff, and repetition policy. The one early-terminated Hex row is described
above. All answering systems agree.

## Current summary

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 383 | 9 | 272.153 us | 6.651 ms | 3.970 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

This table is one release sweep. The integration comparison in
[hexbz-quadratic-norm-certificate.md](hexbz-quadratic-norm-certificate.md)
commits two runs per side and reports their spread, providing the nearby
repeat/noise check without treating old timings as the current result.

## Regeneration

Build the Hex service, stage the desired external services, then run:

```sh
lake build hexbz_factor_service
BENCH_CORE="$(python3 scripts/bench/idle_core.py)"
taskset -c "$BENCH_CORE" \
  python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 \
  --output /tmp/hexbz-factor-sweep-hex.json
taskset -c "$BENCH_CORE" \
  python3 scripts/bench/factor_sweep.py \
  --systems flint,ntl,pari,isabelle-bz,isabelle-lll \
  --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep-external.json
```

The first command reproduces the current Hex early-termination policy; the
second attempts every row, as the external record did. Reproduce the tables
from the selected records with:

```sh
python3 scripts/bench/factor_sweep_table.py
```

Regenerate and verify every plot with:

```sh
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```

CI runs `scripts/bench/check_factor_sweep_freshness.py` and the plot `--check`.
Relevant factorization, corpus, harness, or comparator changes therefore make a
PR fail until its data and all 25 SVGs are refreshed.

Exact solved ranks around the former Hex / verified Isabelle BZ crossover
region, in both the independently sorted cumulative form the charts plot and
the paired-testcase form, come from the same records:

```sh
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 145
```

The historical phase-by-phase attribution and its current resolution are in
[reports/hexbz-cactus-elbow.md](hexbz-cactus-elbow.md).
