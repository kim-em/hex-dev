# HexBZ Cross-System Factorization Sweep

The current public-factor measurement adds verified original-coordinate M1
lifting, bounded modular degree-obstruction certificates, a measured cost
gate, and review-hardened route coverage at clean revision
`d580b121292be127be33b312fe888b00573379ed`. It was
measured 2026-07-30 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU
0. The unchanged no-decline classical row remains at clean revision
`b0150d2b`, and the unchanged Hex lattice row remains at clean revision
`0b95505b`. FLINT, PARI/GP, NTL, and Isabelle are the already-current
2026-07-28 exports from the same host, corpus, CPU placement, and timing
protocol. Those systems were not rerun because this change modifies only Hex's
bounded production classical route.

## Systems

- `hex-factor`: public production dispatcher
- `hex-lattice`: lattice factorization entry point
- `hex-classical-nodecline`: classical entry point without decline
- `flint`: python-flint 0.9.0
- `pari`: PARI/GP 2.17.3 through cypari2 2.2.4
- `ntl`: NTL 11.6.0 `ZZXFactoring`
- `isabelle-bz`: Isabelle2025-2 extraction from AFP
  `Berlekamp_Zassenhaus`, AFP 2026-05-29
- `isabelle-lll`: Isabelle2025-2 extraction from AFP
  `LLL_Factorization`, AFP 2026-05-29

The external toolchains came from transient nixpkgs environments. Isabelle
session and Haskell-export builds completed before the timed sweeps.

## Methodology

- Corpus: `bench/corpus/hexbz-factor-corpus.jsonl`
- Instances: 392
- Corpus SHA-256:
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`
- Per-call cutoff: 10 seconds
- Repeats: median of five if the first call is below one second; otherwise one
  call
- Early termination: disabled
- Warm line-protocol services; per-system protocol overhead recorded in JSON
- Solved-runtime p90 uses nearest rank; paired-ratio p10–p90 uses inclusive
  linearly interpolated deciles
- Cross-check: committed `expectedFactorDegrees` for 385 oracle-backed rows;
  pairwise factor counts for the seven no-oracle Hoeij rows

## Recorded Sweep

| System | OK | Timeout | p50 solved | p90 solved | Slowest solved | Protocol overhead |
|---|---:|---:|---:|---:|---:|---:|
| Hex public factor | 373 | 19 | 401.114 µs | 4.052 ms | 8.900 s | 17.215 µs |
| Hex lattice | 369 | 23 | 1.812 ms | 87.886 ms | 9.590 s | 18.848 µs |
| Hex classical, no decline | 372 | 20 | 386.358 µs | 5.556 ms | 3.717 s | 18.297 µs |
| FLINT | 391 | 1 | 66.850 µs | 1.184 ms | 1.228 s | 19.219 µs |
| PARI/GP | 391 | 1 | 99.958 µs | 1.254 ms | 823.201 ms | 23.755 µs |
| NTL | 391 | 1 | 135.631 µs | 2.714 ms | 1.919 s | 11.487 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs | 5.128 ms | 8.363 s | 17.777 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms | 1.219 s | 9.528 s | 17.136 µs |

These are service wall-clock values; protocol overhead is not subtracted.
Consequently, ratios near the overhead floor require a signal filter.

Every returned factor-degree multiset with a committed corpus oracle matched
it. Hex times out on every Hoeij-Zimmermann row, so it contributes no new
factor-count result on the seven rows without a committed degree oracle;
FLINT, PARI/GP, and NTL factor counts agree on all seven.

Relative to the pre-hot-path Hex record, the public median fell from 1.244 ms
to 401.114 µs and retained two additional solves, `sd5_x_phi45` and `sd6`.
The current no-decline classical entry now also solves `sd5_x_phi45`, leaving
`sd6` as the public dispatcher's one additional frontier success.

On 237 common rows for which current public Hex and the unchanged no-decline
diagnostic are at least 10× their own protocol overhead, public/classical has
median 1.003× and p10–p90 0.710×–1.140×. Public is faster on 116 and classical
on 121. The broader band now contains the deliberately selective M1 wins;
no-decline remains an M2 diagnostic that omits bounded decline/fallback
behavior and the public result check. The production path improves selected
hard rows and adds the `sd6` solve.

On the corresponding 234 public/verified-Isabelle BZ rows, Hex has median
0.852× and p10–p90 0.450×–2.033×; Hex is faster on 143 and Isabelle on 91. The
14.8% aggregate lead is clear, though the family spread still rules out a claim
of uniform superiority.

The new M1 result is concentrated on non-monic Chebyshev and Legendre rows:
U24 falls from 2.610 ms to 0.816 ms, P28 from 8.205 ms to 4.952 ms, P30
from 13.807 ms to 11.034 ms, and P38 from 13.602 ms to 8.422 ms. The complete
phase analysis, degree-bound no-go, modular-scan decision, and dependency
outcomes for issues #9104–#9109 are in
[`hexbz-m1-chebyshev-legendre.md`](hexbz-m1-chebyshev-legendre.md).

Against the immediately preceding `0b95505b` sweep, the cached recombination
implementation has a 0.988× eligible-row median and a 171–72 win split. Its
main effect is deliberately concentrated: `sd5` falls from 89.008 ms to
39.730 ms, while its two shifted variants fall from 76.152–76.981 ms to
28.073–29.903 ms.

The improvement is broad but not universal. Family medians below compare the
fresh public service with the pre-hot-path
`hexbz-factor-sweep-hex-5c371a5a-chungus2.json` record; values below 1 are
faster.

| Family | Common rows | Median new/old | Rows slower |
|---|---:|---:|---:|
| Certificate boundary | 1 | 0.372× | 0 |
| Chebyshev | 28 | 0.204× | 1 |
| Conway | 186 | 0.306× | 3 |
| Cyclotomic | 32 | 0.606× | 1 |
| Cyclotomic products | 19 | 0.613× | 0 |
| Laguerre | 20 | 0.231× | 0 |
| Legendre | 20 | 0.175× | 0 |
| Random products | 30 | 0.204× | 0 |
| Signed-digit products | 9 | 0.421× | 1 |
| Swinnerton-Dyer | 11 | 0.160× | 0 |
| Wilkinson | 15 | 0.895× | 5 |

Every family median improves over the pre-hot-path record. The cumulative
GCD/Hensel stage had an all-row paired median of 0.964× against its immediately
preceding guarded-tree export; the recombination stage above is its own A/B
against `0b95505b`.

Review found that coordinate transport was evaluated before the M1 gate, so
monic rows paid an unused conversion even though the predicate was false.
Moving it inside the taken branch makes the eight previously slow cyclotomic
rows 0.628×–0.684× of the first M1 record and restores them to
1.009×–1.041× of `b0150d2b`. This source-correlated full-sweep result replaces
the earlier, unarchived frequency-drift interpretation.

## Charts

The six most useful presentation figures are:

- [Combined cactus plot](figures/hexbz-cactus-combined.svg)
- [Cyclotomic-products cactus plot](figures/hexbz-cactus-cyclotomic-products.svg)
- [Random-products runtime by degree](figures/hexbz-runtime-degree-random-products.svg)
- [Swinnerton-Dyer cactus plot](figures/hexbz-cactus-swinnerton-dyer.svg)
- [Swinnerton-Dyer runtime by degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)
- [Hoeij-Zimmermann cactus plot](figures/hexbz-cactus-hoeij-zimmermann.svg)

All 25 current family charts are under `reports/figures/hexbz-*`. Regenerate
them with:

```sh
uv run --with matplotlib python3 scripts/plots/hexbz-cactus.py
```

## Artifacts

Fresh Hex exports:

- `reports/bench-results/hexbz-factor-sweep-hex-d580b121-m1-review-chungus2.json`
  (current public factor; SHA-256
  `455b5fc28681707357eda6c60fba25531937128c51f9c3065231adf73dbd959d`)
- `reports/bench-results/hexbz-factor-sweep-hex-b0150d2b-recombine-cache-chungus2.json`
  (preceding public and unchanged no-decline classical; SHA-256
  `7222c12c206d9fdb3489d98595c72f9eb254f31108e5136722242784eb086be3`)
- `reports/bench-results/hexbz-factor-sweep-hex-0b95505b-gcd-hensel-final-chungus2.json`
  (preceding public/classical and current lattice; SHA-256
  `9f9f63ac9f35b3af6d35e530b085a1a1e47e7d03d958179d7597d7850e59c583`)
- `reports/bench-results/hexbz-factor-sweep-hex-53bb12e2-guarded-tree-all-chungus2.json`
  (preceding all-Hex reference; SHA-256
  `926e91245e45523a40e8b915004bf4e0e17f01ed3547feca94589760d3e55e27`)
- `reports/bench-results/hexbz-factor-sweep-hex-a087b28f-guarded-tree-chungus2.json`
  (preceding public-only diagnostic; SHA-256
  `1f03e479ca0d14bedb11a68960da865760072a66b7299d33ee3acd19138bf1e7`)
- `reports/bench-results/hexbz-factor-sweep-hex-b4b36754-exact-factor-only-chungus2.json`
  (preceding public A/B reference; SHA-256
  `090b594a14b12af8332fef091d2bd8ca5652c3e7566e6bd452a984eb473a058a`)
- `reports/bench-results/hexbz-factor-sweep-hex-b4b36754-exact-only-chungus2.json`
  (same-day factor-only A/B reference; SHA-256
  `4ceadcbb1dd54f7e49d77efdd3ed199cb84633fb54c733a6041afa2118ddf9b2`)
- `reports/bench-results/hexbz-factor-sweep-hex-aaabcf15-chungus2.json`
  (preceding lattice and no-decline classical reference; SHA-256
  `30e56da9aa3c6f4f50faca4ef19e5c4d4f6523362542f2d8967ca7665f62f747`)

Unchanged current external exports:

- `hexbz-factor-sweep-flint-5c371a5a-chungus2.json` (SHA-256
  `f656372a18c85fe5fd35dd415033842de95348f718e89031213bb310fdc88da5`)
- `hexbz-factor-sweep-pari-5c371a5a-chungus2.json` (SHA-256
  `fdd253e8944a90f7cdf112a7e36f9d28ec9a481f4c142122ddda47cbd3216ed9`)
- `hexbz-factor-sweep-ntl-5c371a5a-chungus2.json` (SHA-256
  `65db4a80bac19ac390e0e495c56bfa7d0a899a240fe71d61a4de60b2796442ed`)
- `hexbz-factor-sweep-isabelle-bz-5c371a5a-chungus2.json` (SHA-256
  `da44a233d02f8a321ad50878180366df9f5cacb91e9f657ed8138046f7a21e3f`)
- `hexbz-factor-sweep-isabelle-lll-5c371a5a-chungus2.json` (SHA-256
  `512d59e13be1737a71c2f06a93bcdfab4729f0afdfea3452d89f1393dfda2789`)

The latter paths are relative to `reports/bench-results/`. They retain revision
`5c371a5a` in their names because that is the code revision at which those
external services were measured; the corpus and protocol are identical to the
fresh Hex sweep.

## Reproducing Hex

```sh
lake build hexbz_factor_service
taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor,hex-lattice,hex-classical-nodecline \
  --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep-hex.json
```

The unchanged external services can be regenerated with the same command and
their respective Nix environments:

```sh
taskset -c 0 uv run --with python-flint python3 scripts/bench/factor_sweep.py \
  --systems flint --cutoff 10 --no-early-terminate --output /tmp/flint.json
taskset -c 0 nix-shell \
  -p 'python3.withPackages (ps: [ ps.cypari2 ps.cysignals ])' \
  --run 'python3 scripts/bench/factor_sweep.py --systems pari --cutoff 10 \
    --no-early-terminate --output /tmp/pari.json'
taskset -c 0 nix-shell -p ntl gmp pkg-config gcc \
  --run 'python3 scripts/bench/factor_sweep.py --systems ntl --cutoff 10 \
    --no-early-terminate --output /tmp/ntl.json'
nix-shell -p isabelle ghc curl coreutils gnutar gzip \
  --run 'bash scripts/oracle/setup_bz_isabelle.sh && \
    bash scripts/oracle/setup_bz_lll_isabelle.sh'
taskset -c 0 nix-shell -p isabelle ghc curl coreutils gnutar gzip \
  --run 'python3 scripts/bench/factor_sweep.py \
    --systems isabelle-bz,isabelle-lll --cutoff 10 \
    --no-early-terminate --output /tmp/isabelle.json'
```

Commit-named older exports remain historical records and are not merged into
this current-corpus summary.
