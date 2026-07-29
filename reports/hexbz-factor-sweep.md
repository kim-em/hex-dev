# HexBZ Cross-System Factorization Sweep

The current public-factor measurement covers the exact-exponent/factor-only
Hensel implementation over base revision
`b4b3675472f58958c9c2f9b2ab2f7aae16c3dc62`; the current lattice and
no-decline classical measurements are revision
`aaabcf1520121b4acaa793811c8567dddcf39f1f`. Both were measured 2026-07-29
on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU 0. The public
artifact records `git_dirty = true` because that measured runtime patch was
pending over its stated base; the classical/lattice artifact is clean. The
FLINT, PARI/GP, NTL, and Isabelle measurements are the already-current
2026-07-28 exports from the same host, corpus, CPU placement, and timing
protocol. They were not rerun because this change only modifies Hex.

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
| Hex public factor | 373 | 19 | 424.039 µs | 5.577 ms | 8.986 s | 17.196 µs |
| Hex lattice | 369 | 23 | 1.957 ms | 91.186 ms | 10.000 s | 19.118 µs |
| Hex classical, no decline | 372 | 20 | 423.939 µs | 9.029 ms | 3.845 s | 18.527 µs |
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
to 424.039 µs and retained two additional solves, `sd5_x_phi45` and `sd6`.
The current no-decline classical entry now also solves `sd5_x_phi45`, leaving
`sd6` as the public dispatcher's one additional frontier success.

On 238 common rows for which both current Hex measurements are at least 10×
their own protocol overhead, public/classical has median 0.996× and
p10–p90 0.49×–1.08×. Public is faster on 126 and classical on 112. The
production dispatcher is therefore tied with the isolated classical route in
the middle while its bounded classical tier and fallbacks substantially
improve the hard tail and add the `sd6` solve. The preceding 1.5% classical
lead was real but small dispatch overhead before the production lifting work,
not evidence of a fundamentally faster classical algorithm.

The improvement is broad but not universal. Family medians below compare the
fresh public service with the preceding Hex public record; values below 1 are
faster.

| Family | Common rows | Median new/old | Rows slower |
|---|---:|---:|---:|
| Certificate boundary | 1 | 0.373× | 0 |
| Chebyshev | 28 | 0.307× | 2 |
| Conway | 186 | 0.326× | 2 |
| Cyclotomic | 32 | 0.641× | 1 |
| Cyclotomic products | 19 | 0.634× | 0 |
| Laguerre | 20 | 0.254× | 0 |
| Legendre | 20 | 0.242× | 0 |
| Random products | 30 | 0.263× | 0 |
| Signed-digit products | 9 | 0.455× | 0 |
| Swinnerton-Dyer | 11 | 0.264× | 0 |
| Wilkinson | 15 | 0.920× | 5 |

Every family median now improves over the pre-hot-path record. Wilkinson,
previously the lone slower family, is 0.920×; `wilkinson_56` remains 1.26×
slower than its pre-policy value but is 0.97× relative to the immediately
preceding public export.

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

- `reports/bench-results/hexbz-factor-sweep-hex-b4b36754-exact-factor-only-chungus2.json`
  (public factor; SHA-256
  `090b594a14b12af8332fef091d2bd8ca5652c3e7566e6bd452a984eb473a058a`)
- `reports/bench-results/hexbz-factor-sweep-hex-b4b36754-exact-only-chungus2.json`
  (same-day factor-only A/B reference; SHA-256
  `4ceadcbb1dd54f7e49d77efdd3ed199cb84633fb54c733a6041afa2118ddf9b2`)
- `reports/bench-results/hexbz-factor-sweep-hex-aaabcf15-chungus2.json`
  (lattice and no-decline classical; SHA-256
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
