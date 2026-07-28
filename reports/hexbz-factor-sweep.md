# HexBZ Cross-System Factorization Sweep

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0.

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
- Cross-check: factor-degree multisets for every pair of answering systems

## Recorded Sweep

| System | OK | Timeout | p50 solved | p90 solved | Slowest solved | Protocol overhead |
|---|---:|---:|---:|---:|---:|---:|
| Hex public factor | 371 | 21 | 1.244 ms | 24.831 ms | 5.016 s | 15.373 µs |
| Hex lattice | 365 | 27 | 2.258 ms | 99.293 ms | 9.540 s | 19.569 µs |
| Hex classical, no decline | 371 | 21 | 1.008 ms | 12.708 ms | 4.032 s | 19.219 µs |
| FLINT | 391 | 1 | 66.850 µs | 1.184 ms | 1.228 s | 19.219 µs |
| PARI/GP | 391 | 1 | 99.958 µs | 1.254 ms | 823.201 ms | 23.755 µs |
| NTL | 391 | 1 | 135.631 µs | 2.714 ms | 1.919 s | 11.487 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs | 5.128 ms | 8.363 s | 17.777 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms | 1.219 s | 9.528 s | 17.136 µs |

Every returned factor-degree multiset with a committed corpus oracle matched
it. The seven Hoeij-Zimmermann rows without a committed degree oracle retain
their previous combined cross-system agreement; current FLINT, PARI/GP, and
NTL factor counts also agree on all seven.

Compared with the previous 391-row record, the public and classical paths move
from 366 solved rows to 371 of 392; the lattice path moves from 363 to 365;
verified Isabelle BZ moves from 370 to 371; and verified Isabelle LLL moves
from 309 to 314. PARI/GP and NTL now both solve 391 rows, with `hoeij_S9` the
only timeout. Because the corpus gained one row and the host changed, exact
timeout sets and per-row JSON should be preferred to raw percentage or
cross-host timing comparisons.

Current exports:

- `reports/bench-results/hexbz-factor-sweep-hex-5c371a5a-chungus2.json`
  (SHA-256
  `f3bef5656aae3eebf8ac3ab64bf970c65c0f3a086ceddd25044024df45f838bd`)
- `reports/bench-results/hexbz-factor-sweep-flint-5c371a5a-chungus2.json`
  (SHA-256
  `f656372a18c85fe5fd35dd415033842de95348f718e89031213bb310fdc88da5`)
- `reports/bench-results/hexbz-factor-sweep-pari-5c371a5a-chungus2.json`
  (SHA-256
  `fdd253e8944a90f7cdf112a7e36f9d28ec9a481f4c142122ddda47cbd3216ed9`)
- `reports/bench-results/hexbz-factor-sweep-ntl-5c371a5a-chungus2.json`
  (SHA-256
  `65db4a80bac19ac390e0e495c56bfa7d0a899a240fe71d61a4de60b2796442ed`)
- `reports/bench-results/hexbz-factor-sweep-isabelle-bz-5c371a5a-chungus2.json`
  (SHA-256
  `da44a233d02f8a321ad50878180366df9f5cacb91e9f657ed8138046f7a21e3f`)
- `reports/bench-results/hexbz-factor-sweep-isabelle-lll-5c371a5a-chungus2.json`
  (SHA-256
  `512d59e13be1737a71c2f06a93bcdfab4729f0afdfea3452d89f1393dfda2789`)

## Reproducing

```sh
lake build hexbz_factor_service
taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor,hex-lattice,hex-classical-nodecline \
  --cutoff 10 --no-early-terminate \
  --output reports/bench-results/hexbz-factor-sweep-hex-5c371a5a-chungus2.json
taskset -c 0 uv run --with python-flint \
  python3 scripts/bench/factor_sweep.py \
  --systems flint --cutoff 10 --no-early-terminate \
  --output reports/bench-results/hexbz-factor-sweep-flint-5c371a5a-chungus2.json
taskset -c 0 nix-shell \
  -p 'python3.withPackages (ps: [ ps.cypari2 ps.cysignals ])' \
  --run "python3 scripts/bench/factor_sweep.py \
    --systems pari --cutoff 10 --no-early-terminate \
    --output reports/bench-results/hexbz-factor-sweep-pari-5c371a5a-chungus2.json"
taskset -c 0 nix-shell -p ntl gmp pkg-config gcc \
  --run "python3 scripts/bench/factor_sweep.py \
    --systems ntl --cutoff 10 --no-early-terminate \
    --output reports/bench-results/hexbz-factor-sweep-ntl-5c371a5a-chungus2.json"
nix-shell -p isabelle ghc curl coreutils gnutar gzip \
  --run "bash scripts/oracle/setup_bz_isabelle.sh"
taskset -c 0 nix-shell -p isabelle ghc curl coreutils gnutar gzip \
  --run "python3 scripts/bench/factor_sweep.py \
    --systems isabelle-bz --cutoff 10 --no-early-terminate \
    --output reports/bench-results/hexbz-factor-sweep-isabelle-bz-5c371a5a-chungus2.json"
nix-shell -p isabelle ghc curl coreutils gnutar gzip \
  --run "bash scripts/oracle/setup_bz_lll_isabelle.sh"
taskset -c 0 nix-shell -p isabelle ghc curl coreutils gnutar gzip \
  --run "python3 scripts/bench/factor_sweep.py \
    --systems isabelle-lll --cutoff 10 --no-early-terminate \
    --output reports/bench-results/hexbz-factor-sweep-isabelle-lll-5c371a5a-chungus2.json"
```

Commit-named older sweep exports remain historical records. They are not
merged into the current 392-row summary because their corpus hash differs.
