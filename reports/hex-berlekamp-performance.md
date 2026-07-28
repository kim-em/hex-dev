# HexBerlekamp Performance Report

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0. See `polynomial-factorization-performance.md` for the
cross-library snapshot.

## Bench Targets

- `runBerlekampMatrixChecksum`: `n²`
- `runRabinTestChecksum`: `n³`
- `runBerlekampFactorChecksum`: `n²`
- `runDistinctDegreeChecksum`: `n³`

## Verdicts

Three independent outer trials were run for every rung.

| Target | Largest rung | Median | β | Verdict |
|---|---:|---:|---:|---|
| Berlekamp matrix | 192 | 10.776 ms | -0.061 | consistent |
| Rabin irreducibility | 64 | 44.256 ms | -0.105 | consistent |
| Berlekamp factorization | 256 | 3.388 ms | -0.262 | consistent |
| Distinct-degree factorization | 96 | 186.132 ms | -0.272 | consistent |

Raw export:
`reports/bench-results/hex-berlekamp-5c371a5a-chungus2.json`
(SHA-256
`70e05346f363596bceb5dbdd9838ef43ba499cfcd77b04e7161e18e437992bcc`).
`list` and `verify` passed.

## Comparator Ratios

python-flint 0.9.0 was run through the persistent driver. Every fixed target
used five repeats and a 0.2 s inner-repeat floor, so process startup is outside
the steady-state per-call medians.

| Comparator | Smallest matched rung | Lean / FLINT | Largest matched rung | Lean / FLINT |
|---|---:|---:|---:|---:|
| Rabin / `nmod_poly.is_irreducible` | 8 | 0.253 / 0.020 ms (`12.5x`) | 64 | 87.445 / 0.211 ms (`413.8x`) |
| DDF / `nmod_poly.factor_distinct_deg` | 12 | 1.487 / 0.036 ms (`41.1x`) | 96 | 380.479 / 0.533 ms (`714.5x`) |

The trend still diverges in FLINT's favour. Raw exports:

- `hex-berlekamp-rabin-compare-5c371a5a-chungus2.json`
- `hex-berlekamp-ddf-compare-5c371a5a-chungus2.json`

Both are under `reports/bench-results/`.

## Profile

The current compiled Berlekamp diagnostic was rerun with
`RELIFT_PROFILE=berlekamp`. On the split degree-24 fixture, rebuilding the
kernel per basis vector took 16.077 ms, sharing the kernel reduced the
baseline to 1.280 ms, and the fixed path took 577.347 µs. The fixed-path
attribution was 18.18% matrix construction, 2.84% nullspace, and 78.99%
witness splitting.

## Concerns

- Rabin and DDF remain hundreds of times slower than FLINT at the upper
  comparator rungs.
- The profile is a targeted compiled diagnostic, not a fresh sampling-profiler
  trace.
- The benchmark models fit these deterministic fixed-prime fixtures; they are
  not claims about every polynomial distribution.
