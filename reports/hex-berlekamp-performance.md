# HexBerlekamp Performance Report

Current at revision `a1fdbd81ef038faa41765fb39a79cd083109c8ed`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

## Verdicts

| Target | Largest rung | Median | β | Verdict |
|---|---:|---:|---:|---|
| Berlekamp matrix | 192 | 10.791 ms | -0.057 | consistent |
| Rabin irreducibility | 64 | 43.606 ms | -0.094 | consistent |
| Berlekamp factorization | 256 | 3.271 ms | -0.272 | consistent |
| Distinct-degree factorization | 96 | 187.058 ms | -0.270 | consistent |

Raw export:
`reports/bench-results/hex-berlekamp-a1fdbd81-chungus2.json` (SHA-256
`81ff7d318fb80c4c492848dfc9860f25c67a71f060813b2f73ad38d2ba6a71ed`).
`list` and `verify` passed.

The JSON records a dirty worktree because the borrowed-argument ownership fix
and refreshed evidence were pending commit; the full hash identifies the
implementation base. The current headline values differ by less than 2% from
the preceding record;
the large end-to-end gain is in Hensel lifting, normalization, and dispatcher
selection rather than this finite-field layer.

## External Comparator Status

The persistent python-flint 0.9.0 Rabin and DDF exports remain current records
of the external service, but their paired Hex measurements are from revision
`5c371a5a`. They continue to show a large FLINT advantage—hundreds of times at
the upper rungs—but are retained as historical paired measurements rather than
relabelled as exact `a1fdbd81` ratios:

- `hex-berlekamp-rabin-compare-5c371a5a-chungus2.json`
- `hex-berlekamp-ddf-compare-5c371a5a-chungus2.json`

## Profile

On the split degree-24 diagnostic, rebuilding the kernel per basis vector took
16.387 ms, sharing it took 1.245 ms, and the fixed path took 569.224 µs. The
fixed-path attribution was 18.89% matrix construction, 2.95% nullspace, and
78.17% witness splitting.

Raw stdout:
`reports/bench-results/berlekamp-diagnostic-a1fdbd81-chungus2.txt`
(SHA-256
`03e59491ed588ca377ece2ef387450ba699ef9e63d323db50e6c36fa17f265b5`).

## Concerns

- Rabin and DDF remain the largest finite-field gaps to FLINT.
- The profile is a targeted compiled diagnostic, not a sampling-profiler
  trace.
- The benchmark fixtures establish these ladders, not every polynomial
  distribution.
