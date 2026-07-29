# HexBerlekamp Performance Report

Current at revision `f1ab9696cee5fac0cb8ea17bfdfd19caf63bd7c3`,
measured 2026-07-29 on `chungus2` (AMD EPYC 9455, Linux x86-64), pinned to
CPU 0.

## Verdicts

| Target | Largest rung | Median | β | Verdict |
|---|---:|---:|---:|---|
| Berlekamp matrix | 192 | 10.785 ms | -0.067 | consistent |
| Rabin irreducibility | 64 | 45.082 ms | -0.105 | consistent |
| Berlekamp factorization | 256 | 3.493 ms | -0.240 | consistent |
| Distinct-degree factorization | 96 | 190.362 ms | -0.275 | consistent |

Raw export:
`reports/bench-results/hex-berlekamp-f1ab9696-gcd-hensel-chungus2.json`
(SHA-256
`f26d75d214e6d107ee3e374891efcdc53faa7bad8e87bc71facce6867ab8fd18`).
`list` and `verify` passed.

The JSON records a clean worktree. Matrix, Rabin, and DDF remain within 3.4% of
the preceding record. The degree-256 full-factor rung is 6.8% slower in this
sample even though its hot witness-split GCD now uses the cached worker; the
392-row integer corpus nevertheless improves broadly, so this isolated rung is
retained as an explicit downside rather than attributed as an end-to-end gain.

## External Comparator Status

The persistent python-flint 0.9.0 Rabin and DDF exports remain current records
of the external service, but their paired Hex measurements are from revision
`5c371a5a`. They continue to show a large FLINT advantage—hundreds of times at
the upper rungs—but are retained as historical paired measurements rather than
relabelled as exact current-Hex ratios:

- `hex-berlekamp-rabin-compare-5c371a5a-chungus2.json`
- `hex-berlekamp-ddf-compare-5c371a5a-chungus2.json`

## Profile

On the retained `a1fdbd81` split degree-24 diagnostic, rebuilding the kernel per basis vector took
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
