# HexBerlekampZassenhaus Performance Report

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0.

## Bench Targets

Eight parametric targets cover public factorization, the exhaustive backstop,
degree/height, fallback behaviour, and fast-path precision/local-factor axes.
Eight canonical adversarial fixtures are fixed benchmarks.

The canonical cases were changed from one-point parametric registrations to
fixed IO registrations during this refresh. The old shape admitted
constant-folded nanosecond results and could never yield a scaling verdict.

## Verdicts

All parametric targets completed three independent outer trials. Their
classical BHKS upper-bound models are too loose for these small deterministic
fixtures, so the current verdicts are inconclusive rather than failed.

| Target | Largest rung | Median |
|---|---:|---:|
| Public factorization | 24 | 2.254 ms |
| Fallback probe | 24 | 3.042 ms |
| Degree/height | `(6,32)` | 527.560 µs |
| Fast-path precision/local | `(8,32,128,8)` | 3.284 ms |
| Slow factorization | 4 | 14.116 µs |
| Slow degree/height | `(3,8)` | 62.709 µs |
| Public compare domain | 4 | 140.490 µs |
| Slow compare domain | 4 | 26.528 µs |

| Fixed fixture | Median | Min–max |
|---|---:|---:|
| `X⁴ + 1`, public | 98.628 µs | 97.007–99.922 µs |
| `X⁴ + 1`, fast setup | 18.227 µs | 18.040–18.350 µs |
| `(X²-2)(X²-3)`, public | 27.154 µs | 27.086–27.546 µs |
| `Phi_15`, public | 205.705 µs | 201.817–326.834 µs |
| `Phi_15`, fast setup | 18.315 µs | 18.076–18.758 µs |
| `SD_3`, modular split | 8.122 µs | 7.840–8.545 µs |
| `SD_3`, lattice factorization | 2.596 ms | 2.569–2.617 ms |
| `SD_4`, lattice factorization | 34.266 ms | 34.025–37.491 ms |

Exports:

- `reports/bench-results/hex-berlekamp-zassenhaus-parametric-5c371a5a-chungus2.json`
- `reports/bench-results/hex-berlekamp-zassenhaus-fixed-5c371a5a-chungus2.json`

`list` and all 16 non-scheduled `verify` targets passed.

## Comparator Ratios

The current 392-row, 10-second corpus frontier is:

| System | OK | Timeout | Solved-row median |
|---|---:|---:|---:|
| Hex public factor | 371 | 21 | 1.244 ms |
| Hex lattice | 365 | 27 | 2.258 ms |
| Hex classical, no decline | 371 | 21 | 1.008 ms |
| FLINT 0.9.0 | 391 | 1 | 66.850 µs |
| PARI/GP 2.17.3 | 391 | 1 | 99.958 µs |
| NTL 11.6.0 | 391 | 1 | 135.631 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms |

Every current factor-degree check against the corpus oracle passed. See
`hexbz-factor-sweep.md` and the six current sweep exports for percentile,
frontier, and provenance details.

The external toolchains were provided by transient Nix environments. Setup and
AFP export builds were completed before timing; the sweep uses persistent
line-protocol services and records roughly 11–24 µs of protocol overhead.
On 369 common solved rows, public Hex has a median `2.73x` wall-clock ratio
against verified Isabelle BZ. That corpus-conditioned result supersedes the
retired startup-contaminated ratios; see `bz-vs-isabelle-investigation.md`.

## Profile

Current compiled diagnostics:

- Split degree 24: 16.077 ms rebuilding the kernel, 1.280 ms sharing it,
  577.347 µs on the fixed path.
- Fixed split-degree-24 attribution: 18.18% matrix, 2.84% nullspace,
  78.99% witness splitting.
- Hybrid `SD_5`: 134.197 ms through the classical tier.
- Hybrid `SD_6`: 9.858 s, lattice decline, irreducible fallback.
- Lattice core `SD_6`: 9.158 s.

The classical product spike showed no material balanced-product win at degree
24: 8.834 ms sequential versus 8.807 ms balanced on the Mignotte schedule.

## Concerns

- Twenty-one corpus cases still hit the public 10-second cutoff.
- The lattice route solves fewer corpus rows and has a much heavier tail than
  the classical/public routes.
- The registered BHKS models are useful upper bounds but do not describe the
  observed small-fixture scaling.
- The public/Isabelle-BZ common-row median is above the SPEC's aspirational
  `1x` comparator goal, though the corpus frontier is not the SPEC's
  largest-eligible-rung gate.
