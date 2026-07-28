# HexBerlekampZassenhaus Performance Report

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0.

The exports record `5c371a5-dirty` because the benchmark registrations and
reports were being repaired in the same worktree; the measured library revision
is the full hash above.

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

| Warm auto-tuned fixed fixture | Median | Min–max |
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
line-protocol services and records roughly 11–24 µs of protocol overhead. The
corpus table reports service wall clock without subtracting that overhead;
FLINT's and PARI's low solved-row medians therefore include approximately 29%
and 24% protocol cost.

For ratios, a row is eligible only when both medians are at least ten times the
larger measured overhead of the pair. On 247 eligible common solved rows,
public Hex has a median `3.95x` wall-clock ratio against verified Isabelle BZ
(p10–p90 `0.64x–12.76x`). There are 369 common solved rows before that signal
filter. See `bz-vs-isabelle-investigation.md`.

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

Raw diagnostic stdout is preserved in
`reports/bench-results/berlekamp-diagnostic-5c371a5a-chungus2.txt`
(SHA-256
`c79c0167c402c714fbd664e3157236fc5aa1f426a67f83b9f1250a5e5135c364`)
and `reports/bench-results/bz-spikes-5c371a5a-chungus2.txt` (SHA-256
`fe2c873c73ba29bb7f5193aac976691483505880803cdc0429cb09f1d7b21f1b`).

### Swinnerton-Dyer seam

| Fixture | Hex public | Verified Isabelle BZ | Hex / Isabelle |
|---|---:|---:|---:|
| `SD_5` | 121.164 ms | 22.827 ms | `5.31x` |
| `SD_5` shifted by 1 | 182.981 ms | 14.875 ms | `12.30x` |
| `SD_5` shifted by 2 | 183.930 ms | 14.907 ms | `12.34x` |
| `SD_6` | timeout | timeout | — |

The isolated `hex-lattice` service solves `SD_6` in 8.855 s, while the public
service times out at 10 s. The single-shot hybrid spike takes 9.858 s before
declining, so this is a marginal threshold seam rather than evidence of a
large isolated-lattice regression.

## Concerns

- Twenty-one corpus cases still hit the public 10-second cutoff.
- The lattice route solves fewer corpus rows and has a much heavier tail than
  the classical/public routes.
- Public `SD_6` times out even though the isolated lattice entry point solves it
  in 8.855 s; the dispatcher seam consumes the remaining cutoff budget.
- The registered BHKS models are useful upper bounds but do not describe the
  observed small-fixture scaling.
- The public/Isabelle-BZ eligible-row median is above the SPEC's aspirational
  `1x` comparator goal, though the corpus frontier is not the SPEC's
  largest-eligible-rung gate.
