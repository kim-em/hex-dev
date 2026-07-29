# HexBerlekampZassenhaus Performance Report

Current Hex measurements are from revision
`a1fdbd81ef038faa41765fb39a79cd083109c8ed`, measured 2026-07-29 on
`chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU 0.

## Bench Targets

Eight parametric targets cover public factorization, the exhaustive backstop,
degree/height, fallback behaviour, and fast-path precision/local-factor axes.
Eight canonical adversarial fixtures are warm fixed benchmarks. All parametric
targets completed three outer trials; their classical BHKS upper-bound models
are loose on these small deterministic fixtures, so the verdicts are
inconclusive rather than failed.

| Target | Largest rung | Median |
|---|---:|---:|
| Public factorization | 24 | 2.261 ms |
| Fallback probe | 24 | 1.950 ms |
| Degree/height | `(6,32)` | 350.752 µs |
| Fast-path precision/local | `(8,32,128,8)` | 1.669 ms |
| Slow factorization | 4 | 12.564 µs |
| Slow degree/height | `(3,8)` | 30.827 µs |
| Public compare domain | 4 | 72.905 µs |
| Slow compare domain | 4 | 12.577 µs |

| Warm fixed fixture | Median | Min–max |
|---|---:|---:|
| `X⁴ + 1`, public | 30.569 µs | 30.462–30.810 µs |
| `X⁴ + 1`, fast setup | 20.751 µs | 20.487–20.800 µs |
| `(X²-2)(X²-3)`, public | 28.735 µs | 28.577–28.868 µs |
| `Phi_15`, public | 90.301 µs | 89.934–90.999 µs |
| `Phi_15`, fast setup | 25.862 µs | 25.718–25.967 µs |
| `SD_3`, modular split | 8.420 µs | 8.243–8.568 µs |
| `SD_3`, lattice factorization | 1.613 ms | 1.605–1.615 ms |
| `SD_4`, lattice factorization | 29.580 ms | 29.303–29.911 ms |

The public `X⁴+1` fixed fixture falls from 98.628 µs to 30.569 µs and
`Phi_15` from 205.705 µs to 90.301 µs. Quadratic multifactor Hensel lifting,
reported separately, is the largest lower-layer improvement.

Exports:

- `reports/bench-results/hex-berlekamp-zassenhaus-parametric-a1fdbd81-chungus2.json`
  (SHA-256
  `6e1c8e966b178f2ebadfbeec1a5283ab044fa0125f99ed9a9a2326b133da79ee`)
- `reports/bench-results/hex-berlekamp-zassenhaus-fixed-a1fdbd81-chungus2.json`
  (SHA-256
  `49acf7761bc6df09e1192761989f85f3f8acb21733de85d8d01383152951141f`)

`list` and every non-scheduled `verify` target passed.

The JSON exports record a dirty worktree because the borrowed-argument fix and
these refreshed reports were not yet committed. The full hash identifies the
implementation base; the only uncommitted runtime change adds the required
borrow annotations to its native externs. After that fix the quadratic target
stays at 65–69 MiB RSS across repetitions, whereas the rejected run grew
without bound.

## Cross-System Frontier

| System | OK | Timeout | Solved-row median |
|---|---:|---:|---:|
| Hex public factor | 373 | 19 | 460.392 µs |
| Hex lattice | 366 | 26 | 1.864 ms |
| Hex classical, no decline | 371 | 21 | 424.409 µs |
| FLINT 0.9.0 | 391 | 1 | 66.850 µs |
| PARI/GP 2.17.3 | 391 | 1 | 99.958 µs |
| NTL 11.6.0 | 391 | 1 | 135.631 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms |

The external rows are the unchanged current 2026-07-28 measurements from the
same host, corpus, CPU, and protocol. On 234 common rows above the 10× protocol
overhead threshold, public Hex / verified Isabelle BZ has median 1.09× and
p10–p90 0.48×–3.60×; Hex wins 108 rows and Isabelle 126. This is near parity,
not an overall Hex win. The old eligible-row median was 3.95×.

Public and classical now have a 1.008× eligible-row median ratio. Public wins
105 rows, classical 132, and public additionally solves `sd5_x_phi45` and
`sd6`. The dispatcher overhead is therefore almost neutral on the common
corpus while its fallback adds two genuine frontier successes.

## Diagnostics

- Split degree 24: 16.387 ms rebuilding the kernel, 1.245 ms sharing it,
  569.224 µs on the fixed path.
- Fixed split-degree-24 attribution: 18.89% matrix, 2.95% nullspace,
  78.17% witness splitting.
- Hybrid `SD_5`: 96.895 ms through the classical tier.
- Hybrid `SD_6`: 9.087 s, lattice decline, irreducible fallback.
- Lattice core `SD_6`: 8.492 s.

Balanced product construction remains neutral at degree 24: 6.557 ms
sequential versus 6.541 ms balanced on the Mignotte schedule.

Raw diagnostic artifacts:

- `berlekamp-diagnostic-a1fdbd81-chungus2.txt` (SHA-256
  `76f28eb9e779f4672a3138c8167de2d6849b28a899609bff19227a378151af52`)
- `bz-spikes-a1fdbd81-chungus2.txt` (SHA-256
  `cd0cd2c0ecc5c6a3fc6bdd2b08a5f4b114403aa7510fab75048fba4db9c17477`)

Both paths are relative to `reports/bench-results/`.

### Swinnerton-Dyer seam

| Fixture | Hex public | Verified Isabelle BZ | Hex / Isabelle |
|---|---:|---:|---:|
| `SD_5` | 103.643 ms | 22.827 ms | 4.54x |
| `SD_5` shifted by 1 | 89.829 ms | 14.875 ms | 6.04x |
| `SD_5` shifted by 2 | 90.684 ms | 14.907 ms | 6.08x |
| `SD_6` | 9.163 s | timeout | — |

The fresh public service now solves `SD_6`; the no-decline classical service
still times out. The public result and the isolated lattice result (8.187 s)
show that the dispatcher is adding useful reach here. The public measurement
is a single cutoff-limited shot only 8.4% below ten seconds, so this frontier
success has a narrow margin.

## Concerns

- Nineteen public corpus cases still hit the 10-second cutoff.
- FLINT, PARI/GP, and NTL remain much faster in aggregate.
- Isabelle BZ still wins more eligible common rows than Hex despite the near-
  parity median.
- The lattice route has a much heavier tail than the classical route.
- Wilkinson-family rows regress by a 1.221× median against the preceding Hex
  record under the shorter relift-probe policy.
- The BHKS registrations are useful upper bounds but do not describe the
  observed small-fixture scaling.
