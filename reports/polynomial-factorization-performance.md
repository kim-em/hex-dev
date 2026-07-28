# Polynomial Factorization Performance

This is the current performance snapshot for the polynomial-factorization
stack. It supersedes the previously current claims in the individual headline
reports.

## Measurement environment

- Revision: `5c371a5abb85ca6ef6510ec60888f3048db71719`
- Date: 2026-07-28
- Host: `chungus2`, AMD EPYC 9455, 48 physical cores / 96 CPUs, Linux x86-64
- Lean: `leanprover/lean4:v4.32.0-rc1`
- External libraries: python-flint 0.9.0; PARI/GP 2.17.3 through
  cypari2 2.2.4; NTL 11.6.0; Isabelle2025-2 with AFP 2026-05-29;
  GHC 9.10.3
- External toolchains: transient nixpkgs environments; setup and AFP export
  builds are excluded from the timed service calls
- CPU placement: every timing command was pinned with `taskset -c 0`
- Parametric method: three independent outer trials; reported values are
  per-rung medians
- Fixed method: five repeats with a 0.2 s inner-repeat floor
- Corpus method: 10 s per-call cutoff, median of five when the first call was
  below one second, otherwise one call; no family was terminated early

The benchmark exports say `5c371a5-dirty` because this refresh changes the
benchmark registrations and reports in the same worktree. The measured library
revision is the full hash above.

## Headline results

### Finite-field factorization

| Target | Declared model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Berlekamp matrix | `n²` | 192 | 10.776 ms | consistent |
| Rabin irreducibility | `n³` | 64 | 44.256 ms | consistent |
| Berlekamp factorization | `n²` | 256 | 3.388 ms | consistent |
| Distinct-degree factorization | `n³` | 96 | 186.132 ms | consistent |

At the largest matched comparator rungs, Rabin took 87.445 ms in Lean
versus 0.211 ms in FLINT (`413.8x` Lean/FLINT), and distinct-degree
factorization took 380.479 ms versus 0.533 ms (`714.5x` Lean/FLINT).
These fixed-rung values differ from the parametric headline because the fixed
fixtures and timing wrappers are deliberately paired with FLINT.

### Finite-field polynomial substrate

| Target | Declared model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Frobenius `X` mod | `n³` | 80 | 295.793 ms | inconclusive |
| GCD | `n²` | 256 | 44.938 µs | inconclusive; observed faster |
| Weighted product | `n²` | 4096 | 664.360 ms | consistent |
| Square-free decomposition | `n²` | 768 | 6.638 ms | consistent |
| Frobenius power mod | `n³` | 64 | 338.979 ms | consistent |
| Power mod monic | `n² log n` | 512 | 149.547 ms | consistent |
| Division mod | `n²` | 256 | 975.082 µs | consistent |
| Modular composition | `n³` | 192 | 368.882 ms | consistent |

### Hensel lifting

| Target | Declared model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Reduce mod `p` | `n` | 131072 | 10.073 ms | consistent |
| Lift to `Z` | `n` | 131072 | 2.661 ms | consistent |
| Reduce mod `p^k` | `n` | 131072 | 10.431 ms | consistent |
| Linear Hensel step | `n²` | 512 | 15.077 ms | consistent |
| Iterated linear lift | `n²k` | `(192,64)` | 145.228 ms | inconclusive |
| Quadratic Hensel step | `n²` | 512 | 128.731 ms | consistent |
| Polynomial product | `n²` | 1024 | 159.670 ms | consistent |
| Linear multifactor lift | `n²k` | `(192,64)` | 141.179 ms | inconclusive |
| Quadratic multifactor lift | `n² log k` | `(192,64)` | 145.140 ms | consistent |

The persistent python-flint driver is no longer dominated by process startup.
At `n=512`, a single linear step was 27.256 ms in Hex and 11.445 ms in
FLINT (`0.42x` FLINT/Hex); a quadratic step was 225.867 ms versus
5.168 ms (`0.02x`). The iterated comparator is an `fmpz_poly` emulation
because python-flint does not bind the native `nmod_poly_hensel_lift_*`
entry points. At `(n=256,k=8)` that emulation was slower than Hex:
1.067 s versus 53.016 ms for the iterated linear surface, 695.342 ms
versus 28.382 ms for linear multifactor lifting, and 648.198 ms versus
80.566 ms for quadratic multifactor lifting. Those ratios describe the
emulation, not native FLINT Hensel performance.

### Integer factorization

The eight scaling ladders all complete, but their current classical BHKS
upper-bound models are too loose for the measured fixtures, so their verdicts
are inconclusive rather than failed.

| Target | Largest rung | Median |
|---|---:|---:|
| Public factorization | 24 | 2.254 ms |
| Fallback probe | 24 | 3.042 ms |
| Degree/height | `(6,32)` | 527.560 µs |
| Fast-path precision/local factors | `(8,32,128,8)` | 3.284 ms |
| Slow factorization | 4 | 14.116 µs |
| Slow degree/height | `(3,8)` | 62.709 µs |
| Public compare domain | 4 | 140.490 µs |
| Slow compare domain | 4 | 26.528 µs |

Canonical fixtures are fixed benchmarks, not singleton scaling ladders:

| Fixture / operation | Median | Min–max |
|---|---:|---:|
| `X⁴ + 1`, public factorization | 98.628 µs | 97.007–99.922 µs |
| `X⁴ + 1`, fast setup | 18.227 µs | 18.040–18.350 µs |
| `(X²-2)(X²-3)`, public factorization | 27.154 µs | 27.086–27.546 µs |
| `Phi_15`, public factorization | 205.705 µs | 201.817–326.834 µs |
| `Phi_15`, fast setup | 18.315 µs | 18.076–18.758 µs |
| `SD_3`, modular split | 8.122 µs | 7.840–8.545 µs |
| `SD_3`, lattice factorization | 2.596 ms | 2.569–2.617 ms |
| `SD_4`, lattice factorization | 34.266 ms | 34.025–37.491 ms |

The registration shape matters: the previous one-point parametric form could
be constant-folded to nanoseconds and could not produce a scaling verdict.
The current fixed registrations call opaque IO wrappers and passed `verify`.

## Corpus frontier

The committed corpus now contains 392 instances with SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.

| System | OK | Timeout | Median of solved rows | 90th percentile | Slowest solved |
|---|---:|---:|---:|---:|---:|
| Hex public factor | 371 | 21 | 1.244 ms | 24.831 ms | 5.016 s |
| Hex lattice | 365 | 27 | 2.258 ms | 99.293 ms | 9.540 s |
| Hex classical, no decline | 371 | 21 | 1.008 ms | 12.708 ms | 4.032 s |
| FLINT | 391 | 1 | 66.850 µs | 1.184 ms | 1.228 s |
| PARI/GP | 391 | 1 | 99.958 µs | 1.254 ms | 823.201 ms |
| NTL | 391 | 1 | 135.631 µs | 2.714 ms | 1.919 s |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms | 1.219 s | 9.528 s |

Every current factor-degree check against the corpus oracle passed. The seven
Hoeij-Zimmermann rows without a committed degree oracle retain their earlier
combined cross-system agreement; in the current records, FLINT, PARI/GP, and
NTL also agree on their factor counts.

On the 369 rows solved by both Hex public factorization and verified Isabelle
BZ, the per-row `Hex/Isabelle` ratio has median `2.73x` (10th–90th percentile
`0.55x–11.81x`); Hex is faster on 95 rows and Isabelle on 274. This is a
common-solved-row comparison, not a claim about rows where either system hit
the cutoff. See `bz-vs-isabelle-investigation.md` for the corresponding
lattice/verified-LLL comparison and caveats.

## Kernel and tactic sample

Fresh-module import baselines were 1.212 s for the Mathlib-free factorization
entry points and 4.624 s for the certificate umbrella.

| Case | Direct kernel factorization | `factor_poly` | `irreducibility` |
|---|---:|---:|---:|
| `quartic_a4` | 2.347 s | 4.912 s | 4.513 s |
| `cyclo_phi5` | 1.422 s | 3.712 s | 3.690 s |
| `xpow6_minus1` | 2.342 s | 3.654 s | not applicable |
| `sd2` | 1.929 s | provider decline | provider decline |

These are end-to-end fresh Lake module times, not kernel-only timings. The
signed baseline deltas are in the raw artifact. The multi-prime
`quartic_a4` replay completed for both linear and incremental Rabin checkers;
the incremental checker was faster on the two degree-two cases.

## Current diagnostic profiles

The compiled Berlekamp diagnostic shows that rebuilding the kernel per basis
vector remains the avoidable cost on split families. At degree 24, the
rebuilding baseline was 16.077 ms, the shared-kernel baseline was 1.280 ms,
and the fixed shared-kernel path was 577.347 µs. The fixed-path attribution
was 18.18% matrix construction, 2.84% nullspace, and 78.99% witness splitting.
Caching reduced witnesses gave essentially no benefit on the split degree-24
case (465.380 versus 465.231 µs) and only a modest benefit on `SD_4`
(262.950 versus 237.623 µs).

The classical product spike found no meaningful advantage from balanced
product construction on its current fixtures. At degree 24, sequential and
balanced Mignotte schedules were 8.834 ms and 8.807 ms; at the fixed
`k=4` schedule they were 2.840 ms and 2.818 ms.

The hybrid seam completed `SD_5` in 134.197 ms through the classical tier.
`SD_6` took 9.858 s, reached the lattice tier, declined, and returned the
irreducible fallback. The lattice core itself took 9.158 s on `SD_6`.

## Artifacts

Current machine-readable exports:

- `hex-berlekamp-5c371a5a-chungus2.json`
- `hex-berlekamp-rabin-compare-5c371a5a-chungus2.json`
- `hex-berlekamp-ddf-compare-5c371a5a-chungus2.json`
- `hex-poly-fp-5c371a5a-chungus2.json`
- `hex-hensel-5c371a5a-chungus2.json`
- five `hex-hensel-*-flint-5c371a5a-chungus2.json` comparator exports
- `hex-berlekamp-zassenhaus-parametric-5c371a5a-chungus2.json`
- `hex-berlekamp-zassenhaus-fixed-5c371a5a-chungus2.json`
- `hexbz-factor-sweep-hex-5c371a5a-chungus2.json`
- `hexbz-factor-sweep-flint-5c371a5a-chungus2.json`
- `hexbz-factor-sweep-pari-5c371a5a-chungus2.json`
- `hexbz-factor-sweep-ntl-5c371a5a-chungus2.json`
- `hexbz-factor-sweep-isabelle-bz-5c371a5a-chungus2.json`
- `hexbz-factor-sweep-isabelle-lll-5c371a5a-chungus2.json`
- `hexbz-kernel-factor-5c371a5a-chungus2.json`

All paths are relative to `reports/bench-results/`. Commit-named exports from
older revisions are retained for historical comparisons, but only the files
listed above support this current snapshot.
