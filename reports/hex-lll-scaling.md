# HexLLL Scaling Report

This report fits the asymptotic scaling of the HexLLL comparators — the six
curves of each comparator plot
(`reports/hex-lll-performance.md`) — so that the *exponent* (which complexity
class a method is in) and the *constant factor* (how much slower it is than the
fastest at the same complexity) are recorded as numbers rather than read off a
log axis by eye. Regenerate it whenever the implementation changes; the
procedure below is exact and the script reuses the committed bench data the
plot is built from.

## Model

Each comparator's median wall time is modelled as a power law in the dimension
`n`,

```
t(n) = C · n^p
```

so on a log-log axis the curve is a straight line of slope `p`. Two methods
with the *same* `p` are parallel there and differ only by the ratio of their
`C`; two methods with *different* `p` fan out, and no single constant describes
their gap — only the observed ratio at a stated `n`, which then grows with `n`.

`scripts/plots/hex-lll-scaling.py` fits `p` by ordinary least squares on
`(log n, log t)` over an asymptotic window of top rungs, and reports:

- **exponent `p`** and the fit **R²** per method;
- when the family's exponents agree (spread `≤ 0.5`), a **cubic-pinned constant
  `C₃`** — the geometric mean of `t(n) / n³` over the window, in nanoseconds —
  and its ratio to the fastest method. `C₃` is scale-invariant exactly when
  `p ≈ 3`, so it is only emitted for families that share that exponent;
- when the exponents disagree, the **median at the top rung** and the observed
  **ratio to the fastest there** instead, with a note that the ratio grows
  with `n`.

The asymptotic window matters: the small-`n` rungs carry fixed per-call
overhead (subprocess fork for the Isabelle oracles, GHC start-up, the
certificate checker's constant term) that bends the fit below the true
exponent. The defaults are the top rungs of each ladder — random-bounded
`120–180`, harsh-cubic `40–55` — chosen so the fit sees the asymptote, not the
warm-up. Both windows fit with R² ≥ 0.997.

## Results

Snapshot below; regenerate with the command in [§Reproduction](#reproduction)
and replace this block when the numbers move. Each row's data provenance (host,
commit) is printed above its table.

The comparator carries six curves. **Lean native** is the exact `d`/`ν`
reducer (`lllNative`); **Lean steered** is the default native path, the
approximation-steered reducer that drives exact integer row operations from an
untrusted floating-point Gram–Schmidt and certifies its output at `(δ, 11/20)`.

### random-bounded, rungs 120–180

- `reports/bench-results/hex-lll-certified-c3d2fecb.json` — host `carica`, commit `c3d2fecb`
- `reports/bench-results/hex-lll-certified-carica.json` — host `carica`, commit `c3d2fecb`
- `reports/bench-results/hex-lll-random-bounded-steered-ac0d2dcc.json` — host `carica`, commit `ac0d2dcc`

| method | exponent p | R² | median @ n=180 | × fastest @ n=180 |
|---|---:|---:|---:|---:|
| Isabelle native | 3.37 | 0.9996 | 7548.6 ms | 28.1× |
| Lean native | 3.02 | 0.9991 | 4540.9 ms | 16.9× |
| Isabelle certified | 3.01 | 0.9995 | 2364.6 ms | 8.8× |
| Lean steered | 3.58 | 0.9997 | 1901.7 ms | 7.1× |
| Lean certified | 3.08 | 0.9988 | 954.4 ms | 3.6× |
| fpLLL via fplll-ffi | 3.09 | 1.0000 | 268.2 ms | 1.0× |

The six exponents span 0.57, so the methods no longer share one complexity on
this family and the table reports the observed ratio at `n = 180`. The headline
reading:

- **The steered default runs 2.4× faster than the exact reducer** (1901.7 vs
  4540.9 ms at `n = 180`), even though its fitted exponent (`p ≈ 3.58`) is
  slightly *steeper* than exact native's `p ≈ 3.02`: steering at the stricter
  `δ` it forwards to the certifier fires more swaps, and the per-swap
  floating-point work plus the periodic exact-Gram refresh grow with `n`. The
  win here is constant-factor (no Θ(n⁴)-bit Gram-determinant state), not a
  complexity-class change — random-bounded was already `~n³` for the exact
  reducer.
- **Certifying an fpLLL candidate still beats steering** (954.4 vs 1901.7 ms):
  the steered path reduces the basis itself, while the certified path only
  checks fpLLL's, so it stays the fastest verified option where an external
  provider is present.
- **Lean steered beats the Isabelle native extraction by ~4×** (1901.7 vs
  7548.6 ms), and Lean certified beats it by ~8×.

### harsh-cubic, rungs 40–55

- `reports/bench-results/hex-lll-certified-c3d2fecb.json` — host `carica`, commit `c3d2fecb`
- `reports/bench-results/hex-lll-certified-carica.json` — host `carica`, commit `c3d2fecb`
- `reports/bench-results/hex-lll-harsh-cubic-steered-ac0d2dcc.json` — host `carica`, commit `ac0d2dcc`

| method | exponent p | R² | median @ n=55 | × fastest @ n=55 |
|---|---:|---:|---:|---:|
| Isabelle native | 5.76 | 0.9997 | 356.0 ms | 48.4× |
| Lean native | 5.56 | 0.9998 | 235.7 ms | 32.0× |
| Isabelle certified | 4.66 | 0.9982 | 398.4 ms | 54.1× |
| Lean steered | 2.95 | 0.9975 | 42.2 ms | 5.7× |
| Lean certified | 2.62 | 0.9987 | 33.6 ms | 4.6× |
| fpLLL via fplll-ffi | 2.21 | 0.9970 | 7.4 ms | 1.0× |

This is the family the steered architecture targets. **The steered default
leaves the `~n^5.6` complexity class** of the exact reducers, fitting
`p ≈ 2.95` over the top rungs and running **5.6× ahead of exact native at
`n = 55`** (42.2 vs 235.7 ms). The exact `d`/`ν` reducer carries intrinsically
Θ(n⁴)-bit Gram-determinant state on this family — the prefix Gram determinants
have `~6.6·n·i` bits for any basis of the lattice — so its `~n^5.6` cost cannot
be fixed inside the exact representation; the steered path never materializes
that state. The Isabelle-certified curve still rides the `~n^4.7` slope because
it has no interval kernel. The constant-factor framing does not apply across
this mixed set — the per-method gaps grow with `n`, and the table reports the
observed ratio at `n = 55`. The harsh-cubic exponents are local fits over a
narrow high-`n` window; treat them as the slope at these rungs, not a proven
asymptotic.

The steered default and the certified path land within `~1.3×` of each other
here (42.2 vs 33.6 ms): once the exact-GSO state is out of the loop, the
steered native reducer is competitive with certifying an external candidate,
and on this family both are an order of magnitude below the exact `d`/`ν`
reducer. fpLLL's raw float reducer is still `~5×` below either, the gap being
the work neither verified path can skip — the steered path reduces the basis
exactly, the certified path runs the verified reducedness checker.

## Reproduction

From the repository root:

```sh
python3 scripts/plots/hex-lll-scaling.py --all
```

`--family random-bounded` / `--family harsh-cubic` report a single family;
`--window-lo` / `--window-hi` override the fit window (for example, to confirm
the exponent is stable as you widen it, or to fit a freshly added top rung).
The script reads the same committed exports and bench function-name regexes as
`scripts/plots/hex-lll-comparator.py`, so its numbers always match the figure.

To refresh the underlying data after an implementation change, re-run the
HexLLL bench ladders on the bench host (`carica`) per
`reports/hex-lll-performance.md` and `SPEC/benchmarking.md`, commit the new
exports, then re-run the command above and update the [§Results](#results)
tables. The exponent answers "did the change alter the complexity class"; the
`C₃` / observed-ratio columns answer "by what constant factor did it move."

## Caveats

- The curves come from three committed runs: the Lean curves (Lean native,
  Lean steered) and the external curves (Isabelle native, fpLLL) from the
  consolidated `…-steered-ac0d2dcc` sweep, the Lean-certified curve from
  another, and the Isabelle-certified curve from a third — all on `carica`,
  slightly different commits. The two Lean curves and the matched-provenance
  Lean-steered-vs-Lean-native ratio are from one run, so the steered-win
  numbers are exact; cross-run ratios (for example certified-vs-steered) carry
  mild run-to-run noise. A single consolidated six-way sweep would remove it;
  the exponents and the steered-vs-native gap are well outside that noise.
- Exponents are fits over a finite window, not proofs. They report the slope at
  the measured rungs; a wider or higher window can shift them, especially on
  harsh-cubic where the window is narrow.
