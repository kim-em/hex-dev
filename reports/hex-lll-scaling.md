# HexLLL Scaling Report

This report fits the asymptotic scaling of the HexLLL comparators — the five
random-bounded curves and the three harsh-cubic curves of the comparator plot
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

### random-bounded, rungs 120–180

- `reports/bench-results/hex-lll-certified-443bf8fb.json` — host `carica`, commit `443bf8fb`
- `reports/bench-results/hex-lll-certified-carica.json` — host `carica`, commit `4c708c7b`
- `reports/bench-results/hex-lll-random-bounded-schur.json` — host `carica`, commit `56f34229`

| method | exponent p | R² | C₃ (ns·n³) | × fpLLL |
|---|---:|---:|---:|---:|
| Isabelle native | 3.37 | 0.9996 | 1194 | 26.5× |
| Lean native | 3.03 | 0.9990 | 801 | 17.8× |
| Isabelle certified | 3.07 | 0.9977 | 407 | 9.0× |
| Lean certified | 3.20 | 0.9997 | 171 | 3.8× |
| fpLLL via fplll-ffi | 3.09 | 1.0000 | 45 | 1.0× |

Exponents agree to within 0.33, so the five methods share one complexity
(empirically `~n³` on this instance family) and differ only by a constant
factor. The headline reading:

- **Certifying buys ~4.7× over native at matched provenance.** Lean certified
  sits at 3.8× fpLLL against Lean native's 17.8× — the same answer for a
  ~4.7× smaller constant, because fpLLL produces the basis and Lean only
  checks it.
- **Lean beats Isabelle by a constant ~1.5–2.4× on both rows.** Native
  26.5/17.8 ≈ 1.5×; certified 9.0/3.8 ≈ 2.4×.
- **fpLLL's raw constant is ~3.8× below even Lean certified**, the gap being
  the checker (the packed-evaluation same-lattice clause plus a small-basis
  integer Gram–Schmidt), which `reports/hex-lll-performance.md` measures as
  ~62–72% of the certified path.

### harsh-cubic, rungs 40–55

- `reports/bench-results/hex-lll-harsh-cubic-extended-schur.json` — host `carica`, commit `56f34229`

| method | exponent p | R² | median @ n=55 | × fastest @ n=55 |
|---|---:|---:|---:|---:|
| Isabelle native | 5.76 | 0.9997 | 356.0 ms | 48.4× |
| Lean native | 5.59 | 0.9999 | 234.3 ms | 31.8× |
| fpLLL via fplll-ffi | 2.21 | 0.9970 | 7.4 ms | 1.0× |

Here the exponents span 3.55: the native reducers scale far worse (`~n^5.6`
over this window) than fpLLL (`~n^2.2`), so the curves fan out rather than run
parallel. The constant-factor framing does not apply — the 31.8× / 48.4× gaps
are the observed ratios at `n=55` and grow with `n`. The harsh-cubic exponents
are local fits over a narrow high-`n` window; treat them as the slope at these
rungs, not a proven asymptotic.

This is why the harsh-cubic comparator figure shows only the three
native/fpLLL curves: the certified path's cost is dominated by its checker at
the measured rungs (`n ≤ 55`), where it runs slightly slower than native (see
the ratio tables in `reports/hex-lll-performance.md`). But the diverging
exponents predict a crossover — because fpLLL pulls away from the natives as
`n` grows, the certified path (fpLLL + checker) must eventually overtake native
on harsh-cubic at some `n` beyond the current ladder. Locating that crossover
is a candidate for a future densified run.

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

- The random-bounded curves come from three committed runs: the native
  curves (Isabelle native, Lean native, fpLLL) from one, the Lean-certified
  curve from another, and the Isabelle-certified curve from a third — all on
  `carica`, slightly different commits. Within each run the ratios are
  exact; cross-run ratios (for example certified-vs-native) carry mild
  run-to-run noise. A single consolidated five-way sweep would remove it;
  the exponents and the ~4.7× certify-win are well outside that noise.
- Exponents are fits over a finite window, not proofs. They report the slope at
  the measured rungs; a wider or higher window can shift them, especially on
  harsh-cubic where the window is narrow.
