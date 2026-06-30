# HexLLL performance

HexLLL is benchmarked against two verified reducers (the Isabelle
`LLL_Basis_Reduction` extraction, native and certified) and the unverified
floating-point `fplll`, across input families chosen to stress *different*
parts of the algorithm. Each family gets one six-curve log-y wall-time plot:

- **Lean native** — the exact integer `d`/`ν` reducer (`lllNative`).
- **Lean steered** — the default: exact row operations steered by an untrusted
  approximate Gram-Schmidt, certified post hoc.
- **Lean certified** — `fplll` candidate + the verified Lean checker (`certCheck`).
- **verified Isabelle native** / **verified Isabelle certified** — the Zenodo
  2636367 extraction, reducer and checker.
- **fpLLL** — the raw floating-point reducer (unverified baseline).

All comparator data below was generated on an **idle carica** under a load
supervisor (each run aborts and is discarded if a concurrent build pushes the
1-minute load average over 9), so every committed export has `env.git_dirty =
false` and clean, internally-consistent timings. Regenerate with
`scripts/dev/run_lll_bench.sh <family> <filter>`.

## Input families and what each stresses

| family | construction (fplll port) | stresses | shape |
|---|---|---|---|
| `random-bounded` | LCG bounded entries | outer-loop / size-reduction count | square, near-orthogonal |
| `harsh-cubic` | entries `~2^{3.3n}` | exact-integer operand-width growth | square |
| `ajtai` | `gen_trg` triangular, `2^{(2d-i)^{1.2}}` diagonal | **swap / iteration count** (`Θ(d² log B)`) | square, worst case |
| `q-ary` | `gen_qary` `[[I,H],[0,qI]]` | Z-shape profile, transition-band swaps | square, crypto |
| `ntru` | `gen_ntrulike` `[[I,Rot h],[0,qI]]` | planted dense sublattice + q-block | `2d×2d` |
| `knapsack` | `gen_intrel`, rectangular `d×(d+1)` | **rectangular `m>n`** `ofBasis`; planted-vector recovery | rectangular |

## The headline: steering is regime-dependent

The default Lean reducer **steers** exact integer row operations from an
untrusted approximate Gram-Schmidt. On `harsh-cubic`, where the cost is driven
by operand *bit-width*, this wins big — steered tracks `fpLLL`'s near-cubic
slope (see the README plot). But on every **structured or worst-case** family,
where the cost is driven by *iteration/swap count* or an ill-conditioned
profile, the approximate Gram-Schmidt cannot reduce the intrinsic work and
steering **backfires** — it is the slowest or near-slowest verified option:

| family | Lean steered (× fastest) | Lean native | **Lean certified** | what happens to steered |
|---|---:|---:|---:|---|
| `ajtai`    | **81×** (p≈7.6) | 53× | **1.4×** | swap-bound; steering can't dodge `Θ(d² log B)` swaps |
| `q-ary`    | **71×** | 6.6× | **2.3×** | Z-shape trips approx-GSO, blows up at `d≥40` |
| `ntru`     | **17.5×** | 9.7× | **1.2×** | planted dense block + q-block slows steering |
| `knapsack` | **21.4×** | 8.3× | **2.5×** | rectangular; a steered-fallback pathology at `n=40` |

In contrast, the **certified path (fpLLL candidate + verified Lean checker)** is
the cheapest *verified* option in every family (1.2–2.5× the unverified fpLLL
baseline) — it inherits floating-point speed and pays only a cheap check. The
exact reducers (Lean native, verified Isabelle native) sit in the middle:
steady, no blow-up, with Lean native a constant factor ahead of the Isabelle
extraction.

**Reading:** on adversarial or structured lattices, the right architecture is
*certify a fast unverified reducer*, not *run a verified exact reducer*, and
*not* steer — steering only pays off when bit-width, not swap count, dominates.

## Per-family plots

### ajtai — the worst case
![ajtai](reports/figures/hex-lll-comparator-ajtai.svg)

The exact reducers blow up `~d⁷`; Lean steered is the worst of all (`p≈7.6`,
81× fpLLL at d=32). The certified path stays cheap (Lean certified 56 ms @
d=32). Lean native completes at d=36 where the Isabelle native extraction is at
parity. The clearest statement of the headline.

### q-ary
![q-ary](reports/figures/hex-lll-comparator-q-ary.svg)

Steered tracks native to d=32, then blows up (622 ms @ d=40 vs native 37 ms) as
the Z-shape transition band defeats the approximate Gram-Schmidt. fpLLL (10 ms)
and Lean certified (24 ms) stay cheap at d=48.

### ntru
![ntru](reports/figures/hex-lll-comparator-ntru.svg)

The planted dense block plus the q-block make steered the slowest verified
reducer (1993 ms vs native 1100 ms at n=24). Lean certified (133 ms) is within
1.2× of fpLLL (114 ms).

### knapsack — the rectangular `m>n` family
![knapsack](reports/figures/hex-lll-comparator-knapsack.svg)

The only family with `cols ≠ rows`, exercising the `m>n` Gram construction in
`ofBasis` (confirmed working through every reducer). Native and Isabelle are
steady; steered hits a fallback pathology at n=40 (708 ms) while the certified
path stays cheap (10 ms @ n=48). This family also drives the planted-vector
success-vs-density chart (`reports/figures/hex-lll-knapsack-success.svg`).

### random-bounded & harsh-cubic — where steering wins
![harsh-cubic](reports/figures/hex-lll-comparator-harsh-cubic.svg)

The two families where the basis is near-orthogonal (`random-bounded`) or the
cost is bit-width-bound (`harsh-cubic`) are exactly where steering pays off. On
`harsh-cubic`, Lean steered stays near fpLLL's slope (69 ms @ n=65) while the
exact reducers blow up (native 602 ms, Isabelle 909 ms) — this is the README
headline. On `random-bounded` (to n=180) steering is ~2.5× faster than native
(1712 ms vs 4357 ms), since the approximate Gram-Schmidt suffices when the swap
count is low. Steering helps precisely when bit-width, not swap count, dominates
— the clean inverse of the four structured families above.

See [reports/hex-lll-performance.md](reports/hex-lll-performance.md) for the
audit report (ratios, per-call overhead, concerns) and
[reports/hex-lll-scaling.md](reports/hex-lll-scaling.md) for the power-law fits.
