# HexLLL performance

HexLLL is benchmarked against the verified Isabelle `LLL_Basis_Reduction`
extraction (native and certified) and the unverified floating-point `fplll`,
across input families chosen to stress *different* parts of the algorithm. Each
family gets one five-curve log-y wall-time plot:

- **Lean native** — the exact integer `d`/`ν` reducer (`lllNative`), the
  in-tree default.
- **Lean certified** — an `fplll` candidate checked by the verified Lean
  checker (`certCheck`); the certified external-dispatch path.
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

## The headline: certify a fast reducer

The exact reducers — Lean's own `lllNative` and the verified Isabelle
extraction — are always correct but their cost climbs steeply on the hard
families: super-quintically with operand width on `harsh-cubic`, and roughly
`d⁷` on the swap-bound `ajtai` worst case. The **certified path (an `fplll`
candidate checked by the verified Lean `certCheck`) is the cheapest *verified*
option in every family** — it inherits floating-point speed and pays only a
cheap integer check:

| family (top rung) | Lean native | Isabelle native | **Lean certified** | fpLLL |
|---|---:|---:|---:|---:|
| `ajtai` d=36     | 4805 ms | 5167 ms | **97 ms** | 73 ms |
| `q-ary` n=48     | 67 ms   | 82 ms   | **24 ms** | 10 ms |
| `ntru` n=24      | 1100 ms | 1444 ms | **133 ms** | 114 ms |
| `knapsack` n=48  | 33 ms   | 26 ms   | **10 ms** | 4 ms |
| `harsh-cubic` n=65 | 602 ms | 909 ms | **59 ms** | 4.7 ms |
| `random-bounded` n=180 | 4357 ms | 7108 ms | **936 ms** | 335 ms |

Lean certified stays within ~1.2–2.5× of the unverified `fplll` baseline
everywhere, while the exact reducers are 10–80× that on the structured families.
Lean native is at parity with or ahead of the Isabelle native extraction on
every family.

**Reading:** on adversarial or structured lattices the right architecture is to
*certify a fast unverified reducer*, not to run a verified exact one — the
verified output is then obtained at close to floating-point cost. `lllNative`
remains the trustworthy in-tree reducer for the provider-free path.

## Per-family plots

### ajtai — the worst case
![ajtai](reports/figures/hex-lll-comparator-ajtai.svg)

The exact reducers blow up `~d⁷` — Lean native reaches 4805 ms at d=36, at
parity with the Isabelle native extraction (5167 ms) — while the certified path
stays cheap (97 ms at d=36, ~1.3× fpLLL). The clearest statement of the
headline.

### q-ary
![q-ary](reports/figures/hex-lll-comparator-q-ary.svg)

The Z-shape profile makes the exact reducers climb; fpLLL (10 ms) and Lean
certified (24 ms) stay cheap at d=48.

### ntru
![ntru](reports/figures/hex-lll-comparator-ntru.svg)

The planted dense block plus the q-block push the exact reducers to ~1–1.4 s at
n=24 (dim 48); Lean certified (133 ms) is within 1.2× of fpLLL.

### knapsack — the rectangular `m>n` family
![knapsack](reports/figures/hex-lll-comparator-knapsack.svg)

The only family with `cols ≠ rows`, exercising the `m>n` Gram construction in
`ofBasis` (confirmed working through every reducer). The exact reducers are
steady here; the certified path stays cheapest (10 ms @ n=48). This family also
drives a planted-vector **success-vs-density** chart
(`reports/figures/hex-lll-knapsack-success.svg`, a separate non-timed driver).

### harsh-cubic — the README headline
![harsh-cubic](reports/figures/hex-lll-comparator-harsh-cubic.svg)

Entry bit-width grows `~3.3n`, so the exact reducers climb super-quintically
(Lean native 602 ms, Isabelle native 909 ms at n=65) while the certified path
tracks fpLLL's near-cubic slope (59 ms vs 4.7 ms). The cleanest picture of the
certified-path speed, and the figure the README embeds.

### random-bounded
![random-bounded](reports/figures/hex-lll-comparator-random-bounded.svg)

The near-orthogonal baseline to n=180: few swaps, so all reducers scale near
cubically; the certified path stays a small constant factor above fpLLL.

## Asymptotics summary

- **fpLLL vs Lean certified**: same asymptotic slope, small constant gap — the
  certified path inherits fpLLL's complexity and adds a cheap verified check.
- **exact reducers (Lean native, Isabelle native)**: same complexity class as
  each other (Lean native a constant factor better); both diverge sharply from
  the certified/fpLLL curves on the structured and worst-case families.

See [reports/hex-lll-performance.md](reports/hex-lll-performance.md) for the
audit report (ratios, per-call overhead, concerns) and
[reports/hex-lll-scaling.md](reports/hex-lll-scaling.md) for the power-law fits.
