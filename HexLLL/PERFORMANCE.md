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

> **Note (regenerate on an idle machine).** The committed numbers must come from
> a quiet carica: concurrent build load inflates and lumps the curves. Every
> export records `env.git_dirty` + host + timestamp; regenerate with
> `scripts/dev/run_lll_bench.sh <family> <filter>`. Figures currently in the
> tree from a loaded machine are marked provisional below.

## Input families and what each stresses

| family | construction (fplll port) | stresses | shape |
|---|---|---|---|
| `random-bounded` | LCG bounded entries | outer-loop / size-reduction count | square, near-orthogonal |
| `harsh-cubic` | entries `~2^{3.3n}` | exact-integer operand-width growth | square |
| `ajtai` | `gen_trg` triangular, `2^{(2d-i)^{1.2}}` diagonal | **swap / iteration count** (`Θ(d² log B)`) | square, worst case |
| `q-ary` | `gen_qary` `[[I,H],[0,qI]]` | Z-shape profile, transition-band swaps | square, crypto |
| `ntru` | `gen_ntrulike` `[[I,Rot h],[0,qI]]` | planted dense sublattice + q-block | `2d×2d` |
| `knapsack` | `gen_intrel`, rectangular `d×(d+1)` | **rectangular `m>n`** `ofBasis`; planted-vector recovery | rectangular |

## How we're doing, per family

### ajtai — the worst case (provisional numbers; shape reproducible)

![ajtai](reports/figures/hex-lll-comparator-ajtai.svg)

The headline result on adversarial worst-case input. The **exact** reducers all
blow up super-polynomially (fitted exponents ≈ `d⁷` over the measured window):
Lean native, verified Isabelle native, and — notably — **Lean steered, which is
*slower* than Lean native here**. Steering wins on `harsh-cubic` by dodging
bit-width growth, but `ajtai` is **swap-bound**: the approximate Gram-Schmidt
cannot reduce the intrinsic iteration count, so steering only adds overhead.
Meanwhile the **certified path (fpLLL candidate + verified Lean checker) stays
cheap** — it inherits fpLLL's floating-point speed and pays only a cheap check.
Lean native also scales slightly better than the Isabelle native extraction
(it still completes where Isabelle exceeds the per-call cap at the top rung).

**Reading:** on worst-case lattices, the right architecture is *certify a fast
unverified reducer*, not *run a verified exact reducer* — and steering is not a
universal win. (Numbers pending an idle-machine rerun; the ordering and the
~`d⁷` blow-up of the exact reducers are stable across runs.)

### harsh-cubic — the steered-escape headline

![harsh-cubic](reports/figures/hex-lll-comparator-harsh-cubic.svg)

The default headline plot: the exact-integer reducers climb super-quintically as
entry bit-width grows `~3.3n`, while **Lean steered tracks fpLLL's near-cubic
slope** (steering drives the exact row operations from cheap approximate data).
This is the family where steering pays off — the opposite of `ajtai`.

### random-bounded, q-ary, ntru, knapsack

Comparator plots: `reports/figures/hex-lll-comparator-{random-bounded,q-ary,ntru,knapsack}.svg`.
`q-ary`/`ntru`/`knapsack` are new families pending their first clean-machine
run; `knapsack` additionally validates the **rectangular `m>n`** path (confirmed
working through every reducer) and will carry a planted-vector
**success-vs-density** chart. Numbers land with the idle-machine regeneration.

## Asymptotics summary

- **`fplll` vs Lean certified**: same asymptotic slope, small constant gap — the
  certified path inherits fpLLL's complexity and adds a cheap verified check.
- **exact reducers (Lean native, Isabelle native)**: same complexity class as
  each other (Lean native a constant factor better); both diverge from the
  certified/fpLLL curves on the hard families.
- **Lean steered**: matches fpLLL's slope on width-bound families
  (`harsh-cubic`) but joins the exact reducers' blow-up on swap-bound families
  (`ajtai`) — steering is regime-dependent, not a universal speedup.

See [reports/hex-lll-performance.md](reports/hex-lll-performance.md) for the
audit report (ratios, per-call overhead, concerns) and
[reports/hex-lll-scaling.md](reports/hex-lll-scaling.md) for the power-law fits.
