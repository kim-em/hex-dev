# Kernel-evaluation cost of `Hex.factor` (`decide +kernel`)

With `native_decide` banned, the trusted way to run a hex computation inside a
proof is **kernel reduction** (`decide +kernel`). This report measures that cost
for the factorization algorithm directly: how long the Lean kernel takes to
evaluate `Hex.factor` on each corpus instance, and at what size it stops being
viable.

This is the interim, generator-free half of the `decide +kernel` trusted-checking
curve requested on issue #8545. The full curve (kernel-check an irreducibility
*certificate* per factor) waits on the compiled certificate generators of
[#8552](https://github.com/kim-em/hex-dev/issues/8552); the architecture there is
compiled `factor` + compiled certificate construction, with the kernel only
checking (a) the factors multiply back to the input and (b) each certificate.
This report is the "(a)-shaped" measurement plus the raw cost of running `factor`
itself in the kernel.

Like the cross-system sweep, this is a diagnostic comparator run, **not CI**
(see [SPEC/benchmarking.md § Cross-system comparator sweeps](../SPEC/benchmarking.md)):
it measures the kernel, not a hex-internal performance claim.

## Method

`scripts/bench/kernel_factor_sweep.py`, per corpus instance:

1. Run the *compiled* `Hex.factor` (via the warm `hexbz_factor_service`) to get
   hex's exact `Factorization`.
2. Generate `example : Hex.factor <f> = <that factorization> := by decide +kernel`
   and time a fresh `lean` invocation checking it. Forcing the full equality
   (not just the factor count) makes the kernel normalize every factor
   coefficient, so the wall time is honest end-to-end kernel evaluation — and it
   double-checks that kernel reduction agrees with compiled evaluation on every
   solved instance.

A fixed per-invocation **import baseline** (loading `HexBerlekampZassenhaus.Basic`)
is measured once and subtracted to report marginal kernel time. Limits:
`maxHeartbeats 0` (disabled, so the wall-clock `--timeout` is the sole cutoff)
and a raised `maxRecDepth`. Instances over the timeout are **censored** (status
`timeout`), which on a frontier chart reads as the curve stopping. Each family is
swept in ascending degree. A **monotone** family (kernel cost rises with degree)
is abandoned at the first cutoff-hit — everything above it only hammers the
cutoff. The **non-monotone** families (`cyclotomic`, `cyclotomic-products`, whose
kernel cost tracks the modular-factor count rather than degree — e.g. Φ₂₈
finishes where Φ₂₂/Φ₂₄ time out) keep exploring, abandoned only after
`--explore-stop-after` (default 3) consecutive censored points.

Feasibility note: the `factor` call graph has **no `partial def`** (which would
be kernel-opaque), and although it contains 15 well-founded recursions
(`termination_by`, normally reluctant to kernel-reduce), they *do* reduce in
practice. `UInt64`/`ZMod64` arithmetic reduces fine in the kernel (GMP-backed
`Nat` literal reduction), so the finite-field inner loops are not a wall.

## Frontier

Canonical run on carica (commit `09a3f193`), 20 s wall timeout, import baseline
0.41 s subtracted; record
`reports/bench-results/hexbz-kernel-factor-canonical.json`. 60/93 instances
kernel-checked; kernel reduction agreed with compiled `factor` on every solved
instance.

| family | highest degree kernel-checked | first censored degree | slowest solved |
| --- | ---: | ---: | ---: |
| cyclotomic | 28 | 22 | 17s |
| chebyshev | 12 | 12 | 11s |
| legendre | 12 | 10 | 16s |
| laguerre | 11 | 12 | 13s |
| random-products | 11 | 12 | 17s |
| wilkinson | 8 | 10 | 9s |
| swinnerton-dyer | 8 | 16 | 6s |
| sd-products | 8 | 16 | 5s |
| cyclotomic-products | 6 | 12 | 6s |
| hoeij-zimmermann | — | 128 | 0s |

Kernel `decide` on `factor` is a cliff: sub-second to degree ~5, single-digit
seconds through degree ~10, then over the wall in the low-to-mid teens. **Trusted
`decide`-checking of the factorization is viable to roughly degree 10–15 at a
20–40 s budget**, and the exact timeout barely moves the frontier because the
cost grows ~exponentially in the recombination work. The family ordering mirrors
the compiled sweep: cyclotomics (few clean modular factors) reach degree 28;
Swinnerton-Dyer (many degree-2 modular factors, heavy recombination) walls at
degree 8. `cyclotomic`/`cyclotomic-products` are the non-monotone cases — cost
tracks the modular-factor count, not degree, so cyclotomic finishes degree 28
above censored degrees 22/24.

![Kernel evaluation frontier for Hex.factor](figures/hexbz-kernel-factor-frontier.svg)

## Reproducing

```
# Frontier probe (fast: low degree cap, tight timeout):
python3 scripts/bench/kernel_factor_sweep.py --max-degree 24 --timeout 40

# Canonical run (all families, ascending degree, monotone families stop at the wall):
python3 scripts/bench/kernel_factor_sweep.py --timeout 20

# Chart:
python3 scripts/plots/hexbz-kernel-frontier.py --record reports/bench-results/<record>.json
```
