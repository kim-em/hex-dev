# hex-sparse-poly — Phase 4 headline performance report

Everything below was measured with `lake exe hexsparsepoly_bench` built
from the `sparse-poly-bench` branch (parent commit `acb2bcf3f` plus the
bench module) on Linux 6.12.100 x86_64, AMD EPYC 9455 (48-core, 96
threads), with the machine otherwise idle. Raw per-run logs and JSONL
exports live under the run artefacts referenced per case; medians are
per-parameter medians of 3 outer trials at LeanBench's autotuned
~200 ms inner batches with `signalFloorMultiplier := 1.0` (in-process
measurement).

## Bench targets

All compiled-track; the library has no proof/tactic surface. One
registration per separable operation, six SPEC input families:

| family | registrations |
|---|---|
| sparse-arithmetic | `runAddDeg3`, `runAddDeg6`, `runMulDeg3`, `runMulDeg6` |
| sparse-multiplication | `runMul{Sort,Tree,Heap}{Low,High}` |
| crossover | `runCrossAdd{Sparse,Dense}`, `runCrossMul{Sparse,Dense}` |
| evaluation | `runEvalGapSparse`, `runEvalDense` |
| substitution-power | `runSubstPowSparse`, `runSubstPowDense` |
| convert-gcd | `runConvertGcd{BinomPair,Generic}`, `runConvertDivModBinomPair`, `runGcdConversionShare` |

`lake exe hexsparsepoly_bench verify` passes (22 registrations).

## Verdicts

Every registration returns **consistent with declared complexity** at
its scientific settings (`lake exe hexsparsepoly_bench run NAME`,
per-target logs):

- `runAddDeg3` (β=−0.098) / `runAddDeg6` (β=+0.046): `O(t)` merges. The
  family's required degree-independence property holds numerically:
  medians at `t = 256` are 15.2 µs (degree `10³`) against 15.0 µs
  (degree `10⁶`).
- `runMulDeg3` (β=−0.144) / `runMulDeg6` (β=−0.147): `O(t² log t²)`,
  again degree-independent (8.73 ms vs 8.67 ms at `t = 256`).
- `runMulSortLow` (β=−0.005), `runMulTreeLow` (β=−0.042),
  `runMulHeapLow` (β=+0.109), `runMulSortHigh` (β=−0.055),
  `runMulTreeHigh` (β=−0.051), `runMulHeapHigh` (β=+0.111).
- `runCrossAddSparse` (β=−0.024), `runCrossAddDense` (constant model,
  β=+0.049), `runCrossMulSparse` (β=−0.037), `runCrossMulDense`
  (constant model, β=+0.084).
- `runEvalGapSparse` (β=−0.011), `runEvalDense` (constant model,
  β=+0.044).
- `runSubstPowSparse` (constant model, β=−0.001): flat in `k`, which is
  the SPEC's required regression check — 127 ns at `k = 8` and 126 ns
  at `k = 32768`.
- `runSubstPowDense` (β=−0.024, after moving the schedule into the
  asymptotic regime), `runConvertGcdBinomPair` (β=−0.022),
  `runConvertGcdGeneric` (β=−0.063), `runConvertDivModBinomPair`
  (β=+0.002), `runGcdConversionShare` (β=−0.105).

Model notes (declared vs first-draft textbook): the convert-gcd pair
models are **linear**, not quadratic — the `x^n − 1, x^m − 1` remainder
sequence performs a constant number of divisions with bounded-degree
quotients, and the generic pair divides by a fixed degree-7 divisor —
and the family runs over the field `ZMod64 7` so that time tracks
coefficient operations (over `ℚ` the generic pair shows the additional
rational coefficient growth: observed `~n^1.3` against the same
linear operation count).

## The multiplication selection

The SPEC leaves the `@[csimp]` multiplication implementation to this
family. Medians:

| candidate | low collision `t=256` | low `t=512` | high collision `t=256` | high `t=512` |
|---|---|---|---|---|
| sort-and-combine (`ofTerms` route) | 17.95 ms | 94.59 ms | 8.44 ms | 37.30 ms |
| `ExtTreeMap` accumulation | **6.04 ms** | **28.25 ms** | **2.72 ms** | **12.65 ms** |
| Johnson heap merge | 75.56 ms | — | 42.24 ms | — |

Both compare groups report `allAgreed` on all common parameters, so the
three candidates are cross-implementation conformance checks of each
other. The **`ExtTreeMap` accumulation wins both shapes by ~3×** and is
selected as the `@[csimp]` twin; the heap merge has the better bound
and, as predicted by the SPEC, a constant that loses it the race at
every measured size. The sort-and-combine specification route stays as
the kernel-facing body.

## Crossover

At matched degree with the term count swept (medians):

- **add**, degree 4096: sparse runs 126 ns (`t=2`) to 30.1 µs (`t=512`);
  dense is flat at ≈ 30 µs. Crossover at **`t ≈ n/8`** (t = 512 of
  4096).
- **mul**, degree 1024: sparse (sort route) runs 273 ns (`t=2`) to
  38.4 ms (`t=512`); dense is flat at ≈ 8 ms. Crossover at
  **`t ≈ n/4`** (between t = 128 at 1.97 ms and t = 256 at 8.65 ms).
  The selected tree twin shifts this toward `n/3`.
- **eval**, degree 65536 over `ZMod64 7`: gap Horner runs 91 ns (`t=2`)
  to 13.5 µs (`t=512`); dense Horner is flat at ≈ 268 µs. Gap Horner
  is ahead by 20× even at `t = 512 = n/128`; extrapolating the linear
  sparse curve, parity sits near **`t ≈ n/6`**.

These are per-operation numbers, as the SPEC requires; they are written
back into the SPEC's crossover paragraph.

## Comparator ratios

Both declared comparators are `informational`
(`libraries.yml: phase4.comparators`); neither gates.

- **SymPy sparse ring elements** (`sympy.polys.rings`, the conformance
  oracle): on the shared low-collision `t = 256` inputs of
  `prepMulSelect`, SymPy multiplies in 15.6 ms against Lean's 6.0 ms
  (tree candidate) — Lean ≈ 2.6× faster; sparse addition at `t = 256`
  is 16.4 µs in SymPy against 15.2 µs in Lean (parity). Measured with
  `sympy_ratio.py` mirroring the bench generators, best of 5.
- **python-flint `fmpz_poly`** (dense; crossover family only): recorded
  as scheduled-only for the release benchmarking environment, per the
  informational classification — the dense side of the crossover family
  already measures the representation choice in-process, which is the
  comparison the SPEC says is meaningful below the crossover.

## Profile

One case per input family (`scripts/profile/run_profile.sh`, samply
0.13.1 at 999 Hz, lean-bench-samply filter; every case passed
calibration residual < 5 ms, retained ≥ 1700 bench-thread samples, and
the ±5 ms sensitivity check). Categories are leaf self-time.

- **sparse-multiplication** — `runMulTreeLow`, `t=512` (3215 samples):
  93.4% compiled tree code (`DTreeMap.Internal.insert` 76.4%,
  `getD` 17.0%), 6.3% the product loop. The selected candidate's cost
  is exactly its tree updates; nothing unattributed.
- **sparse-arithmetic** — `runMulDeg6`, `t=256` (1730 samples): the
  sort route splits across `MergeSort.Internal.mergeTR_go` 26.3%,
  `splitRevAt_go` 12.3%, `List.reverseAux` 10.5%, closure dispatch
  (`lean_apply_2`) 12.6%, allocator 11.0%, and the `ofTermsImpl`
  combine lambda 9.4% — the sort dominates, which is why the tree twin
  wins.
- **crossover** — `runCrossMulSparse`, `t=512` (1802 samples): same
  shape as `runMulDeg6` (mergeTR 28.6%, reverseAux 13.0%), as expected
  for the same code path at a different degree.
- **evaluation** — `runEvalGapSparse`, `t=512` (2428 samples): 42.5%
  in the `ZMod64` extern multiply (`lean_hex_zmod64_mul` — own
  library FFI, categorised under runtime by symbol prefix), 22.4% in
  the binary gap powering `pow1`, 9.6% in the `evalShifted` walk.
  Multiplications dominate exactly as the `O(t log(n/t))`-multiplies
  model says.
- **substitution-power** — `runSubstPowSparse`, `k=32768` (3426
  samples): the whole operation is ~128 ns, so fixed structure
  allocation and refcounting dominate (alloc 27.4%, runtime 38.8%,
  `mapTerms` walk plus checksum 28%). Nothing scales with `k`, which
  is the point.
- **convert-gcd** — `runConvertGcdBinomPair`, `n=1024` (4511 samples):
  39.2% own code (the dense `DensePoly` division loops reached through
  the conversions), 27.6% allocation (the dense arrays), 20.4%
  runtime. The conversion share registered separately is ≈ 4 µs of the
  89.8 µs total (≈ 5%): even on the sparse-remainder pair the dense
  algorithm, not the conversion, is ~95% of the cost — the number the
  SPEC's open question about a sparse division algorithm asked for.

## Concerns

None.
