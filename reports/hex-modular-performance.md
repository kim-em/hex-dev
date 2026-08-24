# HexModular Performance Report

## Bench Targets

The Mathlib-free suite is registered in `bench/HexModular/Bench.lean`. All
inputs are deterministic and use no random seed. Preparation constructs the
prime supplies, residues, and Fibonacci pairs outside the timed region; the
targets hash their exact answers inside the benchmark harness.

| target | input family | declared model |
|---|---|---|
| `runScalarCrt` | `incremental-crt` | `k²` |
| `runCrtLoop` | `incremental-crt` | `k²` |
| `runVectorCrtWidth` | `vector-crt` | `n` |
| `runVectorCrtDepth` | `vector-crt` | `k²` |
| `runSymMod` | `rational-reconstruction` | `bits * sqrt(bits)` |
| `runEuclid` | `rational-reconstruction` | `b²` |
| `runRatReconLate` | `rational-reconstruction` | `b²` |
| `runRatReconWide` | `rational-reconstruction` | `b * sqrt(b)` |
| `runRatReconMaxQuot` | `rational-reconstruction` | `b²` |
| `runRatReconCheck` | `rational-reconstruction` | `b` |
| `runRatReconVec` | `rational-reconstruction` | `n` |
| `runRatReconFailure` | `failure-cost` | `b²` |

The fixed comparator registrations are in
`bench/HexModularBench/Comparator.lean`. A persistent Python service in
`scripts/oracle/modular_bench_driver.py` removes process startup from the
measurements and implements the declared `gmpy2.gcdext` and python-flint
`fmpz_mod_ctx` comparators. The latter is the manifest's
`python-flint fmpz CRT` comparator: it executes the same incremental Garner
recurrence with FLINT integers and modular inverses.

## Verdicts

The native three-trial run used clean commit
`afbacd447ef150cf72eb8b9e8a5400ca6dbfb8c9` on `chungus2` (AMD EPYC 9455
48-Core Processor, x86-64 Linux), Lean `4.34.0-rc2`, and lean-bench `0.1.0`.
It ran the twelve targets above with `.lake/build/bin/hexmodular_bench run`,
three outer trials, and export path
`reports/bench-results/hex-modular-native-afbacd44-chungus2.json`. The
committed export has SHA-256
`cae2d878ef6e3962eee912be83e0bebb9118239fefb4f43e82709c590cc64065`.

| target | rungs | first → last median | residual slope β | verdict |
|---|---:|---:|---:|---|
| `runVectorCrtWidth` | 1…4096 | 0.028 → 37.209 ms | −0.065 | consistent |
| `runScalarCrt` | 4…8192 | 0.007 → 194.894 ms | −0.084 | consistent |
| `runSymMod` | 64…65536 | 0.000057 → 0.205 ms | +0.038 | consistent |
| `runRatReconWide` | 64…262144 | 0.000458 → 7.340 ms | +0.199 | consistent |
| `runRatReconVec` | 1…4096 | 0.000356 → 0.482 ms | −0.022 | consistent |
| `runEuclid` | 64…262144 | 0.008 → 3,891.322 ms | −0.193 | consistent |
| `runVectorCrtDepth` | 4…8192 | 0.087 → 4,476.360 ms | −0.093 | consistent |
| `runRatReconMaxQuot` | 64…262144 | 0.010 → 3,374.841 ms | −0.196 | consistent |
| `runRatReconLate` | 64…262144 | 0.008 → 2,956.436 ms | −0.151 | consistent |
| `runCrtLoop` | 4…8192 | 0.018 → 1,004.672 ms | −0.071 | consistent |
| `runRatReconCheck` | 64…65536 | 0.000119 → 0.002720 ms | −0.096 | consistent |
| `runRatReconFailure` | 64…262144 | 0.008 → 2,915.113 ms | −0.137 | consistent |

Every target returned `consistent_with_declared_complexity`; none was budget
truncated. The declared schedules cover the word-size CRT transition and the
large Fibonacci Euclidean regime rather than extrapolating beyond the
twelve-second per-call ceiling.

## Comparator Ratios

The clean fixed run used commit
`417a912760c084019d33e1a8e503c1be49dda52b` on the same host and toolchain:

```sh
HEX_MODULAR_BENCH_PYTHON=/tmp/hex-modular-bench-venv/bin/python \
  .lake/build/bin/hexmodular_bench run \
  --filter Hex.ModularBench.Comparator \
  --export-file reports/bench-results/hex-modular-comparators-417a9127-chungus2.json
```

The export contains 71 fixed targets, five repeats per target, and matching
answer hashes for every Lean/comparator pair. Its SHA-256 is
`378a43292ccb16b0d4b318a4f3244057cf4fabe09bc5630e9dbf0bccd98fe157`.
The persistent-call median overhead was 9.621 µs. As specified, a rung is
eligible only when the comparator is at least twice that overhead and both
calls complete within ten seconds. Ratios below are `Hex time / comparator
time`; values below one mean Hex is faster. Both comparators are
informational, so there is no gating threshold.

| family | eligible rungs | bottom ratio | top ratio | top medians (Hex / comparator) |
|---|---:|---:|---:|---:|
| `incremental-crt` | 4…8192 (12) | 0.323× | 0.301× | 186.111 / 618.246 ms |
| `vector-crt` | 1…4096 (8) | 0.286× | 0.248× | 34.463 / 138.953 ms |
| `rational-reconstruction` | 512…262144 (12) | 2.642× | 9.961× | 2,901.900 / 291.328 ms |
| `failure-cost` | 512…262144 (12) | 2.615× | 10.006× | 2,915.113 / 291.328 ms |

The two CRT families settle near a small constant ratio after fixed costs,
with Hex about 3.3× faster for scalar accumulation and 4.0× faster for the
fixed-depth vector case at the largest rung. The two Fibonacci families
instead rise from about 2.6× at 512 bits to about 10× at 262144 bits. That
adverse trend is expected for this informational comparison: `gmpy2.gcdext`
dispatches directly to GMP's tuned full extended GCD, whereas Hex executes
its explicit truncated Lean recurrence and proof-oriented result shape.

The committed plots use exactly the eligible rungs and the two exports cited
above:

- [incremental CRT](figures/hex-modular-comparator-incremental-crt.svg)
- [vector CRT](figures/hex-modular-comparator-vector-crt.svg)
- [rational reconstruction](figures/hex-modular-comparator-rational-reconstruction.svg)
- [failure cost](figures/hex-modular-comparator-failure-cost.svg)

## Profile

One compiled case per input family was captured from clean commit
`9542c7c28df6a1ff98464b9f34dea2d7395fadd3` on `chungus2` (AMD EPYC 9455,
x86-64 Linux 6.12.100), with Lean `4.34.0-rc2`, lean-bench `0.1.0`,
lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, and samply `0.13.1` at 999 Hz.
The filtered profiles, symbol sidecars, and diagnostics remain under `/tmp`
and are not committed. The command form was:

```sh
python3 /tmp/lean-bench-samply.SDVVOD/repo/scripts/profile_bench.py \
  --bench-exe .lake/build/bin/hexmodular_bench \
  --bench-name BENCH_NAME --param PARAM --target-nanos 3000000000 \
  --out /tmp/hex-modular-profile-FAMILY-PARAM.json.gz \
  --samply-args '--rate 999 --unstable-presymbolicate'
```

| family | target and parameter | own code | GMP | allocation/free | Lean runtime | other |
|---|---|---:|---:|---:|---:|---:|
| `incremental-crt` | `runScalarCrt`, 8192 | 0.10% | 89.56% | 9.46% | 0.88% | 0.00% |
| `vector-crt` | `runVectorCrtWidth`, 4096 | 1.51% | 19.63% | 69.57% | 8.61% | 0.69% |
| `rational-reconstruction` | `runEuclid`, 262144 | 0.02% | 88.77% | 10.87% | 0.34% | 0.00% |
| `failure-cost` | `runRatReconFailure`, 262144 | 0.05% | 88.53% | 11.12% | 0.28% | 0.02% |

For scalar CRT, `Crt.pushImpl` and its accumulation fold each covered 42.3%
of samples inclusively, while `symMod` covered 11.0%. The flat cost is chiefly
GMP single-limb division, multiplication, and copying, exactly the growing
integer work performed by the registered incremental target.

For vector CRT, `CrtVec.pushImpl` covered 95.7%, its `Array.zipWithM` loop
93.1%, and `symMod` 48.4% inclusively. Allocation dominates because every
coordinate constructs successive arbitrary-precision residues; the inclusive
ranking remains wholly inside the registered vector push path.

For rational reconstruction, `euclidUntil.go` covered 69.5% inclusively.
For forced failure, `ratRecon?` and `euclidUntil.go` each covered 70.0%.
Their flat profiles are both dominated by GMP limb copies and single-limb
multiply/add/subtract operations generated by the Fibonacci Euclidean
recurrence. The final failed-bound checks add no separate dominant cost.

All four filtering runs passed confidence and the ±5 ms sensitivity check:

| family | residual | timed duration | retained / rejected | other-thread noise | sensitivity |
|---|---:|---:|---:|---:|---|
| `incremental-crt` | 0.436 ms | 2,995.2 ms | 2,970 / 451 | 0 | passed |
| `vector-crt` | 0.598 ms | 2,384.4 ms | 2,323 / 75 | 0 | passed |
| `rational-reconstruction` | 0.258 ms | 4,267.8 ms | 4,175 / 1,003 | 0 | passed |
| `failure-cost` | 0.007 ms | 4,331.7 ms | 4,279 / 954 | 0 | passed |

No dominant inclusive cost lies outside its registered benchmark target.

## Concerns

None.
