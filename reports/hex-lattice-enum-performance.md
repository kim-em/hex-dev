# Exact lattice enumeration performance

## Bench targets

The compiled performance owner is `HexLatticeEnum`. All search, preparation,
LLL transport, certificate production, replay and decoding execute without
Mathlib. `HexLatticeEnumMathlib` is a correspondence-only layer; its build-only
kernel examples are correctness regressions, with no tactic or elaborator API.

The [driver](../bench/HexLatticeEnum/Bench.lean) has 19 **mode 1** registrations
with independently derived, family-specific tight models, and 16 fixed latency
and output-hash anchors. The fixed anchors do not discharge complexity coverage.
No universal polynomial bound in rank is claimed: enumeration is exponential
in general and must write every answer. For a traversal with V visited nodes
and L leaves, centres cost O(n) arithmetic per node, direct reconstruction costs
O(nm) per leaf, and sorting L ambient vectors costs O(m L log L). Preparation,
input independence checking and exact integer square roots have their own costs;
arithmetic cost also depends on operand bit lengths.

The ambient ladders fix rank two, coefficient/rational sizes and tree shape,
then vary m from 64 to 2048. Scanning vectors gives a tight linear model for
input validation, preparation, retargeting, Babai, optimum search, the final tie
pass, closest/shortest APIs, budgeted search, LLL, certificate production,
replay, encoding and decoding. Babai/closest/certificate ladders use a seed
strictly worse than the optimum; shortest improves its initial basis-row seed;
LLL performs a nontrivial reduction. Rank, radius and output-size ladders
exercise growing search trees separately. Adjacent registration comments give
the cost derivations.

| Family | Coverage |
| --- | --- |
| rank-radius | Unit lattices at radius one with increasing rank; rank-one radius sweep; fixed rank/radius controls. |
| basis-quality | Unimodular shears 0, 10, 100 with and without checked LLL; quadratic shear sweep; rectangular LLL. |
| coefficient-height | Rank-two basis and rational-target controls at 8, 64 and 256 bits. These are output/latency controls, without an unsupported bit-complexity fit. |
| rectangular-target | Fixed rank and tree with growing ambient dimension and nonzero off-span residual. |
| ties-boundary | A₂ shortest vectors, half-integral cube targets with exponentially many boundary ties, and improving shortest seeds. |
| babai-gap | Integer least squares where the Babai squared distance is 2 and the optimum is 1; its rectangular extensions. |
| certificate-replay | Preparation, seed, optimization, ties, packaging, replay and codecs measured separately. |

`Input` fixtures hoist preparation and existing search results only for operations
that consume them. End-to-end registrations prepare and search inside the timed
body. Rank/radius/cube use a smaller `BallInput` fixture, avoiding unrelated
optimum and tie searches during fixture initialization. Pure parametric runners
return a consumed checksum; IO anchors read their fixture reference inside the
measured callback. Separate `sizes` validation checks completed searches,
certificate acceptance and exact point equality before reporting work counts.

## Verdicts

All 19 declared models pass; all 35 smoke registrations pass. Measurements use
Lean 4.34.0-rc2 and lean-bench 0.1.0 on Linux/x86_64, an AMD EPYC 9455 host
(`chungus2`). This is a shared host: raw trial spread is preserved, and these
numbers are family-scaling evidence rather than portable latency promises.
The [initial complete export](bench-results/hex-lattice-enum/scientific-initial.json)
contains 17 passing ladders and two inconclusive results. The final
[rank](bench-results/hex-lattice-enum/rank-final.json) and
[cube](bench-results/hex-lattice-enum/cube-final.json) exports replace those two.
A [complete final rerun](bench-results/hex-lattice-enum/scientific-final.json)
passes all 19 ladders together and preserves every fixed-anchor hash. The table
uses this final rerun. C is time divided by the declared
model, in nanoseconds; β is the harness slope of that normalized cost.

| Registration | Model | Range | C range | β | Verdict |
| --- | --- | --- | --- | --- | --- |
| `runAmbient` | m | 64–2048 | 4496.3–5180.8 | 0.010 | consistent |
| `runAmbientBabai` | m | 64–2048 | 487.4–503.4 | -0.002 | consistent |
| `runAmbientBudget` | m | 64–2048 | 2858.6–3518.1 | -0.021 | consistent |
| `runAmbientCertificate` | m | 64–2048 | 4547.2–5608.4 | 0.030 | consistent |
| `runAmbientClosest` | m | 64–2048 | 4834.4–5220.8 | -0.010 | consistent |
| `runAmbientDecode` | m | 64–2048 | 1425.8–1683.9 | -0.022 | consistent |
| `runAmbientEncode` | m | 64–2048 | 679.2–758.3 | -0.018 | consistent |
| `runAmbientInput` | m | 64–2048 | 81.1–91.9 | -0.018 | consistent |
| `runAmbientLLL` | m | 64–2048 | 9163.2–9820.1 | 0.022 | consistent |
| `runAmbientOptimum` | m | 64–2048 | 1378.7–1822.8 | 0.003 | consistent |
| `runAmbientPreparation` | m | 64–2048 | 1772.0–1991.0 | 0.012 | consistent |
| `runAmbientReplay` | m | 64–2048 | 3415.6–3530.6 | 0.004 | consistent |
| `runAmbientRetarget` | m | 64–2048 | 842.0–860.7 | 0.004 | consistent |
| `runAmbientShortest` | m | 64–2048 | 7123.0–8120.6 | -0.015 | consistent |
| `runAmbientTies` | m | 64–2048 | 731.2–878.8 | 0.005 | consistent |
| `runCube` | n²2ⁿ | 8–13 | 133.7–197.4 | — | consistent |
| `runRadius` | r(log₂r + 1) | 64–4096 | 320.0–509.7 | -0.087 | consistent |
| `runRank` | n³ | 32–256 | 270.4–415.8 | 0.067 | consistent |
| `runShear` | s² | 8–256 | 1697.3–1990.8 | 0.030 | consistent |

The rank family has (n+1)² visited nodes and 2n+1 leaves; its centre and
reconstruction work is Θ(n³). The original n=8…128 sweep was inconclusive
(β≈−0.200); n=32…256 with three trials gives β≈−0.108. The model is unchanged.
An intermediate attempt hit the child wall cap while constructing unrelated
optimization fixtures; [that export](bench-results/hex-lattice-enum/rank-intermediate.json)
is retained. The final fixture builds only the requested ball input.
The cube family has exactly 2ⁿ ties; its Θ(n²2ⁿ) declaration is unchanged.
Its original n=6…12 sweep was inconclusive; n=8…13 with three trials passes.
These failures and their resolution are tracked in [#10111](https://github.com/kim-em/hex-dev/issues/10111).

The final rank-256 median is about 6.98 seconds; cube rank 13 emits 8192 points
in about 185 milliseconds. The three rank trials have substantial spread on
smaller rungs; the full samples remain in the export. Fixed anchors retain their
expected hashes. The [smoke log](bench-results/hex-lattice-enum/verify.log)
records all 35 passes and less than one second in the CI budget wrapper.
[Work counts](bench-results/hex-lattice-enum/sizes.txt) record dimensions,
radii, ball nodes/answers and separate optimization/tie nodes.

Reproduce after `lake build hexlatticeenum_bench`:

```sh
.lake/build/bin/hexlatticeenum_bench sizes
.lake/build/bin/hexlatticeenum_bench verify
.lake/build/bin/hexlatticeenum_bench run --filter Hex.LatticeEnumBench --export-file /tmp/lattice-scientific.json
GITHUB_ACTIONS=true scripts/ci/check_bench_verify_budget.sh hexlatticeenum_bench
```

## Comparator ratios

**fplll shortest_vector and closest_vector** is informational. The driver pins
fplll 5.5.0, explicitly selects `SVPM_PROVED` and `CVPM_PROVED`, requests
LLL with δ=.999, η=.501, and checks the required .99/.51 inequalities using
exact rationals before invoking search. It checks both integer-lattice
inclusions after reduction, candidate membership, nonzero SVP output and the
exact minimum against Hex. All 24 supported square cases agree. Rational CVP
scales the original basis and target by their common target denominator and
rescales squared distances afterward. Failures abort the comparison.

Hex preparation, seed and optimum-search times are separate; tie enumeration
and certificate production are excluded from this comparison. Optional Hex LLL
is timed on the original input. fplll always reduces that same original input
(after denominator scaling), and reports LLL, exact prerequisite validation and
search separately. A reduced versus unreduced search is a basis-quality
comparison, not a constant-factor implementation comparison. Each time is the
median of five repetitions after one warmup, excluding subprocess startup and
Python validation. The [requests](bench-results/hex-lattice-enum/fplll-input.jsonl)
and [results](bench-results/hex-lattice-enum/fplll-results.jsonl) retain all
cases, parameters and status codes. Selected times below are microseconds.

| Case | Hex LLL | Hex prepare + seed | Hex search | fplll LLL | fplll prerequisite | fplll search | Search ratio Hex/fplll |
| --- | --- | --- | --- | --- | --- | --- | --- |
| shear-0-lll-false | 0.00 | 6.69 | 4.96 | 8.99 | 1.17 | 7.81 | 0.63× |
| shear-0-lll-true | 23.86 | 6.57 | 5.01 | 6.09 | 1.17 | 7.92 | 0.63× |
| shear-10-lll-false | 0.00 | 7.48 | 121.00 | 6.29 | 1.08 | 7.82 | 15.47× |
| shear-10-lll-true | 25.57 | 6.73 | 6.18 | 6.46 | 1.07 | 7.83 | 0.79× |
| shear-100-lll-false | 0.00 | 8.10 | 10984.63 | 6.25 | 1.09 | 7.91 | 1388.35× |
| shear-100-lll-true | 25.50 | 6.66 | 6.24 | 6.23 | 1.13 | 7.89 | 0.79× |

The unreduced shear-100 search is expensive because its initial sibling interval
grows quadratically with shear. Checked LLL removes that growth on this lattice.
The comparator uses floating-point Gram–Schmidt with error control; Hex uses
exact rationals and additionally supports complete tie lists and certificates.
Full-ball/all-ties enumeration, certificate replay and codecs, and Babai-only
calls have `no-comparable-surface-in-named-comparator` under this fplll API.
The independent Fraction Cartesian oracle checks their exact outputs, using
coefficient bounds from a left inverse rather than Gram–Schmidt search bounds.

The comparator contracts are in the pinned
[SVP/CVP header](https://github.com/fplll/fplll/blob/5.5.0/fplll/svpcvp.h),
[defaults](https://github.com/fplll/fplll/blob/5.5.0/fplll/defs.h) and
[LLL guarantees](https://github.com/fplll/fplll/blob/5.5.0/README.md).
The local informational comparator is reproducible with fplll 5.5.0, GMP,
MPFR, a C++ compiler and pkg-config:

```sh
scripts/oracle/setup_lattice_enum_fplll.sh
.lake/build/bin/hexlatticeenum_bench comparisons > /tmp/lattice-fplll-input.jsonl
python3 scripts/oracle/lattice_enum_fplll.py \
  --binary .cache/oracles/lattice-enum-fplll/lattice_enum_fplll \
  < /tmp/lattice-fplll-input.jsonl
```

On NixOS the setup command was run through
`nix-shell -p fplll gmp mpfr pkg-config gcc --run scripts/oracle/setup_lattice_enum_fplll.sh`.
It is a standalone timing driver, with no new trusted Hex FFI boundary.
The independent Cartesian oracle and benchmark smoke extend the existing CI job.

## Profile

The [profile driver](../scripts/profile/lattice_enum_profile.py) uses the
repository's lean-bench-samply orchestrator with timed-region sidecars,
`--rate 999 --unstable-presymbolicate`, and a one-second target. It retains
filtered stacks, symbol tables, calibration diagnostics and categorized
summaries in [profiles](bench-results/hex-lattice-enum/profiles/).
The manifest pins the sampler commit, executable SHA256 and source hashes.
All 20 profiles pass the postprocessor's calibration, minimum-sample and
sensitivity checks. The table quotes each diagnostic and leaf-cost breakdown;
full inclusive rankings appear in each linked summary. Profile timings are
coverage diagnostics, not benchmark timings. Every required family is covered,
including the large comparator gap (shear) and coefficient-height controls.

| Case | Parameter | Samples | Timed ms | Residual ms | Own % | GMP % | Allocation % | Runtime % | Confidence / sensitivity |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| [runAmbient](bench-results/hex-lattice-enum/profiles/runAmbient.summary.json) | 2048 | 785 | 793.5 | 1.162 | 4.59 | 27.64 | 34.39 | 33.38 | passed / passed |
| [runAmbientBabai](bench-results/hex-lattice-enum/profiles/runAmbientBabai.summary.json) | 2048 | 656 | 661.3 | 0.896 | 5.79 | 29.27 | 30.95 | 33.38 | passed / passed |
| [runAmbientBudget](bench-results/hex-lattice-enum/profiles/runAmbientBudget.summary.json) | 2048 | 909 | 920.5 | 1.380 | 5.61 | 43.56 | 24.20 | 26.62 | passed / passed |
| [runAmbientCertificate](bench-results/hex-lattice-enum/profiles/runAmbientCertificate.summary.json) | 2048 | 834 | 847.8 | 0.839 | 4.68 | 33.45 | 34.53 | 27.34 | passed / passed |
| [runAmbientClosest](bench-results/hex-lattice-enum/profiles/runAmbientClosest.summary.json) | 2048 | 829 | 834.5 | 1.145 | 3.62 | 34.26 | 35.34 | 26.78 | passed / passed |
| [runAmbientDecode](bench-results/hex-lattice-enum/profiles/runAmbientDecode.summary.json) | 2048 | 995 | 1009.4 | 1.808 | 12.66 | 7.14 | 32.96 | 40.00 | passed / passed |
| [runAmbientEncode](bench-results/hex-lattice-enum/profiles/runAmbientEncode.summary.json) | 2048 | 1117 | 1122.5 | 1.856 | 5.91 | 0.00 | 24.35 | 69.74 | passed / passed |
| [runAmbientInput](bench-results/hex-lattice-enum/profiles/runAmbientInput.summary.json) | 2048 | 673 | 684.6 | 0.574 | 23.03 | 0.00 | 0.30 | 76.67 | passed / passed |
| [runAmbientLLL](bench-results/hex-lattice-enum/profiles/runAmbientLLL.summary.json) | 2048 | 643 | 645.2 | 0.728 | 6.22 | 39.35 | 27.06 | 27.37 | passed / passed |
| [runAmbientOptimum](bench-results/hex-lattice-enum/profiles/runAmbientOptimum.summary.json) | 2048 | 917 | 919.9 | 0.944 | 5.45 | 38.60 | 23.45 | 32.50 | passed / passed |
| [runAmbientPreparation](bench-results/hex-lattice-enum/profiles/runAmbientPreparation.summary.json) | 2048 | 1087 | 1087.3 | 0.218 | 6.16 | 42.13 | 18.49 | 33.21 | passed / passed |
| [runAmbientReplay](bench-results/hex-lattice-enum/profiles/runAmbientReplay.summary.json) | 2048 | 884 | 898.0 | 1.107 | 5.43 | 27.38 | 37.67 | 29.52 | passed / passed |
| [runAmbientRetarget](bench-results/hex-lattice-enum/profiles/runAmbientRetarget.summary.json) | 2048 | 894 | 901.3 | 0.952 | 3.13 | 27.85 | 43.29 | 25.73 | passed / passed |
| [runAmbientShortest](bench-results/hex-lattice-enum/profiles/runAmbientShortest.summary.json) | 2048 | 670 | 672.5 | 0.659 | 5.67 | 29.55 | 35.22 | 29.55 | passed / passed |
| [runAmbientTies](bench-results/hex-lattice-enum/profiles/runAmbientTies.summary.json) | 2048 | 1020 | 1025.0 | 0.449 | 2.94 | 33.14 | 35.10 | 28.82 | passed / passed |
| [runCube](bench-results/hex-lattice-enum/profiles/runCube.summary.json) | 13 | 1067 | 1077.3 | 0.971 | 12.18 | 17.71 | 31.68 | 37.96 | passed / passed |
| [runHeight](bench-results/hex-lattice-enum/profiles/runHeight.summary.json) | 8/64/256 bits | 2618 | 2634.9 | 0.975 | 0.73 | 36.94 | 47.56 | 14.29 | passed / passed |
| [runRadius](bench-results/hex-lattice-enum/profiles/runRadius.summary.json) | 2048 | 675 | 685.2 | 1.300 | 9.33 | 22.96 | 33.48 | 33.63 | passed / passed |
| [runRank](bench-results/hex-lattice-enum/profiles/runRank.summary.json) | 128 | 566 | 566.5 | 0.160 | 5.12 | 24.73 | 36.22 | 33.22 | passed / passed |
| [runShear](bench-results/hex-lattice-enum/profiles/runShear.summary.json) | 128 | 599 | 607.7 | 0.755 | 6.18 | 42.90 | 32.72 | 18.20 | passed / passed |

Traversal (`traverseAux`, `children`) dominates the search profiles, with
reconstruction and exact distance arithmetic inside it. Its rational operations
spend much of their leaf time in GMP and allocation. Preparation/retargeting
and replay have their own registrations and profiles, so their scans are
attributed separately. LLL's reduction and checked coordinate recovery are
covered by `runAmbientLLL`; the input profile is dominated by Gram data and
array construction. The shear profile attributes about one fifth of inclusive
samples to `Data.centreImpl`; its fixed-rank quadratic node-growth model covers
that cost. Bounds and coefficient iteration each account for roughly one
percent there, so a separate microbenchmark is not warranted by this profile.

The codec profiles attribute string/list processing to encoding and bounded
parsing. The coefficient-height fixed control includes expensive decimal
conversion in its result checksum: about four fifths of its inclusive samples
are checksum work. Its timing is therefore labelled a fixed output/latency
anchor, and is not used to claim a bit-complexity model for search. Its retained
stacks also attribute the traversal, reconstruction and distance work. Ambient
and rank/output ladders supply the search complexity evidence independently.
No earlier `perf` call-stack result is used: that profiler could resolve leaf
instruction addresses on this host but lost the timed worker's DWARF stacks.

```sh
# Checkout the sampler revision recorded in profiles/manifest.json.
export LEAN_BENCH_SAMPLY_HOME=/path/to/lean-bench-samply
python3 scripts/profile/lattice_enum_profile.py \
  --results reports/bench-results/hex-lattice-enum/scientific-initial.json \
  --out /tmp/lattice-profiles
```

## Concerns
