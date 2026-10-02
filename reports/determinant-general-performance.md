# Determinant proof performance

The shipped symbolic evaluator succeeds on all five measured examples. These
corrected measurements support a modest Hex advantage on the 10×10 rank-one case
and near parity on the dependent-row fraction 6×6. Small-case differences are
sensitive to build variation. The original quadratic 4×4 has a lower Hex median
after baseline subtraction, but its complete-file medians point the other way;
this run does not establish a robust speed advantage there. The result-producing
3×3 is also too small to draw a strong conclusion from these differences.

## Proof work after imports

Each value is the median of six complete proof-file builds minus their adjacent
import-only builds. Both arms and both baselines have identical imports. Every
proof build includes statement elaboration, proof construction, output cleanup,
Lean kernel checking, ordinary linting and serialization. Result-producing
`def` probes also include the compiler work requested by their olean build. Axiom audits and
profiling are outside the timing samples.

| Example | Mathlib | Hex |
|---|---:|---:|
| Original 4×4 quadratic matrix (two variables) | 1.123 s | 1.010 s |
| 5×5 products of fractions, determinant zero | 0.099 s | 0.103 s |
| 6×6 fractions with a dependent row | 0.198 s | 0.202 s |
| 10×10 rank-one matrix (one variable) | 1.101 s | 0.991 s |
| Compute a nonzero symbolic 3×3 value | 0.012 s | 0.025 s |

Negative individual differences are retained: one Mathlib product-fraction
sample, one Hex product-fraction sample, and one sample in each arm of the 3×3
result comparison are negative. They mean variation between separate builds
exceeded the small proof increment, not that proof work takes negative time.
No host-activity threshold was used to discard samples or wait for an idle CPU.

All six 10×10 Hex differences lie between 0.988 and 1.006 seconds, versus
0.902–1.117 seconds for Mathlib; Hex is faster in five of the six paired
baseline-subtracted observations. The 6×6 medians differ by only 4 ms; Hex is slower in four pairs and faster
in two. Individual differences span 0.132–0.304 seconds for Mathlib and
0.125–0.399 seconds for Hex. These are host-specific observations, not a universal
speed claim or a reason to introduce matrix-family dispatch.

## Complete fresh-file builds

These medians include Lake startup and the common imports as well as theorem
work. They are medians of raw builds, not the sum of independently computed
baseline and difference medians.

| Example | Mathlib | Hex |
|---|---:|---:|
| Original 4×4 quadratic matrix (two variables) | 3.752 s | 3.833 s |
| 5×5 products of fractions, determinant zero | 2.726 s | 2.721 s |
| 6×6 fractions with a dependent row | 2.811 s | 2.826 s |
| 10×10 rank-one matrix (one variable) | 3.714 s | 3.619 s |
| Compute a nonzero symbolic 3×3 value | 2.646 s | 2.688 s |

## Separate import costs

The runner also measures each interface's natural import-only file, alternating
order six times. These times include Lake startup and loading dependencies; they
are not subtracted from the matched-import proof samples above.

| Import-only file | Median fresh build |
|---|---:|
| Mathlib | 1.727 s |
| Hex | 2.615 s |

Mathlib imports `Mathlib.Tactic.NormDet` and `Mathlib.Tactic.Ring`; Hex imports
`HexPolyDetMathlib`. The extra Hex import cost matters for fresh files. It is
separate from the cost of another determinant in an already loaded environment.

## Protocol and source

The run used six adjacent alternating AB/BA pairs, serially on automatically
leased CPU 22, with one Lean thread. The selected cases were
`OriginalQuadratic4`, `Products5`, `Independent6`, `RankOne10` and
`ResultSymbolic3`. Equality comparison uses unchanged Mathlib
`simp only [norm_det] <;> ring`. That is unchanged tactic code running in the
common Hex-importing environment, not in a minimal Mathlib-only environment.
Extra imports may affect elaboration and simplification even after subtracting
import-only time, so these data do not establish the same advantage for a
Mathlib-only user. No separate natural-import proof control was collected.
Result production uses `det%` versus determinant
simplification constructing a certified value; neither receives the answer.

All ten separate axiom audits passed with exactly `propext`, `Classical.choice`
and `Quot.sound`. All 60 proof samples and 12 standalone import samples completed.
The full run, including preparation, audits and baselines, used 438.9 seconds
of a 600-second allowance. No process reached its 60-second limit. No repeat or
extra profiling was needed for this report. The rest of the maintained corpus is
not timed by this run; local compilation checks do not substitute for timings.

Base revision: `2cf1798cff8dabd831431f42498dac4aee3ed894`, with the probe/runner changes
in #10495. The determinant implementation is unchanged. Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean to `v4.34.1`. The raw JSON
records the working-tree source hashes, dependency states, host observations,
compiler output, every completed sample and the executed protocol.

The source archive preserves the exact measured probes and runner. The final
runner additionally binds audit parsing to the exact exported declaration name,
builds each proof before auditing with separate process limits, and distinguishes
aggregate-deadline truncation from a full 60-second case timeout. It retains
warm-up failures and exits unsuccessfully for incomplete runs. All ten retained
audit outputs were revalidated against the exact-declaration check. These runner
changes affect preparation and failure handling, not the timed proof commands
or the successful samples above; the archive records the runner actually used.

`OriginalQuadratic4` restores the exact matrix and target from
`dccd276f7:bench/HexPolyDetMathlib/ProofProbe/N4K2D2S4Hex.lean` (#10320).
The previous `Quadratic4` was a simpler one-variable tridiagonal matrix, retained
as `Tridiagonal4`; its result-producing counterpart is `ResultTridiagonal4`.
The old [#10432 report](determinant-general-issue-10432.md) includes axiom-audit
costs and is retained as historical evidence, not a tactic-speed comparison.

- [CI-built proof examples](../SPEC/proof-examples.md)
- [CI-built proof examples](../SPEC/proof-examples.md)
- [Probe layout and reproduction command](../bench/HexPolyDetMathlib/ProofProbe/README.md)
