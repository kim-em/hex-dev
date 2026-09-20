# Real-formula proof and reification performance

Four fresh-module pairs exercise parameterized reification, quantified Boolean
normalization, a semantic normalization theorem, and the RCF adapter. Each
candidate has a matched import baseline and four completed adjacent measurements.
This is proof-track evidence; no LeanBench executable imports Mathlib and no
compiler-process sampling profile is used.

## Bench targets

The source modules are built by `HexRealFormulaProofProbe`. The first three
pairs belong to `HexRealFormulaMathlib`; the adapter belongs to `HexRCF`.
They replace compiled measurements for meta reification, emitted equivalence
proofs, semantic theorem use, and Mathlib-facing correspondence respectively.
They do not measure RCF search or the compilation of the entire generic theorem
library: imported dependencies are warmed before the fresh-module pair.

| Pair | Candidate module | Matched baseline |
| --- | --- | --- |
| adapter | `HexRCF.RealFormulaProbe.Adapter` | `HexRCF.RealFormulaProbe.Baseline` |
| alternation | `HexRealFormulaMathlib.ProofProbe.Alternation` | `HexRealFormulaMathlib.ProofProbe.Baseline` |
| normalization | `HexRealFormulaMathlib.ProofProbe.Normalization` | `HexRealFormulaMathlib.ProofProbe.Baseline` |
| parameterized | `HexRealFormulaMathlib.ProofProbe.Parameterized` | `HexRealFormulaMathlib.ProofProbe.Baseline` |

The parameterized source is `∃ x : ℝ, x²/2 + a*x ≤ 3/2`, with `a` explicitly
free. The alternation source combines existential and universal subformulas in
a biconditional. Both probes run the public reifier, check its proof in the
kernel, and emit an actual theorem declaration of the returned equivalence.
They do not assert the source proposition itself. The normalization probe
applies `Scoped.toPrenex_correct` to a negated quantified biconditional for
every free valuation. The adapter probe applies `ofSentence_correct` to the
cubic `x³-x-1=0` under RCF's half-open `(1,2]` existential.

## Verdicts

The harness reports `measurement_state: complete`, `release_quality: true`,
with no validity exceptions. These are fixed fresh-build observations, not
asymptotic verdicts or tactic time budgets. Every completed pair is retained;
no host-load filter or retry-until-clean rule is used.

| Pair | Baseline median ms | Candidate median ms | Median paired delta ms | Paired delta range ms |
| --- | ---: | ---: | ---: | --- |
| adapter | 7570.43 | 7745.72 | 129.62 | -559.94–271.96 |
| alternation | 2043.57 | 2246.85 | 204.99 | 195.60–317.14 |
| normalization | 2033.35 | 2142.14 | 111.72 | 105.00–116.05 |
| parameterized | 2051.49 | 2244.44 | 192.95 | 115.66–209.29 |

All raw pairs (A = matched baseline; B = candidate):

| Pair | Round | Order | A ms | B ms | B−A ms |
| --- | ---: | --- | ---: | ---: | ---: |
| adapter | 1 | AB | 8279.78 | 7719.84 | -559.94 |
| adapter | 2 | BA | 7631.74 | 7771.61 | 139.87 |
| adapter | 3 | AB | 7509.12 | 7781.08 | 271.96 |
| adapter | 4 | BA | 7495.36 | 7614.73 | 119.37 |
| alternation | 1 | AB | 2053.43 | 2264.39 | 210.96 |
| alternation | 2 | BA | 2029.66 | 2228.68 | 199.02 |
| alternation | 3 | AB | 2078.10 | 2395.24 | 317.14 |
| alternation | 4 | BA | 2033.72 | 2229.31 | 195.60 |
| normalization | 1 | AB | 2034.08 | 2139.08 | 105.00 |
| normalization | 2 | BA | 2025.88 | 2137.81 | 111.93 |
| normalization | 3 | AB | 2033.01 | 2149.06 | 116.05 |
| normalization | 4 | BA | 2033.69 | 2145.21 | 111.52 |
| parameterized | 1 | AB | 2045.60 | 2245.30 | 199.70 |
| parameterized | 2 | BA | 2036.91 | 2152.58 | 115.66 |
| parameterized | 3 | AB | 2067.51 | 2276.80 | 209.29 |
| parameterized | 4 | BA | 2057.38 | 2243.59 | 186.21 |

The adapter delta changes sign across pairs, so these samples do not resolve
a stable positive adapter overhead. Every pair remains in the report.

Every candidate theorem's reported axiom set is exactly
`[propext, Classical.choice, Quot.sound]`. The raw artifact retains compiler
output, axiom checks, artifact sizes, peak RSS, CPU accounting and all samples.
There are no source or dependency changes during measurement.

## Comparator ratios

The baseline controls imports and ordinary fresh-module overhead. It is not
an alternative QE tactic or semantic solver. Paired deltas describe the added
work of these particular modules; small or negative deltas are not speedup
claims. No external performance comparator is specified for this frontend.

## Profile and provenance

Timed-region sampling does not apply to proof-track builds. The substitute is
[the complete fresh-module artifact](data/hex-real-formula/proofs.json), with
repository/dependency revisions and cleanliness, exact source hashes, commands,
compiler evidence and host context. The compiled core's five sampled families
are in the [core report](hex-real-formula-performance.md).

The measurement uses the clean implementation commit
`34271e57d8971f9cd07474568f144e9258d30f9f`, Lean 4.34.0, and the shared host
`chungus2` (AMD EPYC 9455, x86-64 Linux). An automatically leased CPU is pinned
for the run; its identity and sibling activity are recorded in the artifact.
Each round rotates pair order; adjacent arm order alternates AB/BA. All four
rounds are retained. Wall times are observations on this host.

Reproduce from a clean checkout with:

```sh
python3 scripts/bench/real_formula_sweep.py proofs --output /tmp/real-formula-proofs.json
```

The harness builds warmed dependencies, removes only each measured module's
generated artifacts, and invokes `lake build +<module>:olean`. The candidate
and baseline modules contain no clocks, timing loops, or benchmark main.

## Concerns

The evidence covers four fixed integration cases. It does not establish a
complexity law for arbitrary source expressions, expanded biconditionals, or
prenex normalization. Those remain output-sensitive and budgeted. Independent
review and dependency gates remain separate from the measurements; the new
libraries' phase prefix is 1, including the currently Phase-1 HexReflect
prerequisites. No unfulfilled implementation proof obligation is hidden by
that phase status.

The atom-coordinate proofs enumerate the entire sealed variable map for each
atom; these small probes do not establish scaling for many atoms and variables.
The public reifier checks its returned proof, and declaring it as a theorem
checks it again. Returned formulas also contain tree-backed polynomial
projection expressions. The conformance suite composes a returned formula with
`toSentence?` and `decide_sound` in the kernel, but replay of that conversion may
be expensive for large inputs. The validated list evaluator has a direct
correctness theorem; a list-only reifier-to-RCF replay path is not provided.
