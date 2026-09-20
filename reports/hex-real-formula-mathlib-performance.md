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
| adapter | 7907.29 | 8047.03 | 146.73 | 3.38–1422.42 |
| alternation | 2145.35 | 2393.89 | 261.04 | 84.91–501.91 |
| normalization | 2088.34 | 2167.02 | -5.17 | -44.11–294.11 |
| parameterized | 2159.94 | 2370.31 | 198.92 | 156.78–263.96 |

All raw pairs (A = matched baseline; B = candidate):

| Pair | Round | Order | A ms | B ms | B−A ms |
| --- | ---: | --- | ---: | ---: | ---: |
| adapter | 1 | AB | 7749.04 | 7845.65 | 96.61 |
| adapter | 2 | BA | 7861.47 | 7864.85 | 3.38 |
| adapter | 3 | AB | 7953.12 | 9375.54 | 1422.42 |
| adapter | 4 | BA | 8032.35 | 8229.21 | 196.86 |
| alternation | 1 | AB | 2124.49 | 2332.44 | 207.95 |
| alternation | 2 | BA | 1953.43 | 2455.34 | 501.91 |
| alternation | 3 | AB | 2166.20 | 2480.34 | 314.14 |
| alternation | 4 | BA | 2232.77 | 2317.68 | 84.91 |
| normalization | 1 | AB | 2033.31 | 2056.88 | 23.57 |
| normalization | 2 | BA | 1940.67 | 2234.78 | 294.11 |
| normalization | 3 | AB | 2366.14 | 2332.24 | -33.91 |
| normalization | 4 | BA | 2143.37 | 2099.26 | -44.11 |
| parameterized | 1 | AB | 1941.75 | 2147.88 | 206.13 |
| parameterized | 2 | BA | 2232.18 | 2496.14 | 263.96 |
| parameterized | 3 | AB | 2447.22 | 2638.92 | 191.70 |
| parameterized | 4 | BA | 2087.70 | 2244.48 | 156.78 |

Negative paired deltas occur for normalization. These observations
do not establish a speedup or a stable positive overhead for those pairs.
Every pair is retained.

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
[the complete fresh-module artifact](data/hex-real-formula/proofs-bounded.json), with
repository/dependency revisions and cleanliness, exact source hashes, commands,
compiler evidence and host context. The compiled core's five sampled families
are in the [core report](hex-real-formula-performance.md).

The measurement uses the clean implementation commit
`1473963a960b6c773ec9566a0b04a38b98c77991`, Lean 4.34.0, and the shared host
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

Additional completed runs are retained with their own source provenance: [first](data/hex-real-formula/proofs.json), [second](data/hex-real-formula/proofs-final.json).
