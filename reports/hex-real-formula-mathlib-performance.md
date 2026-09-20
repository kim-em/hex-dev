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
| adapter | 10238.17 | 11304.18 | 1978.65 | -1437.02–3604.20 |
| alternation | 3145.96 | 3823.01 | 935.64 | 412.64–1330.44 |
| normalization | 2622.88 | 3300.04 | 687.82 | 48.66–2316.06 |
| parameterized | 3474.69 | 3295.94 | -445.53 | -692.36–-43.67 |

All raw pairs (A = matched baseline; B = candidate):

| Pair | Round | Order | A ms | B ms | B−A ms |
| --- | ---: | --- | ---: | ---: | ---: |
| adapter | 1 | AB | 15353.04 | 18957.25 | 3604.20 |
| adapter | 2 | BA | 10747.59 | 9310.57 | -1437.02 |
| adapter | 3 | AB | 9728.74 | 11466.33 | 1737.59 |
| adapter | 4 | BA | 8922.32 | 11142.03 | 2219.71 |
| alternation | 1 | AB | 3397.89 | 3810.54 | 412.64 |
| alternation | 2 | BA | 6183.68 | 7113.51 | 929.83 |
| alternation | 3 | AB | 2894.03 | 3835.48 | 941.45 |
| alternation | 4 | BA | 2273.96 | 3604.40 | 1330.44 |
| normalization | 1 | AB | 3131.83 | 3516.16 | 384.33 |
| normalization | 2 | BA | 2695.41 | 5011.47 | 2316.06 |
| normalization | 3 | AB | 2092.60 | 3083.92 | 991.32 |
| normalization | 4 | BA | 2550.36 | 2599.02 | 48.66 |
| parameterized | 1 | AB | 4325.07 | 3747.83 | -577.24 |
| parameterized | 2 | BA | 3203.33 | 2889.51 | -313.82 |
| parameterized | 3 | AB | 3746.05 | 3702.38 | -43.67 |
| parameterized | 4 | BA | 3159.40 | 2467.04 | -692.36 |

The parameterized pair has both negative and positive deltas, so these samples
do not resolve a stable positive reification overhead. Every pair is retained.

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
[the complete fresh-module artifact](data/hex-real-formula/proofs-final.json), with
repository/dependency revisions and cleanliness, exact source hashes, commands,
compiler evidence and host context. The compiled core's five sampled families
are in the [core report](hex-real-formula-performance.md).

The measurement uses the clean implementation commit
`74b02514d3e6fa41140171d242fe06ee8e253273`, Lean 4.34.0, and the shared host
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

[The earlier completed run](data/hex-real-formula/proofs.json) is retained with its own source provenance.
