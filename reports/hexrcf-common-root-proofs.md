# Source tactic proofs with repeated and shared roots

This experiment checks how the fixed-field tactic handles repeated roots and
additional polynomials sharing roots, while retaining the same degree-four
normalized carrier. All three fresh modules use the actual `rcf` command and
ordinary-kernel proof acceptance. The comparisons change their source input;
they do not compare solvers or isolate one parameter for a complexity model.

The [modules](../bench/HexRCF/ProofProbe/CommonRoots/Simple.lean) prove:

```lean
∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2
∃ x : ℝ, (x ^ 2 - Real.sqrt 2) ^ 2 = 0 ∧ 1 < x ∧ x < 2
∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧
  (x ^ 2 - Real.sqrt 2) * (x - 1) = 0 ∧ 1 < x ∧ x < 2
```

They use identical imports and options: monic carrier, indexed lookup and
interval signs; reduced literals, combined replay and generator refinement
are disabled. They each authenticate the single selected √2 source coefficient.
The repeated input changes maximum atom degree from two to four and product
degree from four to six, while retaining three atoms. The shared input changes
maximum atom degree from two to three, product degree from four to seven and
atom count from three to four. These targets have the same principal zero set,
but are distinct Lean statements. The additional factor x−1 supplies no new
carrier root because the existing strict lower-bound atom already uses it.

## Retained measurements

The clean measured and audited source is
[`22c5010fe54a41b681370680916e2f71cdf7e0d0`](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-common-roots-22c5010fe).
The [raw report](bench-results/hex-rcf-common-root-proofs-22c5010fe-chungus2.json)
and [incremental samples](bench-results/hex-rcf-common-root-proofs-22c5010fe-chungus2.json.samples.jsonl)
retain all 16 completed arms and full compiler output. Source and dependency
identities remained unchanged. Four trial-major rounds rotate two adjacent
pairs. Each pair occupies each position twice and uses two AB and two BA
rounds. No completed sample was excluded and no unchanged rerun was taken.

The AMD EPYC 9455 shared-host runner automatically leased CPU 88 (SMT sibling
40), with one Lean thread. Recorded activity is context. The 120-second
per-arm timeout is an operational safeguard. Imports and dependencies are
warmed; measured costs include source coefficient preparation, certificate
production, quotation and fresh-module kernel acceptance.

| Input pair | Simple median s | Candidate median s | Median paired change s | Private proof bytes | Median peak RSS KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| Repeated polynomial | 15.084 | 16.353 | +0.890 | 646400 → 650560 | 4022352 → 4045812 |
| Additional shared polynomial | 14.259 | 15.867 | +1.266 | 646400 → 667880 | 4035706 → 4174302 |

The reference is rebuilt within each pair. Paired medians need not equal
changes between marginal medians. Repeated-input signed differences are
−8.198, +1.396, +4.534 and +0.384 seconds. Shared-input differences are
−0.494, +1.906, +0.627 and +2.670 seconds. Every observation remains retained.
The positive paired medians are input-specific observations, not a general
scaling law or isolated cost of repeated/common roots. No pooling or fitted
model is used. Both pairs report `no-comparable-control`.

All 16 quoted theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`. Native production proposes data and supplies no proof premise.

## Carrier and proof audit

The [audit](data/hexrcf-common-root-signs/22c5010fe/audit.json) retains
[complete compiler output](data/hexrcf-common-root-signs/22c5010fe/compiler-output.json).
All three probe source hashes match the timed source; final artifact hashes
are unchanged across the separate audit. These are not per-arm hash captures.
The traversal requires the actual `FieldBuild.Result.checkExists_sound` proof
and exactly one literal solver envelope with five carrier coefficients and
four root sections. Every case has four sections and five sectors. The first
two have three root-sign rows; the shared input has four. None uses the
multi-source `CommonPresentation.checkPolynomials_sound` path: each has one
irrational source coefficient in a single selected field.

| Input | Interval/full-query entries | Unique expressions | Expanded local-reference nodes |
| --- | ---: | ---: | ---: |
| Simple | 126 / 0 | 17567 | 831043799068 |
| Repeated | 126 / 0 | 17725 | 835066928034 |
| Shared | 139 / 0 | 18137 | 980744958554 |

All three have seven reachable local declarations, three distinct conjunction
constructors and no refinement window. Equality is `Lean.Expr.eqv`, alpha
equivalence with binder annotations ignored. Imported bodies remain leaves;
expansion counts local declaration types and bodies at every reference,
without reductions or let substitution. These are syntactic counts, not
physical allocation, kernel execution counts or byte attribution.

This study does not measure arbitrary field degree, nested extension depth,
multi-source common-field construction or a general infinitesimal realization.
The [precision acceptance study](hexrcf-precision-production-proofs.md) and
[window study](hexrcf-window-proofs.md) retain different source pins and scopes.

Reproduce on the retained source with:

```sh
python3 scripts/bench/hexrcf_common_root_proofs.py --timeout 120
```
