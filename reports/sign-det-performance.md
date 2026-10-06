# Sign-determination performance evidence

This report covers the BKR/Thom library's compiled operations and ordinary
kernel examples. Its claims are limited to the recorded source snapshots,
inputs and hosts. The individual reports retain exact commands, declarations,
raw observations, checksums, source reconstruction and coverage limits.
A coefficient-operation bound is not a wall-time law for arbitrary coefficient
fields. No result here is a bound for quantifier elimination or the `rcf` tactic.

## Bench targets

| Work being measured | Registrations and evidence | Scope |
| --- | --- | --- |
| Many queries with sparse realized support | `runProduce`, `runDirect`, `runTree`, `runGraph`; [sparse tables](sign-det-sparse-model.md) | Repeated queries on a two-root head; production/tree work has arity volume s(log₂s+1), while shared graph replay has total arity O(s). |
| Components of that table calculation | `runQueries`, `runProducts`, `runMatrices`, `runSolvers`, `runSigns`; [phase costs](sign-det-phase-model.md) | Actual prepared queries, products, matrix construction/solving and coefficient signs. Components overlap and must not be summed as independent phases. |
| Complete ternary support | [maximal-support inputs](sign-det-maximal-inputs.md), [matrix evidence](sign-det-maximal-matrices.md), `MaximalMatrix.runTensorCheck`; [wider checking](sign-det-matrix-wide.md) | Full BKR root/sign agreement at small inputs; large integer inverse/count checking at complete dimensions. The large matrix checker does not measure full root production. |
| Joint derivative and source constraints | `Joint.runCompletion`, `runComparison`, `runReduced`, `runDirect`, `runCheckReduced`, `runCheckDirect`; [joint evidence](sign-det-joint-performance.md) | Two-root binomial heads, growing degrees, derivative queries, coefficient/witness bits and certificate bytes. Cubic formulas count coefficient operations; fitted timing verdicts are descriptive. |
| Coefficient height | `Height.runReduce`, `Height.runCheck`; [height evidence](sign-det-height-model.md) | Growing coefficient bits at fixed degree/support, with a separately justified linear-bit model for positive-monomial normalization and its checking. Not an end-to-end bit bound. |
| Nested coefficient arithmetic | `NestedSigns.runSign`, `NestedTables.runProduce1`, `runTree1`, `runProduce2`, `runTree2`; [scalar signs](sign-det-nested-signs.md), [nested tables](sign-det-nested-tables.md) | Extension depth and actual coefficient constructors; full production/tree replay at depths one and two over growing query lists. |
| Small reduced/full reference agreement | `runSmallReduced`, `runSmallFull`; [paired comparison](sign-det-compare-model.md) | Identical small inputs, complete answers and adjacent timings; the auxiliary full arm is not the production inversion path. |

The bench executable is Mathlib-free. Its `list` and `verify` commands are
required CI checks; `verify` supplies correctness/bitrot evidence, not timing
or complexity acceptance. Fixed one-to-three-column reference solves check
answers and make no timing claim. Large rational reference inversion is not
production's matrix-inversion workload: production inverts leaf systems and
transports parent inverses. Parent rank work remains part of production.

## Verdicts and comparisons

The sparse whole-table and component collections retain complete schedules
consistent with their independently derived models. Height normalization and
its checker retain complete schedules consistent with the linear-bit model.
The nested scalar-sign finding is resolved by the actual constructor
recurrence, not by the earlier leaf-sign count. The original incorrect
prediction and all observations remain retained.

The earlier complete-support reference-inversion verdicts remain descriptive
auxiliary evidence. The integer matrix-checker finding has a separate
source/profile explanation for its cubic loop plus lower-order entry work;
its original two inconclusive verdicts remain unchanged. The proved small-power
optimization has its own controlled before/after comparison, distinct from
those old scaling measurements. Its exploratory comparison is retained with
its confounds disclosed.

Joint observations retain all original fitted verdicts. Their scope section
replaces the unsupported wall-time prediction with coefficient-operation
bounds and representative actual times. Reduced/direct table and replay
comparisons retain matching answers and complete adjacent schedules on their
recorded common domain. The interrupted wider collection is not a complete
production/replay comparison. It contributes only its completed operations
and explicitly partial output.

The wider nested-table evidence records all four production/replay families
on its prospectively declared range. Its timing range does not empirically
distinguish a linear term from the declared logarithmic factor; the source
arity-volume argument supplies that factor. No slope or tolerance is changed
to fit old points.

Reduced/full and reduced/direct ratios describe complete implementations on
these inputs. They include checks and the direct reference's extra powers,
and do not isolate a mathematical reduction step. External Z3 and FLINT
oracles independently check answers; their root/isolation operations are not
Lean matrix-solving or proof-checking baselines. No external speed ratio is
claimed by this report.

## Allocation, memory and attribution

[Joint](sign-det-joint-allocations.md), [matrix](sign-det-matrix-allocations.md),
[height](sign-det-height-allocations.md) and nested-table reports retain
operation-scoped allocation observations, with their covered allocator paths,
exact callbacks and native-result controls. Requested cumulative bytes are
not peak live bytes. The [method](sign-det-allocation-method.md) states the
interception limits. The [whole-process memory report](sign-det-process-memory.md)
separates native resident high-water marks from instrumented mapped-page
profiles, and includes startup and preparation. No live-object accounting or
isolated callback working-set claim follows from those observations.

Representative profiles cover sparse production, joint comparison, reference
matrix solving, actual integer matrix checking and nested coefficient signs.
They distinguish leaf cost from inclusive attribution and state when unwinding
failed. The joint source/profile record identifies rational normalization,
GMP integer construction and allocation; it does not price every coefficient
operation equally. No profile constant is fitted into a replacement timing law.

## Ordinary kernel evidence

CI builds the computational library, the companion and its development
headline proofs through `HexQuerySemantics`, including representative accepted
and rejected certificates. The declared companion proof-example roots retain
axiom guards. The [final conformance report](sign-det-final-conformance.md)
links independent root/sign oracles, actual nonquadratic coefficient fields,
common-field examples, noninjective representations, infinitesimals and
adversarial certificate/byte checks.

[Same-level replay](sign-det-proof-model.md) and [nested replay](sign-det-nested-kernel.md)
retain the measured costs of their particular proof strategies and matching
baselines. They are not universal proof-checking bounds or substitutes for
semantic correctness. The current in-process proof assembly and byte handling
have their own [byte evidence](sign-det-json-bytes.md) and correctness examples;
ordinary theorem applications require no blanket timing sweep.

## Concerns and phase attestation

This report does not itself advance a phase. Its evidence must be delivered,
reviewed and checked against the current API before attestation. In particular,
the wider nested records, matrix finding/optimization, joint interrupted
records and evidence-policy corrections are separately reviewed changes.
The dependency rule also requires prerequisite Sturm phase readiness, owned
by #10577. Rank readiness is already delivered under #10352; it is not a
reason to repeat its campaign.

The finite families do not cover every polynomial or coefficient field.
Large integer matrix checks are not full high-degree root computations;
positive-monomial normalization is not general Sturm-chain bit complexity;
two-root joint heads are not maximal-support inputs. Shared archived profiles
and memory observations retain their historical source/cache qualifications.
A genuine source-bound violation, unsuitable time/memory on intended inputs
or an unmet explicit comparison target remains a defect to investigate.
Expensive extra runs solely to cross a fitted-slope threshold are not required.

The joint timings and resident peaks below delimit practical use of the measured
implementation. The small library examples exercise low-degree polynomials;
degrees 3–15 are the representative joint workload, while degree 31 is a
stress case. Degree 63 comparison takes about 28 seconds, and degree 255 takes
about 29 minutes: neither is a suitable interactive demonstration. The
large sizes are retained diagnostic observations, not a claim of practical
high-degree comparison. No hard acceptance threshold was declared for these
sizes, so this judgement does not manufacture a retrospective timing gate.

The shared-root comparison performance case, peak intermediate (rather than
stored witness) coefficient bits, and counts of polynomial gcd calls still
need explicit evidence. The existing shared-root correctness examples do not
supply those measurements. #10635 separately records avoidable repeated sign
construction for actual number-field coefficients; the small rational families
here do not demonstrate that bottleneck has been resolved.
