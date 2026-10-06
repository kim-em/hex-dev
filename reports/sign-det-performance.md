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
| Different defining polynomials sharing a root | `SharedRoots.runOne`, `runTwo`, `runThree`; [timings](sign-det-shared-roots.md), [construction inventory](sign-det-shared-root-work.md) | Actual equality and strict comparison, including common-factor removal and re-encoding. Three small rational cases; all eleven returned table constructions are counted. |
| Coefficient height | `Height.runReduce`, `Height.runCheck`; [height evidence](sign-det-height-model.md) | Growing coefficient bits at fixed degree/support, with a separately justified linear-bit model for positive-monomial normalization and its checking. Not an end-to-end bit bound. |
| Nested coefficient arithmetic | `NestedSigns.runSign`, `NestedTables.runProduce1`, `runTree1`, `runProduce2`, `runTree2`; [scalar signs](sign-det-nested-signs.md), [nested tables](sign-det-nested-tables.md) | Extension depth and actual coefficient constructors; full production/tree replay at depths one and two over growing query lists. |
| Number-field coefficient signs | [Field-coordinate signs](../bench-results/field-sign/README.md), [common-field consumers](../bench-results/field-sign/common-fields/README.md) | Canonical conversion versus the proved interval-sign operation, including cubic coordinates and independently constructed common quartic fields. Fixed end-to-end comparisons, with separate source bindings. |
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
these inputs. The historical joint collections include the direct reference's
extra powers; the [power correction and small current comparison](sign-det-poly-power.md)
retain all new observations. Both comparisons include checks,
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

The shared-root examples compare sqrt(2), described by X²−2 and by that
polynomial times additional linear factors, and compare it with an integer
root. The retained median times are 22.03, 43.26 and 109.01 ms at degrees
3, 4 and 5 on their recorded host. The corresponding whole-child resident
peaks are about 72 MiB, including startup and harness tuning. These are
baseline observations before the polynomial-power correction, with no
asymptotic timing claim. These callbacks use reduced moments only; that power
correction does not change their computation path. In all three cases P divides
Q, so the common polynomial is Q itself. A common polynomial strictly larger
than both inputs is not measured by this collection. The untimed inventory
independently checks the actual selected intervals and the orders returned
by both comparisons; it is a diagnostic
source snapshot, not a replacement timed binary.

Those callbacks construct eleven squarefree chains and 223, 304 or 451
query chains, plus two explicit polynomial gcds and six explicit exact
divisions in the common-product constructors. Divisions internal to gcd,
query preprocessing, positive pseudo-division, coefficient normalization and
subsequent replay are outside those counts. This exposes repeated domain
preparation and re-encoding without labelling construction counts as a
complete timing decomposition.
The guards are separately enumerated in the inventory report; derivative
construction is not counted, and its SPEC accounting remains open.

The number-field path already uses the proved interval operation
`QAdjoin.signApprox` rather than converting each coordinate to a canonical
algebraic number. The close-value scalar comparison records 54.805 ms versus
2.334 s for twenty signs. A separate complete common-field comparison records
a median within-pair canonical/interval ratio of 1.252, with one of six pairs
favouring canonical conversion. The reports bind those observations to their
different source versions; the larger scalar ratio must not be attributed
to the common-field workload or the current per-call reality check.

## Intermediate operand bounds

Stored witness maxima alone are not peaks of transient arithmetic. For the
complete integer matrix callbacks (`MaximalMatrix.runCheck`,
`runCheckDimension` and `runTensorCheck`), their actual summations give a useful
independent bound. Let B_A be the largest bit length of a supplied inverse
entry, B_c that of a supplied count, B_d that of the denominator and B_t that
of a supplied moment value (`values` entry), with zero assigned zero bits.
The column guard runs before any product, so every moment entry used is
−1, 0 or 1. The actual naive `mulImpl`/`dotProductImpl` folds sum at most r
terms. Every partial inverse-product sum therefore has at most
B_A+ceil(log₂ r) bits, and every partial count-product sum has at most
B_c+ceil(log₂ r) bits. The checker’s coefficient integers, including products
and partial sums, have bit length bounded by the maximum of these two bounds,
B_d, B_t and 1. This follows from the actual r-term sums in `System.check`;
it is not a measured maximum or a bound for rational inverse construction.

For the complete tensor inputs r=3ˢ, counts are one, inverse entries have at
most s+1 bits and the denominator is 2ˢ. This gives bounds of 14, 17, 20 and
22 bits at dimensions 243, 729, 2187 and 6561. These bounds include transient
partial sums even when the final entry cancels to zero. This checker performs
no polynomial gcd, exact polynomial division or derivative construction.
Its large dimensions therefore do not measure those costs.

The separate `Height.runReduce` and `Height.runCheck` callbacks have an
equally restricted source bound, excluding their `Height.phaseInput`
preparation. Their three inputs are cX², cX and c, where c=2ᴴ−1. Their degrees are
below the head’s degree three. Each step first multiplies the query by the
constant polynomial 1; all three positive pseudo-divisions then return
immediately with multiplier one and quotient zero. Three positive
normalizations produce X², X and 1. Their check reconstructs the monomials
and tests zero differences. Every rational coefficient operand in those
operations has numerator and denominator of at most H bits; before rational
cancellation a binary arithmetic operation needs at most 2H+1 bits. This is
an independent conservative bound, not an observed peak. It excludes input
construction and backend scratch storage. Witness hashing and magnitude
copies for bit-length fingerprints also operate on at most H-bit integers.
Neither callback searches for a
polynomial gcd or computes a derivative; polynomial quotient iteration does
not run on these inputs. Rational normalization still performs integer gcds.

Finite products over core `Rat` also admit a source bound without
instrumenting every arithmetic operation. Suppose the operand polynomials
passed to `moment` have degree at most D and their coefficient numerators and
denominators have at most B bits, with B≥1. For a product of L factors,
counting repeated factors separately, put W=1 if L=0, and otherwise

W = B·L·(D+1) + (L−1)·ceil(log₂(D+1)) + 1.

This covers every product the constructor forms: each is a product of a
sub-multiset of the L factors, including squares, the seed 1 and multiplication
by 1. Use the product Q of all input coefficient denominators as a common
denominator. It has at most B·L·(D+1) bits, and every normalized coefficient
denominator divides Q. An expanded term's numerator over Q multiplies its
selected numerators by the remaining denominators, so has at most that same
bit bound. For a coefficient there are at most (D+1)^(L−1) terms: choosing
L−1 exponents determines the last one. This also bounds any partial sum,
including one that later cancels. Its normalized numerator is no larger in
absolute value than its numerator over Q.

Core `Rat.mul` cancels common factors before multiplying. `Rat.add` uses the
least common multiple of the operands' denominators, which divides Q; its
cross products and numerator sum obey the same term bound. Thus W bounds
both normalized coefficients and pre-cancellation coefficient integers in
these product calculations. It does not bound polynomial division, a gcd
search or backend scratch storage. For the direct moment constructor after
the polynomial-power correction, L is the sum of the ternary exponents and
is at most twice the query count. This claim does not describe the historical
discarded powers before that fix. The operands are `QueryReduction.operands`,
which need not be the original user queries.

For an individual `ReductionStep.check` identity, suppose p, prev, factor,
quotient and next each have degree at most D. The numerators and denominators
of all their coefficients and of leftScale and rightScale have at most B
bits. D explicitly includes the supplied quotient's degree; the checker does
not impose a degree guard on that quotient. Put k=D+1 and
U=2B·k+ceil(log₂ k)+1. This is the preceding W bound for two factors: each
coefficient accumulates at most k terms over a common denominator containing
at most 2k input denominators. The same least-common-multiple argument bounds
its partial sums and pre-cancellation coefficient arithmetic by U.

Scaling the left product `prev*factor` adds at most B bits. Adding the right
product `quotient*p` to the scaled remainder `rightScale*next` adds at most
2B+1 bits. Generic numerator/denominator bounds for subtraction then bound
the zero difference by 2U+3B+2 bits, including its pre-cancellation integers.
This includes transient values that disappear in a successful identity
check. It concerns that finite check, not production of its witnesses.

These bounds cover the named integer matrix callbacks, height-normalization
callbacks, direct moment products and individual reduction-step identity
checks. They do not establish peak arithmetic sizes for general Sturm chains,
joint table production or nested coefficient arithmetic, and do not turn
allocator request sizes into coefficient-bit observations.

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

The shared-root timings and construction counts are supplied by the linked
records. Those shared-factor inputs have P dividing Q. The separate joint
family has coprime heads and a common polynomial larger than both; neither
collection measures a common factor proper in both inputs. Source bounds
exist only for the four named finite operations.
Transient sizes in chain/pseudo-division production, rank certificates,
common-product gcds, leaf rational solves and nested coefficient arithmetic
are neither bounded nor measured here; this SPEC requirement remains open.
Stored witness maxima must not be called those peaks.

Merged #10641 removed canonical conversion from the per-sign path
(`signField` calls `QAdjoin.signApprox`). The linked fixed comparisons record
its effect on those inputs only. A persistent sign cache across callbacks and
the claimed interpreter bottleneck under #10635 are not resolved by them;
neither those fixed comparisons nor the small rational families establish
general number-field scaling.
