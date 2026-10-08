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
| Complete ternary support | `maximalOne`, `maximalTwo`, `maximalThree`; [maximal-support workflows](sign-det-maximal-inputs.md), [matrix evidence](sign-det-maximal-matrices.md), `MaximalMatrix.runTensorCheck`; [wider checking](sign-det-matrix-wide.md) | Complete construction/production/reference/replay workflows at 3, 9 and 27 roots; separate large integer inverse/count checking. The large matrix checker does not measure full root production. |
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
The nested scalar-sign model finding is resolved by the actual constructor
recurrence, not by the earlier leaf-sign count. Repeated lower-field numeral
construction in HexRationalFn/HexOrderedFn remains an arithmetic cost; the
corrected declaration measures that implementation and claims no optimization.
The original incorrect
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
The inventory report separately enumerates the guards and bounds derivative
operations in descriptor extraction, chain construction and replay. Those
bounds concern the successful finite callbacks and include no timing prediction.

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

The integer rank-certificate producer has a source bound for its two passes
on each retained moment matrix. Let k be that matrix's column count. Its
entries are −1, 0 or 1. `Matrix.rankCert` uses the existing integer fraction-free
Gauss–Jordan implementation: first on the retained matrix, then on the original
selected pivot block augmented with an identity. Both initial matrices have
entries of absolute value at most one; each pass makes at most k pivot updates.
No new rank algorithm or rank measurement is used here.

The proved upstream `RowReduce.Inv` identifies pivot rows as rows of
adj(B)·P, whose entries are Cramer minors. Non-pivot rows are
det(B)·Aᵢ − Aᵢ,cols·adj(B)·P; their entries are bordered minors by the Schur
identity, and zero on pivot columns. Their order is at most min(rows,k).
In the second pass they are minors of the ternary augmented matrix [B|I]. Hadamard's
bound therefore gives H(k)=floor(sqrt(k^k)) as an absolute-value bound for
stored entries and pivot denominators, with H(0)=1. Each update's two products
have magnitude at most H(k)², and their pre-division difference at most
2H(k)²≤2k^k. Division is exact by the existing elimination invariant; its
previous denominator is a nonzero pivot or the initial 1. The quotient cannot
increase that magnitude. The compiled route uses `rowReduceWithImpl`,
whose updates are checked by `toForm_reduceStepImpl`. Native `exactDiv`
requires the invariant's exactness for correctness as well as the magnitude
bound. At k≥1 every coefficient integer thus has at most
floor(k log₂ k)+2 bits: 4, 6, 10 and 13 bits at k=2,3,4,5, and 35 bits at k=10.
At k=0 there is no coefficient update and the denominator is 1. This is a
mathematical source bound, not an observed peak or a timing law.

A second conservative derivation uses only the update recurrence:
H₀=1, Hⱼ₊₁=2Hⱼ². It bounds the same products, difference and exact quotient;
Hⱼ=2^(2ʲ−1), giving at most 2ᵏ bits. This bound does not use the minor
characterization implied by `RowReduce.Inv` and becomes loose rapidly with k.
The sharper rank scaling evidence remains upstream under #10352. Both bounds
exclude backend scratch storage and index arithmetic.

For a rank certificate actually returned by those passes, the naive products
in `Matrix.checkRank` have additional finite bounds. Its input entries remain
ternary. The selected block times the adjugate and the adjugate times selected
rows accumulate at most k terms of magnitude H(k). The remaining product
accumulates at most k of those sums, so its partial sums have magnitude at
most k²H(k). The scaled input and scaled identity have magnitude at most H(k).
`Node.check` also checks the adjugate times the selected submatrix; its
partial sums are bounded by kH(k). These bounds apply
to these constructed witnesses, not arbitrary supplied large integers.

The separate child-to-parent transport is also accounted for. Let kₗ,kᵣ be
the child ranks, R=kₗkᵣ the parent candidate dimension, and
V=H(kₗ)H(kᵣ). `parentInverse` forms a tensor product, so each entry and the
product of child denominators have magnitude at most V. Assume the
`Observations qs.length xs` and `QueryModel … xs` hypotheses of
`buildTreeFrom_complete`, and set N=xs.length. Under the lawful coefficient
interpretation and sign assumptions, `query_model` in
`HexSignDetMathlib/RootProducer.lean` and `rootObservations_valid` in
`RootModel.lean` supply these hypotheses for the root sign vectors.
`buildPrepared_roots` connects them to the actual producer. Each moment is
a sum of N ternary products,
so its magnitude is at most N. The naive
R-term sums in `solveScaled` then have magnitude at most RVN; the nonzero
exact divisor cannot increase this. The inverse-identity check's partial sums
have magnitude at most RV. The returned counts are nonnegative and sum to N
by the `Counted` conclusion of `buildTreeFrom_complete` under that model,
so the count-identity check's partial sums have
magnitude at most N. These give the coefficient-integer bound
max(1,V,RV,RVN,N) for that transport, solve and system check, including products
and partial sums. They do not cover the preceding query production or the
leaf solve and its integer checks, bounded separately below. Under the
stated model, zero candidate dimension entails N=0, both child ranks are
zero, and the denominator is 1. Backend scratch storage and index arithmetic remain excluded.

The production leaf solves use only the one-column matrix [1] and the fixed
three-column matrix displayed in the library SPEC. The latter's Gauss–Jordan
pivots are 1, 1 and 2. After the first pivot its other rows are
`[0,1,2 | 1,1,0]` and `[0,-1,0 | -1,0,1]`; after the second, the first and
third rows are `[1,0,-1 | 0,-1,0]` and `[0,0,2 | 0,1,1]`. Scaling the last
row by 1/2 and clearing its column gives inverse rows
`[0,-1/2,1/2]`, `[1,0,-1]` and `[0,1/2,1/2]`. This traces the actual first nonzero
pivot rule and row operations of `HexRowReduce`.

All rational coefficient numerators and denominators during this inversion
have magnitude at most two. Core `Rat.mul` cancels before multiplying;
`Rat.add` uses the common-denominator least common multiple. Their coefficient
integers remain bounded by four, including denominator products. If the
same `Observations` and `QueryModel` hypotheses hold, with N=xs.length,
the integer moments have magnitude at most N. Each inverse-times-moment term has denominator dividing two, and its
numerator over denominator two has magnitude at most 2N. Every three-term
partial sum and its pre-cancellation integers are therefore bounded by 6N.
The denominator lcm in `solveSystem` is at most two, its integer products at
most four, and its scaled inverse entries at most two. With the returned
nonnegative counts summing to N, the subsequent integer system check has
inverse-identity partial sums bounded by four and count-identity partial sums
bounded by N. A conservative bound for all these coefficient integers is
thus bitLength(max(6N,4)), including N=0. This concerns the
production leaf solves and their system checks, not large reference solves,
query construction, index arithmetic or backend scratch storage.

## Small intermediate-coefficient observations

The [rational arithmetic diagnostic](https://github.com/kim-em/hex-dev/pull/10825)
observes the generic coefficient operands/results in the three shared-root
callbacks, including their producers' acceptance checks. Maximum normalized
numerator/denominator sizes are 35, 75 and 161 bits. The corresponding
source-derived binary-operation temporary bounds are 71, 151 and 323 bits.
All eight operation categories are observed. Ordinary checks bind the seven
descriptors and four joint tables to their subjects; both common products
and full orders are checked, and the independent oracle identifies their
polynomials, intervals and roots. These are rational cases with P dividing Q;
the gcd stops after an exact division. They measure no nontrivial gcd
remainder growth and make no timing prediction.

The [nested operand diagnostic](https://github.com/kim-em/hex-dev/pull/10826)
uses the existing depth-one/depth-two infinitesimal fields with four and
eight queries. Observed outer coefficients have one-bit rational components
and at most three/five rational coordinate slots. Those maxima equal the
sizes of the input infinitesimals. Positive normalization changes the queries
to 1, retaining the infinitesimal in each scale witness; depth-two lower
coordinates are only 0 and 1. This does not exercise interaction between
infinitesimals. The ordinary checker and independent fixed-family oracle
bind the actual head, queries, whole-line interval and complete sign answer.
The observations exclude temporaries inside field arithmetic/sign dictionaries,
equality tests, Zero/One constructors and fixed matrix arithmetic. They are
not a general nested-field coefficient-growth bound.

The [joint and interacting operand supplement](https://github.com/kim-em/hex-dev/pull/10835)
checks the actual coprime-head comparison pipeline at degrees 3, 7 and 15,
with maximum normalized rational bits 9, 36 and 107 and temporary bounds
19, 73 and 215. Its explicit common-product constructor performs one
polynomial gcd and three exact polynomial divisions; internal remainder and
normalization work is outside those call counts. The interacting family
records reduced/direct/reference construction at depths one through three,
with constant outer operation counts and coordinate maxima 14, 80 and 250.
These are actual interacting coefficients, unlike the normalized-query
family above. The supplement binds subjects through ordinary replay and
independent Z3/FLINT checks, and separates outer operand observations from
temporaries inside recursive field dictionaries.

These observations complement the source bounds above. They distinguish
stored witnesses, outer coefficient operands and internal arithmetic
integers; neither counts nor bit maxima are wall-time laws. Their source
patches and main bases preserve reconstruction after squash merge and head
branch deletion.

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
The PR that advances the phase must link the raw observations and build the
declared HexSignDetMathlib proof-probe root in CI.
The dependency rule requires this library through Phase 3 and prerequisite
Sturm through Phase 4. The Phase-3 attestation is supplied by #10805;
prerequisite Sturm readiness is owned by #10577. The current numeric records
must satisfy both gates before a Phase-4 bump. Rank readiness is already
delivered under #10352; it is not a
reason to repeat its campaign.

The finite families do not cover every polynomial or coefficient field.
The 27-root maximal-support diagnostic takes about 1.91 seconds and includes
input interpolation, three producers and certificate checks. That complete
diagnostic is costly for repeated interactive use; it does not isolate or
establish the time of the shipped producer. No extrapolation to 81 roots or
general downstream production range follows from the three observations.
Large integer matrix checks are not full high-degree root computations;
positive-monomial normalization is not general Sturm-chain bit complexity;
two-root joint heads are not maximal-support inputs. Shared archived profiles
and memory observations retain their historical source/cache qualifications.
A genuine source-bound violation, unsuitable time/memory on intended inputs
or an unmet explicit comparison target remains a defect to investigate.
Expensive extra runs solely to cross a fitted-slope threshold are not required.

The linked joint timings and resident peaks delimit practical use of the measured
implementation. The small library examples exercise low-degree polynomials;
degrees 3–15 provide a practical small joint workload, while degree 31 is a
stress case. Degree 63 comparison takes about 28 seconds, and degree 255 takes
about 29 minutes: neither is a suitable interactive demonstration. The
large sizes are retained diagnostic observations, not a claim of practical
high-degree comparison. No hard acceptance threshold was declared for these
sizes, so this judgement does not manufacture a retrospective timing gate.
This is a judgement about the measured examples, not a demonstrated range of
all downstream calls. The tower consumer's actual degrees remain its own
integration evidence.

The interacting-infinitesimal conformance case in
[nested fields](sign-det-nested-fields.md) has a separate practical concern:
its complete emitter takes about 0.035, 0.815, 18.9 and 422 seconds at depths
one through four. These single executions include several production,
reference, replay and deliberately invalid replay operations; they are not
timings of one table constructor. Unlike the normalized-query family, their
coefficients combine infinitesimals from different levels. The scalar-sign
constructor recurrence alone does not explain the roughly 23-fold per-level
increase. The
[denominator-one fast paths and interacting diagnostics](https://github.com/kim-em/hex-dev/pull/10835)
remove repeated polynomial gcd/division work from nested polynomial arithmetic.
Existing reconstruction and correspondence proofs check the new branches.
The controlled two-depth comparison retains all 24 observations, with median
within-pair improvements of 3.86 and 19.41. A current complete four-depth
conformance execution takes about 0.55 seconds and passes the independent
oracle; its ratio to the historical run is not a controlled speedup claim.
The corrected implementation and short paired comparison supply a disposition
of that practical finding without another deep timing ladder. They do not
remove the separate scalar numeral-construction recurrence or establish a
general tower-depth limit.

The shared-root timings and construction counts are supplied by the linked
records. Those shared-factor inputs have P dividing Q. The separate joint
family has coprime heads and a common polynomial larger than both; neither
collection measures a common factor proper in both inputs. Source bounds
exist only for the named finite operations.
The linked diagnostics supply intermediate-operand observations for the
named small rational and nested families. General polynomial-chain growth,
nontrivial gcd remainder growth and temporaries inside nested field
dictionaries are outside those observations and the finite source bounds.
Stored witness maxima must not be called those peaks.

Merged #10641 removed canonical conversion from the per-sign path
(`signField` calls `QAdjoin.signApprox`). The linked fixed comparisons record
its effect on those inputs only. A persistent sign cache across callbacks and
the claimed interpreter bottleneck under #10635 are not resolved by them;
neither those fixed comparisons nor the small rational families establish
general number-field scaling.
