# General determinant prototype investigation

The objective is a general supplied-equality backend with lower complete-proof
cost than `simp only [norm_det] <;> ring`, without determinant fallbacks or
matrix-family dispatch. Production migration remains conditional on correctness,
API coverage, SPEC agreement and the shipping performance protocol.

The original 10×10 loss is not reproduced, and the final prototype wins that
case. A controlled arithmetic-proof change reduces its proof nodes by 21% and
both kernel timings by about 11%. The broader search finds real remaining losses:
independent symbolic quotients favor compact opaque entries, whereas exposing
quotient factors can make cancellation much cheaper. Neither scalar policy wins
universally. The final 6×6 product-denominator example is 0.261s versus Mathlib's
27.397s; the independent-quotient 6×6 counterexample is 4.699s versus 3.131s.
These are experimental supplied-equality timings, not native value benchmarks
or performance claims about production `det`.

## Search coverage and open hypotheses

| Direction | Required comparison or investigation | Evidence in this round |
|---|---|---|
| Rank one | 10×10 loss, then safe dimension scaling | Patched baseline wins 2.386s versus 2.495s; old small loss not reproduced. Compact arithmetic alone wins at 16×16. Final bounded control at 10×10 wins 1.165s/1.323s; Mathlib times out at 18×18 in the preceding bounded stage. |
| Kernel proof structure | Arithmetic congruence, recurrence and literal transport costs | Smaller arithmetic congruence proofs reduce nodes and kernel time at 10×10; recurrence and transport remain open. |
| Cancellation | Triangular and scattered algebraic zeros versus literal zeros | Algebraic zeros: 8×8 triangular 0.889s/1.327s; 7×7 scattered 15.348s/15.917s (prototype/Mathlib). Literal scattered zeros at 7×7 give 15.031s/15.621s. |
| Coefficient rings | Generic ring, rationals, prime and composite characteristic | Generic, integer and rational probes favor the prototype. Characteristic two at 6×6 gives 9.552s/10.268s; composite characteristic at 6×6 gives 8.337s/8.394s with split pairs, so no advantage is established. |
| Polynomial complexity | Degree, variable count, support and large coefficients | Dense 4×4 with four variables: 4.504s/9.102s. Polynomial coefficient ring at 4×4: 0.522s/0.679s. |
| Sharing | Repeated expressions retained versus expanded | Retained expressions: 13.029s/14.239s; expanded: 13.446s/14.969s. |
| Target representation | Expanded versus factored supplied targets | Factored 6×6 Vandermonde gives 9.158s/37.665s; matched representation controls remain open. |
| Row dependencies | Singular, skew-symmetric, circulant, independent entries | Odd skew 7×7: 19.510s/20.440s, a small observed margin. Variable-quotient singular matrices expose a substantial loss (below). Circulant 6×6 favors the prototype; the Mathlib 7×7 arm reaches its process timeout. |
| New directions | Concrete integer entries, alternate seeds, row/column permutations | Concrete integers tested through 16×16. At 12×12 the first batch has a loss and a win (3.314s/3.372s); its single unchanged repeat favors the prototype (3.459s/4.026s). At 16×16: 14.034s/15.815s. A second seed with transposition and reversed rows at 4×4 gives 6.998s/13.147s; both pairs favor the prototype. |

Select cases from evidence, not an automatic grid. Diagnose reproducible losses
before extending their dimension ladder. Each fresh module has a process ceiling
at most 60 seconds. A timeout blocks strictly larger comparable inputs. The
additional measurement allowance for this goal is 3600 seconds, shared across
all sibling variant roots under `bench-results/determinant-goal`; failures and diagnostics
count. Earlier rounds are separate evidence, not measurements charged here.

Keep all samples and source snapshots. Component diagnostics explain hypotheses;
only ordinary adjacent AB/BA comparisons establish the complete-proof outcomes.
List remaining uncertainties explicitly rather than treating untested directions
as wins.

## Controlled arithmetic proof assembly

`Compact.lean` adapts Mathlib's certificate evaluator with the same recurrence,
scalar arithmetic routines, cache keys and zero pruning. The supplied-target frontend enables field normalization, whereas Mathlib’s determinant reifier keeps division opaque; this difference is tested separately below. It replaces chains of `congrArg`,
`congr` and `Eq.trans` for addition, multiplication and negation with applications
of three small proved lemmas. This is a general arithmetic proof change.

On the 10×10 rank-one input, the ordinary adjacent before/after medians are
1.817s for the direct frontend and 1.387s for the compact arithmetic variant.
Both pairs favor the change. A separate profiler diagnostic finds:

| Component | Direct, two samples | Compact arithmetic, two samples |
|---|---:|---:|
| Unique full-proof nodes | 143,397 | 113,982 |
| Final kernel check | 645ms, 626ms | 562ms, 567ms |
| Tactic execution | 246ms, 445ms | 240ms, 289ms |
| Share common expressions | 216ms, 190ms | 166ms, 180ms |
| Process pre-definitions | 37ms, 36ms | 24ms, 27ms |

Proof nodes fall by about 21%; both adjacent kernel checks improve. The profile
does not support assigning the entire ordinary elapsed-time improvement to the
kernel: frontend and host variability also contribute. Node counting occurs
after declaration checking and outside the declaration clock. A failed first
diagnostic, caused by an unqualified logging identifier in the harness, is
retained and charged to the allowance; it is not a successful timing sample.

The baseline and optimization are separate comparisons. The fresh patched
baseline's small advantage over Mathlib does not establish that the restricted
conversion fix caused the earlier 10×10 gap to disappear. The controlled proof
assembly comparison is stronger evidence for an independent improvement.

At 16×16 the compact arithmetic variant takes 11.237s against Mathlib's 13.354s,
with both pairs agreeing. This extends dimension evidence without recognizing
rank-one matrices in the implementation.

## Recurrence proof control and cache invariant

`Steps.lean` proves combined scalar unfolding equations for the zero and
successor iteration cases. The first experimental integration accidentally
returned before inserting the result into the iteration cache. It times out at
10×10 under a 20-second process ceiling; the compact control takes 1.476s.
No larger input was attempted for that broken implementation.

A smaller 6×6 profile isolates the regression: tactic time grows from about
49ms to 709–715ms, while kernel checking only changes from 61ms to 69–71ms.
The generated C returns directly in the new branches instead of reaching the
cache insertion. Term sharing grows from 19–21ms to 928–1090ms; roughly one further second remains unattributed. Although the unique proof-node count falls from 19,980 to
19,290, repeated construction before term sharing overwhelms that saving.
This is an implementation error, not evidence against the combined theorem.

The corrected branches return their certificate to the shared insertion point.
An audit compares all three cache sizes with the ordinary recurrence on a 4×4
integer matrix: 16 entries, 25 iterations and 12 diagonal sums, in both modes.
The broken source and all its observations remain archived. The corrected
10×10 comparison gives 1.176s against compact arithmetic alone at 1.208s, with
both pairs favoring the change. These two small timing margins do not establish a robust additional speedup. The smaller proof structure is deterministic evidence; its time benefit remains uncertain.

## Coefficient and small-dimension controls

Ordinary medians in seconds, prototype versus Mathlib, with both pairs agreeing:

| Input | Corrected combined prototype | Mathlib |
|---|---:|---:|
| Dense 2×2, generic ring, quadratic entries | 0.050 | 0.075 |
| Concrete 4×4 integers, 16-bit entries | 0.046 | 0.051 |
| Dense 6×6 rational quadratic entries | 15.379 | 16.153 |
| Rank-one 6×6, 64-bit row denominators | 0.188 | 0.208 |
| Rank-one 8×8, 512-bit row denominators | 0.490 | 0.545 |
| Rank-one 8×8, 8192-bit row denominators | 0.757 | 0.814 |

The rational rank-one construction divides each row by its own constant
nonzero denominator. It preserves the zero determinant while stressing exact
fraction arithmetic. Entries here are spelled as fractional coefficients multiplied by monomials, not whole expressions divided by constants. No row-denominator recognition exists in the tactic.
The 8192-bit probe does not reproduce the hypothesized coefficient-normalization
loss. This does not establish the best normalization policy for arbitrary
rational inputs.

## Zero-matrix counterexample

The 16×16 zero matrix exposes a small loss. The first ordinary batch is
inconclusive (prototype 0.219s, Mathlib 0.217s, pairs disagree); its single
unchanged repeat favors Mathlib in both pairs (0.244s versus 0.237s).

The separate profile has virtually equal complete declaration medians, so it
does not reproduce the entire ordinary gap. It does isolate repeatable costs:

| Component | Mathlib | Combined prototype |
|---|---:|---:|
| Unique proof nodes | 3,492 | 3,294 |
| Kernel check, two samples | 188ms, 192ms | 183ms, 183ms |
| Tactic execution | 13.4ms, 13.4ms | 14.6ms, 14.4ms |
| Share common expressions | 1.08ms, 1.11ms | 4.95ms, 5.46ms |

The evidence does not support blaming the kernel for this loss. In particular,
smaller unique node counts do not imply less work in the term-sharing pass.
An explicit input-sharing control is inconclusive: the two pairs disagree
(prototype 0.235s, input-sharing variant 0.230s). Source inspection shows that
Lean already shares the goal and local context before entering a tactic via
`instantiateMVarDeclMVars`. Input sharing is therefore not an established fix.

A separate physical-node diagnostic also contradicts simple duplication as the
cause: Mathlib has 7,669 allocated expression nodes before abstraction and
10,063 afterward; the prototype has 7,274 and 9,425. After structural sharing
the corresponding closed counts are 3,632 and 3,434. These diagnostic clocks
include expensive counting and must not be used for performance rankings.
The small ordinary zero-matrix loss remains unresolved.

## Quotient normalization

Numeric quotient entries written as `x / d` at 5×5 with independent variables
favor the prototype: 1.086s versus 1.949s. But symbolic denominators expose a
substantial opposite result. In a 4×4 generic field matrix, each entry in the
first three rows is `(x + y) / z`, with fresh variables; the final row is the
sum of the first two. The zero target is valid without any nonzero assumptions.
Mathlib takes 0.232s, versus 1.458s for the prototype, with both pairs agreeing.

Mathlib keeps these quotient expressions opaque during the recurrence. The
prototype expands their numerators into monomials with inverse atoms before
multiplication. This motivates a controlled experiment in postponing division
normalization until comparison of the determinant value with the supplied target
requires it. It does not justify matrix-family recognition.

All ordinary observations here use two adjacent pairs, not the six-pair shipping
protocol. Small margins remain weak evidence, particularly where the same
implementation varies substantially across batches. The reference occupies
positions one and four, cancelling linear drift but not necessarily first-run
effects. No observations are discarded on that account.


The quotient profile finds 12,201 proof nodes for Mathlib versus 84,736 for the
eager field-normalizing prototype. Kernel checks are 46.9/47.7ms versus
316/302ms; tactic execution is 81/118ms versus 457/475ms; sharing is 60/41ms
versus 405/406ms. These are separate diagnostic samples, not replacements for
the ordinary comparison. The expansion affects construction and checking,
not just the final kernel.

`staged_bird` tests the general alternative: compute the recurrence over
opaque quotients, try the supplied-target comparison in the same atom context,
and only expand divisions if the first comparison fails. The second stage
cleans internal raw coefficient notation, normalizes the already computed
scalar value and the target, and composes the equality proofs. It never reruns
the determinant or invokes a determinant tactic. A first implementation omitted
that cleanup and failed the existing rational audit; this was repaired before
extending coverage. The archived initial controlled timing remains evidence
only for the zero-target branch that it exercised.

On the variable-quotient 4×4 input, the controlled initial comparison is 1.797s
for eager normalization versus 0.280s for staged normalization. The corrected
variant's ordinary comparison with Mathlib is inconclusive: 0.270s versus
0.286s, with the pairs disagreeing. This removes the large observed regression;
it does not establish superiority over Mathlib on this case.


At 5×5 with symbolic denominators, the opaque variant takes 0.990s versus
Mathlib's 1.249s, both pairs favoring it. Its rational rank-one control exposes
the opposite tradeoff: 3.984s versus Mathlib's 3.700s, with the pairs disagreeing.
This is not a universally better normalization policy.

`coeff_bird` separates coefficient arithmetic from symbolic inversion: its
scalar normalizer expands divisions by constant coefficients, while retaining
other quotients as atoms. The final full-field comparison remains available
when the first polynomial comparison is unequal. It does not inspect the matrix
family. The implementation adapts `Ring.Common.eval`; a production version
should expose a scalar-normalization policy hook rather than maintain this copy.

The initial controlled rational rank-one comparison gives 0.213s for this rule
versus 1.606s for opaque division, with both pairs agreeing. The initial symbolic
5×5 comparison has a small loss (0.339s versus 0.321s). That implementation
normalized every denominator merely to decide whether it was constant. The
current version asks the coefficient evaluator directly; a symbolic denominator
is left untouched when coefficient evaluation fails. The coefficient-only variant has a
separate archive, so no timings are silently combined across these sources.

## Additional target control

The capture diagnostic copies the exact cleaned expression Mathlib produces,
then a separate ordinary comparison supplies that expression as the target.
Capture and pretty-printing costs are excluded from that later ordinary run.
The first capture had a missing tactic import; its failed build is retained.
The corrected 4×4 capture timed out at its 30-second process limit. The smaller
3×3 capture succeeds, but its first export contained pretty-printer ellipses and
failed to compile as a supplied target. That failure is retained; the runner now
rejects truncated target text before invoking Lean. With deep-term printing
enabled, the two complete independent captures agree.
No larger capture input is attempted after the timeout.


The ordinary 3×3 comparison with the complete captured target takes 5.040s for
the coefficient-policy prototype versus 5.495s for Mathlib; both pairs favor the
prototype. This does not reproduce the hypothesized Mathlib advantage. Captured
source has a different target representation and different statement-checking
costs from the independently generated expansion, so its absolute times are
not a before/after backend comparison with the capture diagnostic.


## Coefficient-only implementation controls

These are fresh adjacent comparisons against Mathlib using the final coefficient
normalizer, not pooled with older variants. Times include the entire theorem
declaration and are specific to the shared host.

| Input | Prototype | Mathlib | Pair direction |
|---|---:|---:|---|
| 3×3, four variables, quadratic entries, captured target | 5.040s | 5.495s | Both favor prototype |
| 6×6, two-term numerators, symbolic denominators, dependent row | 5.690s | 7.219s | Both favor prototype |
| 10×10 rank-one matrix over a generic ring | 2.154s | 2.614s | Both favor prototype |
| Original issue #10320 integer quadratic fixture | 2.214s | 2.841s | Both favor prototype |

The larger symbolic-denominator control supports retaining opaque nonconstant
quotients as a general arithmetic mechanism. It does not imply that opacity is
always beneficial: cancellation across differently written symbolic quotients
can still require the stronger final normalization, after a potentially expensive
recurrence. No matrix-family recognition is used to choose that behavior.


The 7×7 symbolic-denominator escalation reaches the 60-second process ceiling
in Mathlib's first arm. The batch stops immediately without running the candidate;
no larger comparable input is attempted. This is a search boundary, not a
prototype win or a counterexample with Mathlib below one minute.


## Remaining symbolic quotient cancellation

A further control divides each row of a rank-one matrix by a fresh symbolic
denominator. It is still singular, including when any denominator is zero.
At 4×4 the coefficient-only policy and Mathlib are tied (0.487s each, pairs
split). At 5×5 it loses both pairs: 5.376s versus 4.596s. Thus distinguishing
constant denominators alone does not resolve the normalization tradeoff.

A general next rule is to expand a quotient when its numerator normalizes to
at most one monomial, or its denominator is a constant coefficient. This can
expose multiplicative cancellation without turning one quotient atom into a
sum. Inverting a polynomial itself likewise does not create a polynomial sum:
the existing ring evaluator leaves inverse sums atomic. This hypothesis concerns
scalar expression growth and requires controls against multi-term numerators;
it does not inspect rank, determinant value or matrix shape.


The 5×5 loss profile localizes the regression away from the final kernel:
Mathlib's tactic samples are 2.629/2.294s versus 3.575/3.174s for the
coefficient-only policy. Kernel samples are 551/460ms versus 431/431ms, while
sharing remains roughly 0.95–1.08s for both. Unique proof counts are 89,572 and
86,965. Optimizing kernel checking alone would miss the dominant difference.

`AtomM.containsThenAdd` scans existing atoms and calls definitional equality
on each. The prototype's second field-normalization pass retains the first
pass's now-obsolete quotient atoms; Mathlib's separate `ring` call starts fresh.
`fresh_bird` isolates starting a fresh atom context for the second pass. Both
sides are re-normalized in that new context, and only expressions and equality
proofs cross the boundary; no old atom indices are used in the comparison.


The controlled fresh-context comparison improves both pairs: 5.484s versus
6.260s with the retained atom table. This supports dropping obsolete atom
indices at that boundary. It is separate from the proposed monomial-growth
policy and does not require a matrix-pattern test.


Against Mathlib, the fresh-context variant is inconclusive at 5×5: 3.536s
versus 3.528s, with split pairs. The subsequent `division_bird` experiment
expands quotients with a constant denominator or a numerator containing at most
one normalized monomial. It retains inverse normalization from the existing
ring evaluator. When a trial numerator/denominator normalization is discarded,
it restores the prior atom table before making the whole quotient an atom.
This prevents speculative, unused atoms from slowing subsequent lookups.

The controlled comparison on symbolic row denominators improves from 2.396s
with coefficient-only division and fresh comparison to 0.184s with the new
scalar rule. Both pairs agree. The matrix recurrence and zero pruning are
unchanged; the scalar representation now exposes cancellation during the
recurrence rather than after it. The multi-term numerator controls below show why this scalar rule alone is
insufficient as the final policy.


For 6×6 multi-term quotients, the first division-policy batch is inconclusive
(6.287s versus Mathlib's 5.304s, split pairs). Its one unchanged repeat favors
the prototype in both pairs (9.210s versus 10.178s). Both batches are retained;
the repeat does not erase the initial loss. There is no third unchanged run.

Additional correctness audits cover nested quotient products, zero numerators
and literal zero denominators without assuming any symbolic denominator is
nonzero. Two stronger scalar identities are explicit limitations: simplifying
inverse-of-inverse expressions and reducing a denominator `2` to zero in
`ZMod 2` require scalar simplifications that neither bare determinant comparison
closes. The audits verify both failures using `solve` (checking that all goals
close, rather than merely whether a tactic returns) and prove the mathematical
identities separately with ordinary simplification. They are not successful
prototype proofs or performance counterexamples.


## Cost of speculative normalization

The multi-term quotient test has another important axis: the numerator can be
written compactly as a polynomial power. With 4×4 entries `(x+y+z)^8 / w` and
the same dependent last row, the division policy takes 1.102s versus Mathlib's
0.300s, losing both pairs. The profile isolates discarded work: tactic samples
are 965/1086ms versus 85/177ms, while kernel checks are 53.5/54.5ms versus
60.6/68.8ms. The prototype even has fewer proof nodes (11,365 versus 12,457).
It expands every numerator to decide that it should not expand the quotient.

`bounded_bird` tests stopping that speculative pass at a recursive result with
more than one monomial. The rejected quotient retains its original expression
and restores the prior atom table. Numeric denominator arithmetic remains eager;
in this measured source stage, other inverse arguments remain opaque until the
stronger final comparison needs their contents. This is a scalar normalization cost control, not an
estimate of determinant minors or recognition of a matrix family.


The controlled high-degree comparison drops from 0.433s to 0.103s with bounded
speculation, with both pairs agreeing. This fixes work that never contributed
to the emitted certificate. It is a distinct experiment from the earlier
monomial-expansion change and from resetting the second-pass atom context.


## Residual cost of expanding monomial quotients

With a single independent numerator per entry and a dependent final row at
4×4, bounded normalization loses both ordinary pairs: 0.139s versus Mathlib's
0.080s. Retaining the quotient as one atom is cheaper here than replacing it
with a numerator factor and an inverse factor. This is a counterexample to
claiming the monomial rule is universally preferable, despite its large gain
on symbolic rank-one entries. It must remain in the corpus.


The controlled representation profile confirms extra checking work. With
quotients opaque, the 4×4 proof has 10,989 unique nodes and kernel samples
43.0/49.9ms. Bounded monomial expansion gives 15,122 nodes and 86.6/114ms.
Tactic samples also grow (65/85ms to 83/149ms); sharing overlaps. Both policies
use the same compact recurrence and input. The loss persists at 5×5 in an
ordinary comparison: 1.558s versus Mathlib's 1.307s, both pairs favoring Mathlib.
This is a representation tradeoff, not a reason to add a rank-specific route.


## Bounded-policy coverage

| Input | Prototype | Mathlib | Ordinary paired result |
|---|---:|---:|---|
| Original integer quadratic issue fixture | 2.863s | 3.233s | Both favor prototype |
| Circulant 6×6 over a generic ring | 3.252s | 4.038s | Both favor prototype |
| Independent quotient entries, dependent row, 4×4 | 0.139s | 0.080s | Both favor Mathlib |
| Same construction, 5×5 | 1.558s | 1.307s | Both favor Mathlib |
| Same construction, 6×6 | 5.532s | 3.769s | Both favor Mathlib |

The 7×7 circulant and 18×18 generic rank-one cases time out in Mathlib's first
arm at the 60-second process ceiling. Their candidates are not run, and larger
comparable inputs are blocked. These timeouts include fresh-module overhead;
they do not establish that the determinant tactic alone requires 60 seconds.
They are search boundaries, not prototype wins.

The same bounded source stage gives 2.347s versus 2.851s on concrete rational
8×8 matrices with 16-bit numerators and denominators; both pairs agree. On 5×5
rank-one entries with symbolic row denominators it gives 0.403s versus 5.546s,
also with both pairs agreeing. Absolute drift is substantial in some pairs;
these medians are observations on the shared host, not portable predictions.

## Bounded denominator normalization and final controls

The final implementation applies bounded normalization to symbolic denominators
and inverse arguments too. Otherwise `a/(u*v)` and `(a/u)/v` unnecessarily use
different factor representations, and row/column product denominators hide
cancellation until the expensive second pass. A compound denominator that would
expand into multiple monomials remains opaque. Both Meta state and atom state
are restored when speculation is discarded. Scalar multiplication propagates
refusal instead of concealing it with an opaque subexpression.

`bounded_first` disables the stronger final comparison. Positive audits require
rank-one quotient cancellation, product denominators, nested division and inverse
products to succeed under it. Independent atom checks cover successful monomial
splitting and rollback after powers, scalar multiplication and nested division.
Thus the audits detect regressions which ordinary successful final proofs could
hide behind a second normalization pass.

These corrections do not resolve the opposing representations needed by two
inputs whose individual entries have the same scalar shape. Independent
monomial quotients remain a reproducible loss. The high-degree input also has a
small residual loss; removing its wasted expansion is not the same as beating
Mathlib on the complete proof.

The residual high-degree loss is localized by the final profile: tactic execution
is 46.9/46.7ms versus Mathlib's 32.0/32.0ms, while kernel checking is slightly
smaller (22.0/21.9ms versus 23.5/23.5ms) and sharing is about 7–8ms for both.
Bounded trial normalization still performs work that the opaque-quotient
comparator avoids. A static syntax-only rejection might reduce this overhead,
but must preserve profitable cancellation; it is not implemented or claimed as a
fix. The earlier controlled bounded-versus-unbounded comparison establishes the
large improvement, while this profile establishes the remaining frontend cost.

The final single-numerator quotient ladder stops at 7×7: Mathlib's first arm
hits the 60-second fresh-module ceiling. No larger comparable input is run.
This is distinct from the earlier 7×7 timeout with two-term numerators; reducing
support made this a legitimate smaller input, not an escalation past that limit.

## Final-source comparison table

All rows below use the same final Lean sources. Times are complete declaration
medians in seconds. Each completed row has two adjacent AB/BA pairs; different
source stages above are not pooled with these results.

| Input | Prototype | Mathlib | Pair result |
|---|---:|---:|---|
| Dense quadratic 6×6 over ZMod 6 | 7.533 | 7.913 | Both favor prototype |
| Dense 3×3, two variables, degree-eight entries | 0.534 | 1.022 | Both favor prototype |
| Original integer quadratic 4×4 issue fixture | 0.883 | 1.005 | Both favor prototype |
| Rank one 4×4, products of row/column denominators | 0.099 | 0.303 | Both favor prototype |
| Same construction, 5×5 | 0.162 | 2.175 | Both favor prototype |
| Same construction, 6×6 | 0.261 | 27.397 | Both favor prototype |
| Rank one 10×10 over a generic ring | 1.165 | 1.323 | Both favor prototype |
| Dependent-row 4×4, three-term numerators raised to degree eight | 0.102 | 0.091 | Both favor Mathlib |
| Dependent-row 4×4, two-term quotient numerators | 0.086 | 0.080 | Both favor Mathlib |
| Dependent-row 6×6, independent monomial quotients | 4.699 | 3.131 | Both favor Mathlib |
| Same construction, 7×7 | — | 60s process timeout | Search boundary |
| Zero matrix 16×16 | 0.216 | 0.216 | Split |

Full inputs, CPU/host context, source snapshots, raw outputs, failures and ranges
are retained in the [final inventory](bench-results/determinant-goal/bounded-final/inventory.md).
The diagnostic timings live in a [separate inventory](bench-results/determinant-goal/bounded-final-profile/inventory.md).

## Remaining directions and decision

The next architecture should keep compact quotient representatives together with
proved multiplicative identities, using those identities when they enable
combination or cancellation. Eagerly expanding every monomial quotient and keeping
every quotient opaque each have counterexamples. The matrix recurrence need not
change to establish that representation result. The tested compact arithmetic
proof constructors are independently justified and are suitable for an upstream
Mathlib proposal; exact reuse of its semiring congruence lemmas still needs an
instance-conversion control.

Concrete gaps remain, in priority order:

- A representation supporting both retained quotient losses and profitable
  quotient cancellation, with a bound on the second scalar comparison.
- More expression spellings: scalar casts, symbolic exponents, nested inverse
  simplifications, and mixed symbolic/numeric denominators. Current audits cover
  selected identities, not a complete field simplifier.
- Larger product-denominator, high-degree dense and composite-characteristic
  inputs; broader seeds and permutations. One alternate seed/permutation does
  not characterize a distribution.
- A matched target-form ladder using the same polynomial and multiple equivalent
  factorizations. One captured cleaned-target control and the Vandermonde family
  do not cover all supplied targets.
- Production goal forms beyond forward literal `Fin` matrix equalities, including
  reversed equalities, nested tactic goals and APIs constructing a result.
- Fixed-ring value execution and dyadic adapters. These are separate from proof
  timing and have no new runtime measurements in this round.

Timeout frontiers stop the corresponding dimension ladders. The remaining
measurement allowance determines which new complete adjacent batch can be
admitted; it is not permission to discard samples or lower a running timeout.
The corpus supports improvements and counterexamples, not a claim that all
plausible mathematical families have been exhausted.

The [replacement proposal](determinant-redesign-proposal.md) recommends one
normalized Bird proof backend with explicit scalar policy and compact proofs,
while retaining exact-value algorithms and numeric certificates separately.
Production migration requires agreed SPEC changes, broader API coverage, and
six adjacent pairs on a representative shipping corpus. No production route or
normative SPEC is changed by these experiments.

The final zero-matrix control is essentially tied: 0.21645s versus 0.21638s,
with split pair directions. The earlier reproducible 7ms loss remains retained;
this result does not establish a causal fix. The original two-term symbolic
quotient case is reduced from the eager policy's sixfold loss to 0.0861s versus
0.0798s, still losing both final pairs. This small residual is consistent with
the retained bounded-speculation frontend cost, not a universal speedup.

A final direct profile of the 6×6 independent-quotient loss confirms that the
4×4 representation diagnosis scales:

| Component | Mathlib, two samples | Final bounded prototype, two samples |
|---|---:|---:|
| Unique proof nodes | 426,125 | 523,153 |
| Tactic execution | 436/431ms | 608/608ms |
| Share common expressions | 868/861ms | 1440/1440ms |
| Kernel checking | 927/945ms | 1210/1210ms |
| Process pre-definitions | 146/154ms | 195/195ms |
| Complete declaration | 3.159/3.174s | 4.582/4.580s |

Expansion makes the proof about 23% larger. Sharing contributes more of the
elapsed gap than kernel checking, and frontend work grows too. These component
spans do not exhaust the declaration clock; about 0.34s of the median difference
remains outside the listed spans and level-parameter fixing. It is not assigned
to any more specific operation without evidence. This diagnostic supports the
representation recommendation without claiming that smaller kernel terms alone
would eliminate the whole loss.

## Validation and retained evidence

The retained round contains 92 selected cases, 333 successful measured proof
calls, nine failed cases, and 750 source snapshots. The failures include harness
errors, an intentionally retained broken cache integration, and timeout boundaries;
they are charged and are not counted as successful timing samples. Total measured
batch wall time is **3514.7 seconds (58 minutes 35 seconds)**. Correctness builds
and static verification are separate from that measurement clock.

Only 85.3 seconds remain. Admission of the next 7×7 product-denominator batch at
the full 60-second invocation ceiling is
[refused](bench-results/determinant-goal/validation/search-stop.log): four adjacent
invocations require 245 seconds including coordination overhead. The near-minute
search stops here without lowering that ceiling to squeeze in a larger case.
Smaller retained controls were prioritized before this admission check; the
unexplored directions above remain explicit.

The [evidence verifier](../experiments/Determinant/verify_goal.py) checks archived
source hashes, final-source agreement, AB/BA order, permitted theorem dependencies,
all completed and failed case accounting, and the aggregate allowance. It
regenerates each variant's inventory without running new measurements. Its
[machine-readable result](bench-results/determinant-goal/validation/evidence.json)
records the checks and failure list. All accepted measured theorem dependencies
are confined to `propext`, `Classical.choice` and `Quot.sound`.

The explicit Lean audit build covers the normalized, compact, fused, interning,
staged, coefficient, fresh-context, division and bounded variants, plus the proof
inspector. It checks incorrect-target rejection, generic and finite rings,
numeric and symbolic division (including zero denominators), first-pass success,
atom rollback and actual certificate cache reuse. The verifier checks all 137
printed audit dependency records. The runner has seven passing resource-guard
tests, including an admission-only path that cannot start a proof measurement.

The DAG, Phase-4 and released-manifest verifiers pass. Production sources,
conformance drivers and fixtures, CI configuration and normative SPECs are
unchanged; the proposal remains separate from them. This round is exploratory:
no six-pair shipping qualification or production migration is claimed.

`LEAN_NUM_THREADS=1 lake build` and the explicit experimental audit build both
pass. The [validation command record](bench-results/determinant-goal/validation/checks.json)
links their full logs and the static checks. `git diff --check` passes. No
production implementation or release manifest change is part of this deliverable.
