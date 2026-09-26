# Determinant redesign prototypes

These experiments are excluded from production dispatch, default builds and
CI. The fixture producer is Mathlib-free; proof probes are module builds.

From the repository root:

```sh
# Force the fixture-producing declaration to run even with a warm Lake cache.
rm -f .lake/build/lib/lean/Determinant/Fixture.olean
lake build Determinant.Fixture > /tmp/determinant-fixture.log 2>&1
lake build Determinant.Arithmetic
python3 experiments/Determinant/arithmetic.py /tmp/determinant-fixture.log /tmp/determinant-arithmetic
python3 experiments/Determinant/full.py /tmp/determinant-arithmetic/fixture.json experiments/Determinant/Full.lean
lake build Determinant.Audit
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-full
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-transport --mode transport
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-controls --mode controls
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-shared --mode shared
```

Use new output directories and run serially. Runners refuse to overwrite
results and stop the batch on failure/timeout. Every measured invocation has
a 60-second ceiling; each batch has at most a four-minute ceiling. All observations
are retained. The generator is limited to the fixed 4×4 quadratic witness;
it is not a general determinant implementation.

`arithmetic.py` compares list replay, independent ring proofs and cached ring
proofs for equivalent identities in different statement formats.
`full_measure.py` includes every prototype lemma and compares production
Hex and explicit Mathlib proofs of the same generated statement. Witness
production and source generation are outside the proof clocks.

The default full-proof clock is synchronous complete declaration elaboration,
including statement and all kernel checks. `--clock profile` selects the older
tactic/kernel component diagnostic. Do not compare those metrics directly.
`--mode arithmetic --clock profile` compares ordinary and opaque-certificate
arithmetic; `--mode transport` holds the witness fixed while changing transport;
`--mode controls` compares improved transport against production tactics.
`--mode deferred` compares delayed ordinary normalization with cached traversal
of the same shared Bird expression. `--mode shared` compares the latter with
explicit Mathlib and production Hex. Cases are `quadratic4` (default),
`independent4`, `common-factor4`, and `linear6`; the last requires python-flint
to generate an independent target. These are forward literal equality probes,
not a general production frontend. All candidate construction and checking,
including the supplied-target comparison, is inside the declaration clock.

For compiled value experiments, use a Python environment with `python-flint`
(the retained runs use 0.9.0). Build before measuring, then select one case:

```sh
lake build determinant_experiment
python experiments/Determinant/runtime.py /tmp/determinant-int --ring int --dimension 16
python experiments/Determinant/runtime.py /tmp/determinant-poly --ring poly --dimension 4
python experiments/Determinant/runtime.py /tmp/determinant-rat --ring rat --dimension 8
python experiments/Determinant/runtime.py /tmp/determinant-dyadic --ring dyadic --dimension 8 --spread 64
python experiments/Determinant/runtime.py /tmp/determinant-modular --ring int --dimension 32 --modular
python experiments/Determinant/runtime.py /tmp/determinant-flat --ring int --dimension 128 --flat
python experiments/Determinant/runtime.py /tmp/determinant-owned --ring int --dimension 32 --owned
python experiments/Determinant/runtime.py /tmp/determinant-word --ring int --dimension 128 --word
python experiments/Determinant/runtime.py /tmp/determinant-univariate --ring univariate --dimension 4
python experiments/Determinant/word_loop.py /tmp/determinant-flat /tmp/determinant-c
python experiments/Determinant/verify.py /tmp/determinant-value-verification
python experiments/Determinant/word_verify.py /tmp/determinant-c-verification
```

These are independent commands, not instructions to run a grid. Choose the
next case from the preceding result. The runtime runner stops its whole batch
on a timeout/failure, and never launches a larger case automatically. After a
timeout, do not manually advance a comparable dimension/coefficient ladder.
The polynomial cases use fixed fixtures: only dimension 4, dense shape, and
the default bits/spread arguments are accepted.
`--modular` compares existing ordinary CRT and divisor routes without fallback
and attributes ordinary CRT stages. `--flat` changes just its elimination route.
`--owned` and `--word` compare the experimental owned Lean buffer and hoisted
raw-word arithmetic. The univariate case compares sparse/dense Bareiss and cold
nine-point interpolation, returning the same dense coefficient array. It is
limited to the fixed 4×4 quadratic fixture.

`word_loop.py` requires a C compiler and consumes a retained `--flat`, `--owned`
or `--word` batch containing the exact matrix and prime list. It compiles a
value-only C diagnostic, compares all prime images with FLINT in two AB/BA pairs,
and removes the generated shared object. Its hard batch limit is 60 seconds.
It is never linked into Lean proofs or production Hex. `word_verify.py` checks
its small/boundary/singular/pivot cases with the undefined-behavior sanitizer;
the retained host uses Clang and its standalone UBSan runtime.

Native clocks include input-reference reading, arithmetic and storing the result
before the stop clock; generated C was inspected to verify that ordering.
Inputs, JSON serialization and external validation are outside the native
clocks. The runner retains executable/source hashes, inputs, process resource
metrics, FLINT answers and all samples. `verify.py` checks boundary dimensions,
singularity, initial row pivoting, and the executable's Mathlib-free import
closure; it is not a timing experiment. Bird and scaling remain experimental
value routines with differential checks, not new universal correctness proofs.

`Arithmetic.lean` uses scalar arithmetic helpers from Mathlib's Bird
certificate module. It never calls the Bird determinant evaluator or
`norm_det`. `Audit.lean` checks axioms, counts proof nodes, and tests generic
arithmetic and rejection of unequal normal forms.
`DeferredAudit.lean` checks generic-ring shared/deferred determinant proofs,
rejection of a wrong supplied target, and their axiom dependencies. The
`Deferred.lean` recurrence is an attributed experimental adaptation of Mathlib's
Bird certificate evaluator; the scalar normalizer itself is reused.

The recorded integer microbenchmark's exact support source is in its archive.
The working support is generalized to arbitrary commutative rings; a rerun
is not byte-for-byte reproduction of that integer-only implementation.

See [results](../../reports/determinant-redesign-results.md) for measurements,
limitations, negative results and the next hypotheses.

## Adversarial proof search

`adversarial.py` compares the unchanged `shared_bird` prototype with explicit
`simp only [norm_det] <;> ring`. Select one case at a time; this is not a grid.
The [search report](../../reports/determinant-adversarial-search.md) describes
the losses, controls, and untested regions. Every retained `case.json` records
the command parameters, and each directory preserves the actual Lean statements.

```sh
lake build Determinant.Deferred Mathlib.Tactic.NormDet Mathlib.Data.ZMod.Basic
python experiments/Determinant/adversarial.py /tmp/det-search/cancel6 --family cancel --n 6 --degree 2
python3 experiments/Determinant/adversarial_report.py /tmp/det-search
```

Use a Python environment with python-flint (the retained search uses 0.9.0).
Ordinary cases have two fresh adjacent AB/BA pairs and synchronous complete
declaration clocks. All theorem/kernel checking is included. Import loading,
parsing and target generation are outside that clock; the 60-second process
ceiling includes loading and build overhead, so a timeout is not an exact
60-second tactic measurement. Every successful result theorem's axioms are
audited by its qualified name, not by the first axiom message from an import.

The runner enforces serial use of this worktree, refuses existing output
directories, gives a case at most six minutes, and caps its allowance by the
remaining 40-minute cumulative search budget. It refuses to start without
allowance for four full invocation ceilings plus coordination overhead. Preserve
a common output parent across the search: its recorded timeouts block
coordinatewise larger cases in the same
family/carrier/representation. Changing an independent input direction is a new
scientific decision, never an automatically scheduled escape from a timeout.

`dense` varies dimension, atoms, degree, support and coefficient bits.
`cancel`/`triangular` and `sparse-cancel`/`sparse` pair algebraically zero entries
with literal zeros. `decorated` adds a zero polynomial to nonzero entries.
`singular`, `skew`, `rankone`, `independent`, `vandermonde` and `circulant` supply
other constructions. For the last four, dimension determines the entries;
the unrelated polynomial-shape flags must stay at their defaults. Independent
entries use `n²` variables, rank-one entries use `2n`, and Vandermonde/circulant
entries use `n`. Rank-one targets are supplied as zero directly; ordinary targets use independent subset
expansion with FLINT polynomial arithmetic, outside both proof arms' clocks.

`--rational` uses rational coefficients, and `--modulus` specializes to `ZMod`.
`factor --target factored` retains a common factor in the supplied target;
`shared --entry-form factored` retains a repeated expression in the entries.
The corresponding `expanded` spelling is a separate selected control.
`--diagnostic` adds a tactic clock, and `--kernel-profile` additionally profiles
final declaration processing. Keep these diagnostics separate from the ordinary
comparisons. The inventory reparses multiline kernel/profile messages from the
saved compiler output and verifies that the prototype source hashes never changed.

## Normalized determinant comparison

`Normalized.lean` reuses Mathlib's normalized Bird certificate evaluator and
normalizes the supplied target in the same atom context. It uses the ordinary
ring cache, including available field instances for rational coefficients.
It does not invoke `norm_det` or a determinant fallback. These remain manual
experiments, excluded from production dispatch.

Three entry points isolate proof assembly: `normalized_bird` composes the two
normalization proofs explicitly; `composed_bird` uses Lean's equality proof
constructors, which remove syntactic reflexivity; `direct_bird` additionally
returns the determinant certificate when its normal form is definitionally
equal to the supplied target at reducible transparency. Restricting this optional
conversion prevents expensive unfolding of concrete ring arithmetic; ordinary
target normalization handles the remaining cases. These are general assembly
variants, without matrix-family recognition. `literal_bird` additionally keeps
the goal's dimension expression in the certificate. It is a structural control,
not a demonstrated speed improvement or the selected default.

```sh
lake build Determinant.NormalizedAudit
python experiments/Determinant/adversarial.py /tmp/det-normalized/cancel6 --candidate normalized --family cancel --n 6 --degree 2
python experiments/Determinant/adversarial.py /tmp/det-direct/rankone10 --candidate direct --family rankone --n 10
python3 experiments/Determinant/adversarial_report.py /tmp/det-normalized
python3 experiments/Determinant/adversarial_report.py /tmp/det-direct
```

Select cases independently; the examples do not prescribe a sweep. Keep a
separate output root per variant, with all roots under one parent. The runner
charges these variants against one ten-minute allowance across sibling roots,
including failures and diagnostics. Switching variants does not reset it.
The same serial lock and per-invocation ceiling apply. Each archive retains the
prototype source used at that stage; later assembly changes are not substituted
into earlier observations. The [normalized comparison report](../../reports/determinant-normalized-comparison.md)
records the results and remaining counterexamples.

`--invocation-seconds` may lower the default 60-second process ceiling. Admission
reserves four of the selected ceilings plus coordination overhead; the cumulative
allowance is unchanged. The selected limit is recorded with the case, including
any resulting timeout. Shortening it cannot establish a 60-second runtime claim.

`--reference direct --candidate literal` compares the dimension representation
directly in adjacent before/after pairs. Keep different references in separate
roots. `--search-seconds` sets the cumulative allowance for a separately
authorized round, with an absolute maximum of 3600 seconds. The default remains
600 seconds for normalization variants. A recorded lower cap remains in force
across sibling normalization roots even if a later invocation omits or raises
this argument. Do not change output parents to evade a round's budget.

`Inspect.lean` and `inspect_proofs.py OUTPUT [direct|literal]` compare the retained
10×10 rank-one theorem bodies after kernel checking. Build `Determinant.Inspect`
first. The inspector selects the Bird certificate inside each proof, compares
exact expressions and unique node sets, and reports the first structural
mismatch. Head counts include partial applications; they are not arithmetic
operation counts. Full structural comparison can itself be expensive. The
inspector has a 60-second process ceiling and 65-second batch allowance, charged
against a six-minute sibling-root ledger. It measures both arms in one fixed
order, so its clocks are diagnostics, not performance rankings. Do not pass its
custom archive to `adversarial_report.py`.

The [wider comparison](../../reports/determinant-wider-comparison.md) records
the structural control, rational/skew/factored/positive-characteristic probes,
and the restricted-conversion fix, with frozen sources for each stage.

## General proof improvements

`compact_bird` substitutes small proved arithmetic congruence lemmas into the
same Bird recurrence and scalar normalizer. `fused_bird` also combines the
recurrence unfolding equalities using `Steps.lean`. These are experimental
controls, not additional production strategies or matrix-shape dispatch.
`--reference compact --candidate fused` isolates the recurrence-proof change.
Build `Determinant.CompactAudit` and `Determinant.FusedAudit` before measuring.
The latter also checks that both recurrence variants populate the same caches.

`--proof-nodes` counts unique theorem-body nodes after kernel checking; it marks
the batch as a diagnostic. `--kernel-profile --proof-nodes` combines that count
with declaration-stage attribution. Do not pool diagnostic clocks with ordinary
comparisons or interpret unique node counts as measuring physical sharing during
proof construction.

For coefficient stress tests, `--integer` specializes the carrier to `Int`, and
`--concrete` supplies numeric entries in a dense matrix over an explicit ring.
Rational entries use `--denominator-bits` (default 3). `--row-denominators` uses
one denominator per row, permitting rational rank-one inputs without destroying
their dependency. These parameters describe generated tests; the tactic does
not branch on them. Ordinary defaults reproduce the earlier statements.

The [goal investigation](../../reports/determinant-goal-investigation.md)
maintains the search coverage, causal evidence and unresolved directions.
Its separately authorized one-hour ledger is `reports/bench-results/determinant-goal`,
shared by every variant and diagnostic in that round.


`staged_bird` keeps division opaque during the recurrence, expanding it only if
comparison with the target needs that identity. `coeff_bird` instead normalizes
constant denominators early and keeps symbolic quotients opaque; it uses the
same final comparison when necessary. `Coefficients.lean` is an attributed
experimental adaptation of the ring scalar evaluator, not a determinant
algorithm. Build `Determinant.StagedAudit` and `Determinant.CoeffAudit` first.
The experiments compare these policies rather than dispatching by matrix shape.
`intern_bird` is an inconclusive input-sharing control, not a recommended change.

Additional selected-input controls include `--polynomial` for a polynomial
coefficient ring, `--reverse-rows`, `--transpose`, and the fixed `zero` and
`identity` families. `issue10320` retains the exact original integer quadratic
fixture. `--quotient-entries` writes whole rational numerators divided by their
denominators; the default writes fractional coefficients separately. These
representations can behave very differently. `variable-quotients` makes a
generic-field matrix whose last row is the sum of the first two; `--support`
sets the number of fresh numerator variables per entry. These shapes belong to
the test generator, never to tactic dispatch.

`--physical-nodes` measures allocated proof objects before declaration sharing;
its overhead makes the complete clocks unsuitable for performance rankings.
`--capture-target` is also diagnostic: it records Mathlib's cleaned output
between `CLEANED_TARGET_BEGIN` and `CLEANED_TARGET_END`. A later ordinary control
can use `--cleaned-target FILE`, a JSON object with `expression` and the captured
`input.json`'s `original_statement_sha256`. The runner verifies the original
statement hash and archives that JSON. This tests supplying precisely the
expression Mathlib produces, rather than an independently expanded target.

Run `python3 experiments/Determinant/test_adversarial.py` when no measurement
holds the serial lock. These checks exercise the shared allowance, persistence
of a lower cap, unfinished cases and timeout ordering without running Lean.


`fresh_bird` uses the coefficient policy and starts a fresh atom table only for
its second scalar comparison. Old atom indices are not needed after both sides
are normalized anew. `--reference coeff --candidate fresh` isolates that cost.
`--symbolic-row-denominators` adds fresh generic-field denominators to the
rank-one test generator; unlike numeric denominators, these exercise residual
symbolic quotient cancellation. They add no dispatch branch to the tactic.

Timeout ordering also applies across sibling roots for Mathlib, and for an
unchanged candidate whose archived Lean source hashes still match. Diagnostic
clocks are compared separately from ordinary probes; moving a timeout to a new
output root does not authorize advancing its unchanged dimension ladder.


`division_bird` adds the scalar rule in `Division.lean`: normalize division by
constant coefficients, or when the normalized numerator is zero or a single
monomial. Preserve other quotients atomically. Trial normal forms that are
rejected restore both the atom table and Meta state. This is independent of matrix
dimension, rank or shape; all branches use the same cached Bird recurrence.
The stronger final comparison uses a fresh atom context. Build
`Determinant.DivisionAudit` before measuring; it includes symbolic/numeric
quotients, nested division, zero numerators and literal zero denominators. It separately records
inverse-of-inverse and finite-characteristic simplifications that both bare
normalizers fail to close without additional scalar simplification. `--reference fresh --candidate division` isolates this policy.


`bounded_bird` uses `Bounded.lean` to stop speculative numerator normalization
at a recursive result with more than one monomial. It applies the same bound to
denominators and inverse arguments, keeping a multi-term argument opaque. It
still permits the full-field final comparison. This avoids
expanding a large numerator merely to reject its expansion. Build
`Determinant.BoundedAudit`; compare with `--reference division --candidate bounded`.
The variable-quotient generator accepts `--degree` for powers of each numerator
sum, allowing compact inputs with larger potential expansions.

`bounded_first` is an audit-only entry point that disables the stronger final
comparison. Positive rank-one, nested quotient, product-denominator and inverse
checks must close with this entry point, so a successful audit cannot conceal
loss of bounded normalization behind a second expansion. Atom checks exercise
scalar-multiplication refusal, nested speculation and successful monomial
splitting. The ordinary `bounded_bird` entry point still permits the second pass.
Use `--symbolic-row-denominators --product-denominators` on the rank-one generator
to test a product of row and column denominators; no nonzero hypotheses are used.

`--admission-only` checks resource and timeout guards without creating a case or
starting Lean. The runner guard tests always use it. A batch with insufficient
time for the next full invocation records budget exhaustion rather than silently
lowering that invocation's timeout. Timeout blocking remains conservative even
if a later request raises its process ceiling. Budget accounting is per documented
round directory, under the worktree-wide serial lock; it is not a global accounting
service across unrelated directories or worktrees.

For the bounded one-hour goal corpus, run
`python3 experiments/Determinant/verify_goal.py reports/bench-results/determinant-goal --source-ref 81d4a0e86`
after the audit build. This checks every retained source snapshot, completed pair
order, theorem dependencies and aggregate measurement allowance, then regenerates
all per-variant inventories. It also checks the recorded audit log and requires
the final measured Lean sources to match that retained implementation revision.
Omit `--source-ref` when checking a corpus against the current worktree. It does not
launch Lean or perform measurements.


`relations_bird` implements compact quotient monomials with multiplicative
signatures. It reuses the compact Bird recurrence and its caches. Entry and sum
hooks search for like terms hidden by opaque quotients; only selected monomials
are expanded, directly through their `ExProd` structure. Proofs for expanded
atoms and products are cached. The same signature index aligns the determinant
and target after partial cancellation. `relations_first` disables the stronger
final comparison so audits can check the relation mechanism independently.

Signatures are optimization hints, never proof evidence. They never cancel a
factor against its inverse, since denominators can be zero. A private-factor test
skips searching when the factor representation of the current scalar atoms is
injective on monomials. Atom-table growth invalidates that test. Sum-tail and
factor caches avoid repeating searches; the audit checks cache insertion/reuse,
zero expansion for independent quotients, positive expansion for hidden
cancellation, and ordinary permitted proof dependencies.

`det.relations.maxWork` bounds distinct sum-tail visits; exceeding it declines
explicitly. `det.relations.maxHeartbeats` bounds the complete relation backend,
including the stronger scalar comparison, and cannot increase the caller's
remaining heartbeat allowance. Zero is rejected rather than disabling that bound.
`det.relations.trace` reports search/expansion counts for diagnostics. These
experimental controls do not change production dispatch.

`--candidate relations` and `--reference fresh` isolate the relation hook from
its opaque-quotient control. `--family rankone-diagonal` with symbolic product
denominators tests partial cancellation using a nonzero supplied target for
`I + u*vᵀ`. Keep these manual proof probes outside Mathlib-free value benchmarks.

For this follow-up corpus, run
`python3 experiments/Determinant/verify_relations.py` after the audit build.
It checks retained measurements against their own source snapshots and the
correctness-validated source against `validation/sources.json`. The last measured
source and the final cache/diagnostic fixes are deliberately distinguished; see
[the relation report](../../reports/determinant-relations.md). No measurements
are launched by this verifier. The sum-visit budget covers relation indexing;
the stronger scalar comparison is bounded by heartbeats, not that visit count.
