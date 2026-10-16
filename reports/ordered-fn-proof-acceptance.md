# OrderedFn computational proof and manual acceptance

`HexOrderedFn` completes Phases 6–7 with the native quotient and infinitesimal
compiler replacements. Its [Theory companion](ordered-fn-declaration-review/theory-acceptance.md)
already completes those phases independently. This acceptance does not promote
any transitive input, accept the downstream real-closure algorithms or establish
split-package publication eligibility.

## Individual API and proof review

The [computational assessment](ordered-fn-declaration-review/computational.md)
examines every handwritten nontrivial declaration in the five production modules
at its recorded source. The [current source record](ordered-fn-declaration-review/core-acceptance-source.json)
binds all sixteen production modules, including both umbrellas. `Search`, `Real` and
`Extension` are byte-identical to that assessment. The two changed modules have
individual supplemental assessments:

| Module | Current declaration treatment |
| --- | --- |
| `Oracle` | The [five-row quotient assessment](bench-results/ordered-fn-positive-quotient/README.md#declaration-assessment) covers the preserved `div?`, two private Rat-order helpers, the native `divImpl` and its whole-function compiler equality. |
| `Infinitesimal` | The [six-row sign/scan assessment](bench-results/ordered-fn-sign-scan/README.md#declaration-assessment) covers both preserved reference definitions, both native implementations and both compiler equalities. |
| `Search`, `Real`, `Extension` | The original individual assessment applies to unchanged bytes: actual trial recursion, finite success versus progress, width normalization, canonical-fraction arithmetic, fixed registration and representation transport. |

The [ten core retention decisions](ordered-fn-declaration-review/core-api.md)
address the original zero-reference rows individually, including the private
termination instance. Public characterizations, simp rules and storage equations
have useful contracts even when elaboration or anonymous examples leave no named
edge. No production caller is invented for an unused public rule. The historical
49-row table contains ten core and 39 companion rows; the later 33-row companion
set is not its complement. Frozen inventories keep their original source and
reference-count scopes.

The private `accessibleWf` instance is used by the `firstSome` termination
annotations. `inv_le_of_pos` is used by `quotient_corners`, which supplies both the
native result's order proof and `div_eq_impl`. The compiler registrations consume
the implementation twins. These are used implementation/proof helpers, rather
than alternative algorithms retained without a caller.

Characterizing lemmas expose first successful trials, literal transport, exact
widths and finite output. [Automation and imports](ordered-fn-declaration-review/quality.md)
keep terminating constructor/width normalizations in simp; unbounded recursion,
semantic witness choice and conditional progress remain explicit. Core bounds
prove endpoint order, not containment. Registration supplies executable providers
and erased progress, not transcendence or an order proof. The companion supplies
containment, relative transcendence over the whole predecessor field and
same-subject transport hypotheses. Original expression divisor obligations remain
with expression consumers.

The unchanged RationalFn umbrella imports retain their public re-exports for
compatibility. The new `Init.Util` import supplies the core pointer-equality
shortcut with its proof argument. No Hex `unsafe`, `implemented_by`, new axiom or
runtime oracle is introduced. Computational imports remain independent of
Mathlib, Tau Ceti, companions and HexInterval. Existing names and namespaces are
preserved; the new implementation names and equality names are short and describe
the actual operation.

## Native execution, trust and construction evidence

The three kernel reference definitions are marked noncomputable, with proved
`@[csimp]` replacements for native code. Their whole-function equalities preserve
arbitrary outputs, empty/all-zero scans, unshared coefficients, all predecessor
sign procedures and denominator refusals. The equalities do not assume a provider,
linear order or sharing. Native execution uses Lean's actual scan, rational
arithmetic and accessible trial search; no proof term or external oracle supplies
a result. Generated C and separate native executable reconstructions are bound
in the optimization reports.

The current `HexOrderedFnTheory.LintTests` lints both public library roots,
including theorem documentation, and audits every owned compiled constant in
both complete production import closures. It rejects missing/unexpected modules,
owned axioms, empty selections and dependencies beyond `propext`,
`Classical.choice`, `Quot.sound`. The existing core tests additionally pin the
three compiler equalities' exact axiom sets. This covers generated declarations
as well as handwritten proofs: 276 core constants in six modules and 298 companion
constants in ten modules pass. Lint and axiom counts do not replace individual
API judgments.

The core's field dictionary reuses canonical RationalFn arithmetic. The
companion's localization injectivity, nonzero denominator, Hahn interpretation,
native-dictionary identity and order-transfer proofs are the Lean-checked field
construction evidence. The [companion acceptance](ordered-fn-declaration-review/theory-acceptance.md#semantic-hypotheses-and-field-construction)
states their hypotheses and limitations. No external irreducibility claim or
bundled transcendental provider is needed by this computational API.

## Computational regression and retained Phase-4 scope

The [complete comparison](bench-results/ordered-fn-final-comparison/README.md)
passes all 17 families, eight parameters each and three trials: 816 completed
arms, 136 parameter comparisons, matching answer hashes, zero failed arms and
zero regressions under the unchanged independent-arm-median 10% rule. The
1,690-file archive retains all raw output, source/build/SDK bindings, protocol,
consumed reservation and setup/control records. Offline replay recomputes every
derived result with the byte-identical committed follow-up analyzer. Six negative
controls reject corrupted data, omissions, altered results, affinity and
reservation records. Replaying evidence performs no measurements.

The historical arm is a fresh, isolated build of the original committed baseline
`ee490f54889e2db8170c8b9fc6e8568f8a978bbe` with its sixteen pinned requirements and
Lean 4.34.1. The candidate is `b4e1e1522a81b09205ff792f8b1d0dc650a63e37` with its own
pinned requirements and Lean 4.35.0-rc3. Baseline selection preceded timing. Its
fresh binary differs from the old retained executable; this is not a recovered
original build or an artifact-identical retest. It is the full unchanged baseline
source, compared with the meaningfully changed implementation. The comparison
has no causal attribution solely to API polishing or either optimization.

Both older captures and their failed findings remain intact. Every old flagged
parameter is included in the new complete passing comparison. The predeclared
source-pair reservation prevents an unchanged repeat, including one obtained by
swapping baseline binary bytes. No rerun or discarded completed sample is used to
obtain this pass.

The [Phase-4 report](hex-ordered-fn-performance.md#evidence-scope) retains its
scientific models, comparators, profiles and original source attributions. The
new quotient branch reduces a constant exact-operation count; the zero guard
reads storage; coefficient scanning retains its structural fallback. These do
not enlarge the scoped fixed-depth/search upper-bound models. The large third-
level gain is specific to the measured shared-padding specialization. No generic
unshared-zero speedup or uniform precision/depth claim is inferred. The complete
Phase-6 raw-loop comparison does not supply new runner signal-floor eligibility,
replace scaling evidence or convert a smoke/proof timing into a performance pass.
Tower8/MetiTarski and clean-versus-eager integration remain with #10378.

## Conformance and documentation

Existing kernel tests cover bounds, finite signs, poles, zero, original denominator
conditions, provider transport and successive infinitesimals. The native emitters
produce the unchanged 80 infinitesimal and 122 real fixtures; pinned Z3/FLINT and
exact Fraction oracles pass them. The test-only Liouville fixture exercises the
actual registered total sign/approximation path and native dictionary, without
adding a bundled provider or a computational Mathlib dependency.

The [chapter](../HexManual/Chapters/HexOrderedFn.lean) explains the computational
and semantic boundaries, source-derived signatures, finite signs, registered
constants, same-subject transport, successive infinitesimals and the Mathlib
correspondence. Its existing examples and both development READMEs are reused.
There is no separately anchored tutorial for this library. The READMEs accurately
state that both packages are unreleased; ordinary monorepo imports do not imply
availability from published companion packages.

Validation includes both public libraries, complete tests and lint/axiom target,
the native Liouville integration, the full monorepo build and manual, import/DAG,
benchmark/proof boundary, named-admission and phase/manual checks. The current
manual is rendered and inspected at desktop and narrow widths. The native source
and configuration bytes are checked against the measured candidate; unchanged
benchmark inputs and fixtures are reused rather than measured again.

Only `HexOrderedFn.done_through` advances from 5 to 7. The companion remains at 7;
all other phase counters and the release manifest remain unchanged. This is local
proof/API/manual acceptance, with no claim that the real-closure family or its
transitive inputs are ready for distribution.
