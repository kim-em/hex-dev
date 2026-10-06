# hex-rcf

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

A proof-producing Lean tactic, `rcf`, deciding the univariate fragment of
real-closed-field arithmetic: Boolean combinations of polynomial
(in)equalities in one real variable under a single quantifier over `ℝ` or
over a half-open dyadic interval. The package builds on
[`hex-real-roots`](https://github.com/leanprover/hex-real-roots),
[`hex-real-roots-mathlib`](https://github.com/leanprover/hex-real-roots-mathlib),
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z), and Mathlib. The
tactic targets `ℝ`, so its soundness theorem lives in this same package;
there is no separate `hex-rcf-mathlib`.

# Quickstart

```toml
[[require]]
name = "hex-rcf"
git = "https://github.com/leanprover/hex-rcf.git"
rev = "main"
```

```lean
import HexRCF

example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by rcf
example : ∀ x : ℝ, 0 < x → x ^ 2 + 1 ≥ 2 * x := by rcf
example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by rcf
```

# Functionality

For an in-fragment sentence the compiled builder constructs a squarefree
carrier polynomial, isolates its real roots with Sturm certificates, and
decides the sentence on the resulting cell decomposition of `ℝ`, the
one-variable case of Tarski's theorem. Neither `polyrith` nor `nlinarith`
is complete on this fragment, and `decide` does not apply to quantifiers
over `ℝ`.

- The `rcf` tactic reifies a goal, runs the builder, and replays the
  returned certificate through a small kernel checker.
- `Hex.RCF.decide`, `Hex.RCF.build?`, and the certificate types are the
  programmatic surface beneath the tactic.
- A `false` verdict is diagnostic only: the tactic reports the failing cell
  but never proves a negation. Builder failure is a separate error channel
  and is never reported as `false`.

Optional coefficient solvers can register a monomorphic meta declaration of
type `Hex.RCF.Handler` with `@[rcf_handler]`. The base tries registered names
in `Lean.Name.lt` order only when rational reification encounters unsupported
closed coefficient syntax, including local symbols with explicit equalities
to closed real expressions. A handler explicitly declines, reports a terminal
failure, or returns a proof checked against the original goal. Rational solver
failures never dispatch to another handler. This interface does not itself
provide real algebraic or named-constant coefficient support.

Handlers run with the debug kernel bypass disabled. Before accepting a result,
the base shares repeated expression nodes, checks its type against the original
goal without assigning the goal's metavariables, and audits axiom dependencies.
It closes the candidate over its local variables as a fresh auxiliary theorem,
substituting let-bound locals without evaluating certificate checks in the
elaborator. Lean's ordinary kernel checks it synchronously with the configured
limits and cancellation token. The base requires a theorem, audits it and uses
it in the final proof. Malformed terms, unresolved proofs, different goals,
admitted dependencies and unsafe declarations are rejected.

Elaboration and kernel checking have separate heartbeat counters. Synchronous
kernel checks share their counter within an elaboration task; each call applies
the configured limit without resetting that counter. The check can wait for
earlier background declaration checks. These guarantees assume an ordinarily
checked environment and handlers using normal declaration APIs.

# Verification

Every `true` verdict is kernel-checked. The headline theorem
`Hex.RCF.check_sound` states that any certificate accepted by the public
Boolean checker proves its sentence (`cert.check s = true → s.toProp`), and
the kernel checks that Boolean reduction together with the reifier's
equivalence with the original goal, so no unverified output of the compiled
builder or reifier is trusted. Operational totality of the builder on
in-fragment sentences follows from the completeness theorems of
[`hex-real-roots-mathlib`](https://github.com/leanprover/hex-real-roots-mathlib);
no completeness theorem is stated for `false` verdicts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.

In the `hex-dev` development monorepo, the optional `HexRCF.RealCoefficients`
import extends `rcf` with the documented selected algebraic/common-field inputs
and caller-registered finite bounds. `@[rcf_constant]` registers an exact closed
real subject, an approximation procedure and its containment proof; width and
progress guarantees remain separate. The finite path checks all original
source divisors before proof construction, including cancelled divisions, and
checks frozen bound/subject/version bindings and coverage of used providers,
then validates enclosure, guard and final proofs in the ordinary kernel.
Nonseparating bounds leave guards unresolved. This mode is bounded proof search,
not a complete named-constant field solver.
Positive rational square and higher-root aliases are authenticated against
checked selected roots of `denominator * X^n - numerator`. Closed division by
these aliases preserves original base/exponent/divisor guards and becomes
multiplication by a closed inverse before shared-schema abstraction. The
[rational-root regressions](../conformance/HexRCF/RationalRoots.lean) exercise
actual tactic and prepared replay proofs, a further root over the coefficient
field, half-open domains, terminal false verdicts and zero-divisor failures.
Root bases or exponents with an evaluated zero divisor are refused during
recognition rather than reaching common-field replay. The
[algebraic-base regressions](../conformance/HexRCF/AlgebraicRoots.lean) also
authenticate nested roots, shifted bases and guarded quotients. Frozen power,
polynomial and sign evidence checks the base's selected embedding and the
nonnegative root branch. Degree one accepts negative algebraic bases as the
identity; higher degrees do not acquire a signed-root interpretation.
Nonreciprocal real exponents remain unsupported.
In common-field preparation, unsupported root-base syntax and unsupported
sibling coefficients take precedence over recognition exhaustion. For otherwise supported sources,
`Coefficients.prepare` returns a structured budget error before field construction.
Authentication then proceeds in source order: a terminal failure or exhaustion
stops before later coefficients are authenticated, including later negative bases.
Before common-field search, `rcf.algebraic.commonDegree` bounds the product of
the canonical degrees of distinct selected generators (default 64). This
conservative admission uses the shared exponent budget diagnostic; different
aliases for the same selected generator are counted once. It does not bound
every subsequent operation or prove certificate-search completeness.
The admission also applies to a single generator. For algebraic-base roots,
the root degree times the base's authentication-field degree must fit the same
limit before root production, even if cancellation lowers its minimal degree.
Exactly repeated bases share authentication throughout one recursive preparation. These roots require
supported selected-field presentations and irreducibility certificates;
arbitrary algebraic source conversion is not yet complete.
The finite-bound path applies the root syntax and size checks separately to
each leaf before rational normalization or enclosure proposals; errors there
are terminal in traversal order.
For algebraic-base roots, it authenticates the exact source before proposing
an interval, then proves containment using ordinary fixed-field replay.
Caller registrations therefore compose with supported nested roots, shifted
bases and guarded quotients. A root must authenticate exactly without using
subterm provider bounds. Matched subterm providers are evaluated, frozen and
checked as dependencies; registering π does not admit `Real.sqrt Real.pi`.
A whole-coefficient registration takes precedence. Original divisors are
checked even inside erased terms or empty domains; uninformative combined
bounds remain unresolved.
Zero-divisor detection within a root follows bounded arithmetic evaluation;
earlier exhaustion can prevent that detection, and either outcome refuses the input.
Inverse notation is supported in rational bases and reciprocal exponents,
including `Real.sqrt (2⁻¹)`. Visible rational constructors are lowered in both.
Registered bounds compose with unregistered selected algebraic values and
checked root aliases through separately proved algebraic enclosures. The
[mixed-coefficient regressions](../conformance/HexRCF/MixedConstants.lean)
cover π/e with square/cubic roots, both divisor signs and cancelled divisions;
their ordinary proofs contain literal replay, with no approximation or root
production call.
Recognized rational radicals retain exact singleton bounds. A preparation-local
cache reuses checked enclosures for exact source expressions, including a
divisor reused by an inverse coefficient; it does not merge distinct aliases.
The [named-constant regressions](../conformance/HexRCF/NamedConstants.lean)
and manual supply fixed bounds from existing Mathlib π/e theorems, then prove
the required inequalities, existential witness and guarded inverse. Separate
[coarse-bound tests](../conformance/HexRCF/CoarseConstants.lean) retain refusal
when the supplied evidence leaves a divisor sign unresolved.

`Hex.RCF.RealCoefficients.Reify.prepare` produces the shared source schema,
fixed coefficient valuation and equivalence to the original goal. The optional
adapter is validated through the default `HexRCFRealCoefficients` Lake target
and is not yet published to the split repository. See the
[SPEC](SPEC/hex-rcf.md#planned-real-coefficient-extension).

The explicit fixed-field API also separates preparation and finite replay.
`Coefficients.prepare` authenticates the supported exact algebraic sources,
coefficient order and all original divisors; `Environment.proveReplay` builds
and quotes an ordinary proof through `Replay.check_sound`. `Specialize.prepare`
and `FieldSpecialize.prepare` retain every shared atom, with proved evaluation
and semantic degree. `Replay.Input` binds the complete formula, quantifier,
coefficient order, divisor order and context; its type fixes the polynomial and
selected root. `Replay.build` uses the bounded producer and preflights original
divisors, while `Replay.check` only reads frozen evidence. It returns structured
binding/divisor/evidence/unresolved errors or an accepted Boolean verdict.
False does not produce a proof. `Replay.buildTotal` uses the existing total
exact-field producer and guarantees an accepted verdict for nonzero original
divisors; zero divisors are rejected before production. `buildTotal_spec` proves
this result independently of direct proposal depth. `Environment.proveTotalReplay`
quotes the resulting evidence without embedding the search. The tactic keeps
its bounded default. This exact-field result does not make general source
recognition or irreducibility quotation complete. The fresh
[prepared API regressions](../conformance/HexRCF/PreparedCoefficients.lean) and
[finite replay regressions](../conformance/HexRCF/FiniteReplay.lean) test proof
transport, state restoration, exact bindings, discarded guards and strict
verdicts. This API covers the documented fixed-field fragment; registrations
use the separate finite-bound interface, and general towers remain incomplete.

`RepresentationSpecialize.prepare` also specializes shared atoms into native
coefficient representations using their ordinary arithmetic. Its evaluation
and degree proofs use operation preservation and zero reflection, without
asserting field laws on stored values. The [native sample regressions](../conformance/HexRCF/TowerSamples.lean)
compose it with the owner's complete real-cell and ordinary-sample laws over
a selected algebraic coefficient field, retaining repeated and zero atoms and
half-open guards. `Samples.run` uses those native cells and the shared strict Boolean/quantifier
folds; `run_spec` proves the exact `Prenex.toProp` meaning at arbitrary fixed
coordinates in one parent with an actual real model. The
[formula regressions](../conformance/HexRCF/Samples.lean) distinguish selected
conjugates, coefficient order, diagnostic false results and half-open domains.
`NumberField.run` constructs the native parent directly from an existing
`RealAlgebraicNumber` and accepts its original `QAdjoin` coordinates. The
owner's checked presentation preserves the minimal polynomial and selected
real embedding; `run_spec` proves shared sentence truth at those original
values. `value_eq_ofField` identifies them with the existing frontend
`Coefficients.ofField` conversion, and `run_coefficients` states the result
at those converted real values. `runWith` and `runWith_spec` reuse one checked
presentation across formulas. The [number-field controls](../conformance/HexRCF/NumberField.lean)
find further roots over selected quadratic and cubic fields, distinguish
conjugates and swapped irrational coordinates, include several-real-root,
non-monic and rational generators and a degree-two cubic-field coordinate,
and check zero/cancelled atoms and
half-open endpoints. This is diagnostic production, with ordinary-kernel
correctness laws, rather than frozen replay or source-goal quotation.
`Gather.values` transports ordered coefficients from independently constructed
native contexts through the owner's checked common-context maps. Its
`prepare_eval` and `run_spec` laws preserve coordinates in supplied compatible
models. `gather_subsequence` proves gathering and decision production when each
owner's registered keys form an ordered subsequence of the target keys and its
infinitesimal depth does not exceed the target depth. For example, an owner over
`[β]` can enter a supplied target over `[α, β]`; provider versions and key order
remain fixed. `gather_spec` retains the prefix API. `run_original` additionally
binds coordinates to separately authenticated original models and selected
embeddings. The
[gathering regressions](../conformance/HexRCF/Gather.lean) exercise different
polynomials, selected conjugates, repeated owners, cancellation and a further
root over the common coefficient field. Ordinary-kernel theorems cover
provider-constructed non-prefix gathering and refusal of reordered and stale keys.
`Gather.runFrom?` selects a validated catalog base automatically before native
production. `gather_catalog` proves actual gathering and decision production
from models of admissible catalog prefixes and compatible depth-zero owners;
`runFrom?_original` preserves supplied owner-model values under explicit
factory equations at the selected target realization; keys alone do not
identify an independently registered model.
For an ordered nonempty list of base-field values in a caller's actual
`RealPrefix.Model`, installed as the only nonrational prefix,
`Gather.run_registered_many` derives target selection and the identity-factory
equations and preserves every original value at its source index.
`Gather.run_registered` is its singleton case.
The model carries provider interpretations and relative-transcendence/progress
laws; a bounded `rcf_constant` registration alone does not construct it.
[Catalog controls](../conformance/HexRCF/GatherCatalog.lean) include a false
existential and refusal when no installed prefix admits every original key path.
This is a producer API, not literal replay or source-goal quotation. The manual
gives direct API examples. General frozen tower replay, source authentication
for that backend and joint infinitesimal realization still require the owner
interfaces.

`Realization.exists_real` turns an accepted one-infinitesimal BKR replay into
an ordinary real witness for the complete shared source formula. The fixed
coefficient field has a supplied ordered real embedding; constant lifting
preserves all source atoms, including domain guards. The
[realization regressions](../conformance/HexRCF/Realization.lean) freeze a root
of `X − (1 + ε)` and prove the whole conjunction `1 < x ∧ x ≤ 2`, with changed
context/coefficient, missing-child and invalid-row controls. This direct API
still requires frontend coefficient/divisor authentication and source reification;
it does not discharge general nested or successive-infinitesimal realization.

The exact path also accepts visible checked `AlgebraicNumber.ofNormalized`
constructions packaged with `RealAlgebraicNumber.ofAlgebraic`, and their
`QAdjoin` coordinates converted through `Coefficients.ofField` or directly through
`QAdjoin.toAlgebraicNumber` and a reality proof over a reconstructed real generator.
Closed arithmetic, natural powers and division for these inputs and positive
natural square-root aliases compile into checked common-field coordinates.
Every original divisor is checked before target cell search. Quotient replay
checks a frozen multiplication identity without repeating inverse search.
Sources in one selected field retain its generator and power basis. Quotation
reuses an authenticated source irreducibility proof by kernel-checked transport from its original polynomial to the literal
computed presentation. The
[quartic constructor](../conformance/HexRCF/CertificationInputs.lean) and
[fresh-module proofs](../conformance/HexRCF/CertificationProofs.lean) exercise
a supplied multi-prime certificate beyond the frontend witness languages.
The certificate construction and fresh goal proofs use ordinary public imports.
For a new common defining polynomial, quotation also tries the owner's public
multi-prime certificate API. These certificate languages do not cover every
irreducible common defining polynomial; refusal need not disappear with a
larger search bound and does not imply reducibility.
The fresh regression also proves a goal combining a selected root of
`X³ − 4X + 2` with `√37`, creating a new degree-six defining polynomial
certified through the multi-prime route.
It binds the original isolation square to the literal selected-root replay, preserving the
chosen embedding. Elaboration executes canonicalization; the kernel reduces
the original polynomial and square identities, rather than canonicalization.
These identities must reduce across imports. A transported isolation certificate
without a directly checkable root witness is currently rejected before search.
This extends source conversion; general reconstruction and algebraic-only
producer completeness remain required.

The fixed-field algebraic backend has a proof-backed complete certificate
producer: it reduces repeated roots, refines complete root intervals, records
all required literal signs and evaluates the shared formula on ordinary real
cells. Compiled decision laws cover both verdicts; only a true verdict with
ordinary-kernel replay produces a goal proof. Complete root proposals use the
existing selected number field, with proved source-polynomial correspondence,
sorted coverage and cofinal separation. The complete producer caches that root
list across precision attempts; both builders prepare rational coordinate-sign
queries once. The bounded builder remains
available. The tactic also bounds direct bisection and fallback refinement
through `rcf.algebraic.directDepth` and `rcf.algebraic.maxDoublings`, with
terminal exhaustion and replay diagnostics. This does not give total
registered-constant search or an unlimited proof elaboration budget.

`SelectedFormula.checkRow` and `checkRowWith` check a complete shared-formula
row at one ordinary selected real root. `row_sound`, `row_false` and
`row_domains` preserve the source row and supplied divisor values. The
[frozen selected-root regression](../conformance/HexRCF/SelectedRoot/Proofs.lean)
proves `∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2` in the original native
field, with ordinary kernel and producer-exclusion checks. This row interface
requires a faithful parent model and authenticated source inputs; it is not
complete root coverage, a generic tactic certificate or nested infinitesimal
realization.

`SelectedFormula.checkBytes` and `checkBytesWith` compose the owner's lexical
byte decoder with this row check. Supplied original divisors are checked before
parsing. The outer error preserves decoding and authentication failures,
including version, root-binding and stored-sign failures; evidence rejection
can occur in either layer. Replay errors and diagnostic false remain distinct.
The limits bound lexical decoding only: compiled canonical arithmetic, or cached
arithmetic on a fact miss, can run native production outside those limits.
Decoding also depends on the value codec; the fixture uses the strict sign-fact
codec and its kernel proofs use writer/parser laws without evaluating production.
The fresh byte regression proves the same original real sentence through a
checked writer binding and lexical-limit proof. This still requires a faithful
parent model and source authentication. See the
[byte evidence and scope](../reports/hexrcf-selected-root.md#byte-decoding-of-the-same-selected-row).

The [adapter evidence record](../reports/hexrcf-adapter-evidence.md) maps the
implemented interfaces to conformance, fresh proof examples and retained cost
experiments, and states the remaining completion limits.

The optional adapter can produce a checked tighter generator window with
`rcf.algebraic.signRefinements`. Its original selected root remains bound by
containment and checked root counts; frozen replay performs no refinement.
The option defaults to zero because the
[retained comparison](../reports/hexrcf-window-proofs.md) found no useful
whole-module speedup. Inconclusive Horner signs retain exact query evidence.

The [initial-generator precision comparison](../reports/hexrcf-precision-proofs.md)
retains checked proofs of the same selected-root sentence at eight and sixty-four
bits. It removes full sign queries in that fixture without establishing a
general speedup or changing default precision.
