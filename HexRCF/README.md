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

`Hex.RCF.RealCoefficients.Reify.prepare` produces the shared source schema,
fixed coefficient valuation and equivalence to the original goal. The optional
adapter is validated through the default `HexRCFRealCoefficients` Lake target
and is not yet published to the split repository. See the
[SPEC](SPEC/hex-rcf.md#planned-real-coefficient-extension).

The exact path also accepts visible checked `AlgebraicNumber.ofNormalized`
constructions packaged with `RealAlgebraicNumber.ofAlgebraic`, and their
`QAdjoin` coordinates converted through `Coefficients.ofField` or directly through
`QAdjoin.toAlgebraicNumber` and a reality proof over a reconstructed real generator.
Closed arithmetic, natural powers and division for these inputs and positive
natural square-root aliases compile into checked common-field coordinates.
Every original divisor is checked before target cell search. Quotient replay
checks a frozen multiplication identity without repeating inverse search.
Sources in one selected field retain its generator and power basis. Quotation
reuses an authenticated source irreducibility proof only when its polynomial
type exactly matches the computed presentation. The
[quartic constructor](../conformance/HexRCF/CertificationInputs.lean) and
[fresh-module proofs](../conformance/HexRCF/CertificationProofs.lean) exercise
a supplied multi-prime certificate beyond the frontend witness languages.
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
