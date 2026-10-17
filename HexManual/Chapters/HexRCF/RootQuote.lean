/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients
import HexRCF.ScalarQuoteCases
import HexRCF.SharedQuoteCases
import HexRCF.RecursiveScalarPublic
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Quoting a supplied root replay" =>
%%%
tag := "hex-rcf-root-quotation"
%%%

{name Hex.RCF.RealCoefficients.RootQuote.quote}`RootQuote.quote` accepts a Lean
expression for an `Except String` replay reader. It returns the reconstructed
data and an ordinary-kernel equation from the original reader's `toOption` to
`some` of that data. This is an acceptance proof for the supplied replay.
The caller separately composes source binding and real interpretation before
using it to prove the original real statement.

A scalar decoder may propose an equality for the exact demanded decode. The
helper checks its type, dependencies and kernel proof before using it. Returning
`none` declines that scalar proposal and restores its changes. Public replay
laws handle the certificate's graph, moments and sign-table checks; ordinary
conditional laws keep dependent proof arguments attached to the decision they
justify. Temporary reducibility changes never escape the call.

For example, this helper continues a request's existing budget and returns the
updated usage together with the checked equation:

```lean
open Lean Hex.RealFormula in
open Hex.Reflect in
open Hex.RCF.RealCoefficients in
meta def quoteSuppliedRoot
    (reader : Expr)
    (scalar : RootQuote.Decoder)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  RootQuote.quote reader scalar
    config used
```

For a rational predecessor, `RationalQuote.decoder` supplies these proposals
without a fixed list of permitted numerators. It recognizes canonical
`[0,n,d]` payloads with a positive coprime denominator and requires the whole
codec record to match the supplied registry's rational base codec under
reducible transparency. Other contexts decline without unfolding their producer.
The argument's inferred type must be `BaseContext.Registry`; complete proof
checking still occurs when the enclosing quotation consumes the equation.
The codec must be reducibly the rational base codec: ordinary definition aliases
or already unfolded codecs may decline. Numerator and denominator identities are ordinary proofs; the
enclosing quotation checks the proposed equation against the original decode.

```lean
open Lean Hex.RealFormula in
open Hex.Reflect in
open Hex.RCF.RealCoefficients in
meta def quoteRationalRoot
    (reader registry : Expr)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  RootQuote.quote reader
    (RationalQuote.decoder registry)
    config used
```

The registry argument is a Lean expression of type
`Hex.RealClosure.BaseContext.Registry`. This helper supplies scalar equations;
it does not reconstruct registry or provider histories. Regression tests check
positive and negative fractions, noncanonical or malformed payloads, and a
different codec whose decoding function is unchanged. The generic callback
also quotes the same frozen cubic independently of the original finite callback.
Its fresh importing audit checks 188 actual generated theorem bodies under
kernel producer diagnostics, with only the standard three axioms.

The [cubic regression](../../../conformance/HexRCF/RootQuoteSource.lean) reads a
supplied replay for `X³−3` on the open interval `(−8,8)`. A fresh public consumer
proves that the accepted descriptor retains the exact context, polynomial,
endpoints and root-selection metadata. The same descriptor, interpreted through
the proved rational model, yields an ordinary real witness `x³ = 3` with
`−8 < x < 8`. No assumed real root or infinitesimal is supplied.
A separate audit checks the actual proof
bodies and complete standard-three axiom closure. All supplied JSON fields are
frozen constructors, including the rational scalar arrays `[0,n,1]`. The test's
scalar callback supplies the public rational decoding equations, which are
checked at every demanded decode. A separate constructor audit excludes producer
calls from the supplied data. Scalar recognition beyond the rational base, source/provider-history
authentication and context reconstruction remain separate work.

A reader that rejects its input or replay returns structured invalid-provider
evidence. Non-readers and unsupported shapes raise terminal exceptions. A reader hiding
its canonical predecessor codec returns invalid evidence with provider key
`RootQuote.boundary`; it is a terminal caller-shape error. An exhausted
reflection budget remains exhaustion; exceptions, heartbeat limits, recursion
limits and cancellation remain terminal. No error selects another solver.
The failure regressions include a changed count with its unchanged matrix,
well-typed forged equations, inadmissible proposals and callback mutations before
decline or failure. Both dependent conditional branches are checked. The helper
forces ordinary kernel checking even when the caller disables it. A successful
call restores caller metavariables and retains checked auxiliaries together
with the environment effects of accepted callbacks. Rejection and failure restore
the complete saved state.

Canonical `Element.codec` decodes remain protected throughout quotation,
including predecessor decodes with an explicit `Element.codec` head. Expand codec
aliases first; that protection does not cover aliases. Supply a checked equation for that exact decode
through the callback; without one the call fails closed. A `DecoderM` returns
`none` to decline a proposal. A structured error is terminal, including one
named `providerDeclined`. The nested polynomial conformance fixture uses an
existing selected-root extension to require actual predecessor callbacks and
retain their source charges. It also checks a bare protected decoder, a wrong
second coefficient sign, trailing zeros and malformed reader heads.
`ScalarQuote.quoteDecodeWith` retains the exact demanded decode expression,
including its primitive projection form. Projection transport and nested reader
steps are checked with an abstract codec before applying the concrete codec
and its checked equation. The original reader expression must expose that
predecessor codec; expand a hiding definition first. Dependent proof terms may
prevent abstraction; type and kernel failures remain terminal. A late rejection restores
the completed callback's auxiliaries. The fresh importing audit rechecks all
47 reachable callback/module theorem bodies and 14 definitions, forbidding
both native producers and canonical-codec unfolding. Exact and one-below nested
budgets also cover the added transport work: 9,143 proof nodes, with exhaustion
at the final 1,006-node charge after 8,137 nodes were consumed. The predecessor
callback is required to run exactly once and retain 17 source nodes.

All quotation regressions use `maxHeartbeats := 12000000`. The original root and rational
cases use `maxRecDepth := 8192`; scalar, shared, callback/module examples and
fresh body audits use depth 32768. Success under Lean's default limits has
not been established. Each rewrite motive contains the current reader, so
proof storage and charged work can grow with the number of steps times the
reader size. Larger packets can exhaust the default reflection budget.

This API does not register a tactic handler or establish complete root coverage.
The acceptance equation alone does not authenticate original source coefficients,
provider histories or a real model. Its conformance build is proof work rather
than a compiled replay benchmark; the separate strict missing-record obligation
for compiled readers remains.

For a coefficient in a selected algebraic extension,
`ScalarQuote.quote` uses the owner's `Element.signCodec` with supplied checked
sign facts, then composes `Element.signCodec_sound`. Its returned equation is
for the canonical `Element.codec` decoder at the original literal. Missing or
mismatched facts reject without starting that context's sign producer. The
predecessor codec must itself have the required checked decoding support.

Pass the original, fully applied `Element.codec` expression, retaining its
implicit arguments. Reinferring definitionally equal context aliases can make
the kernel unfold a native decoder during type comparison. The helper preserves
those arguments when constructing both the strict reader and its transport:

```lean
open Lean Hex.RealFormula in
open Hex.Reflect in
open Hex.RCF.RealCoefficients in
meta def quoteSuppliedScalar
    (codec facts literal : Expr)
    (predecessor : RootQuote.Decoder)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  ScalarQuote.quote codec facts literal
    predecessor config used
```

The monorepo regression imports `HexRCF.ScalarQuoteCases`. It decodes the
nonrational coefficient −2√2 in the existing selected positive √2 context,
proves its exact stored polynomial and sign, and interprets the returned value
through that context's ordinary real model:

```lean
open Hex.RCF.SelectedRootTests in
open Hex.RCF.ScalarQuoteTests in
example :
    Data.original.value restored =
      -2 * Real.sqrt 2 :=
  restored_value
```

The fresh audit rechecks 13 reachable quotation-case theorem bodies, including this value
identity, with only the standard three axioms and no producer reduction.
The nonzero and zero source equations use their exact previously checked
constants with identical types; their diagnostic traces must contain zero reductions. The other
bodies use the existing producer guard with nonempty diagnostic traces.
The three reachable data definitions, `restored`, `literal` and `empty`,
are also re-added to the ordinary kernel with that producer guard. Literal
data definitions may have an empty reduction trace.

Regressions cover continued/exact/exhausted proof budgets, rollback after the
strict stage succeeds, missing or mismatched facts, zero without a fact,
malformed codec applications and rejection of admitted fact proposals.
Reader size is charged before type checking and reduction. Wrong-context
facts reject before scalar callbacks run; malformed field counts, non-array
literals and trailing polynomial zeros also reject. A successful call preserves
the caller's metavariables. The ordinary bridge is tested in a `module` consumer
that imports only the optional umbrella. A direct `ScalarQuote` module consumer
also runs the actual polynomial quotation helper on zero and nonzero stored
polynomials. A separate importing module consumes the nonzero equation.
Public compiled data definitions keep generated proof names out of exported
equation types. The nested
predecessor callbacks are tested separately in the importing audit.
Assigned input metavariables are instantiated before size accounting; expanded
readers, literals and facts have the same charges through assigned metavariables.
The final transport charge is checked separately from the preflight charge.
The facts list's declared element type must use the codec's context under
reducible transparency; aliases in that index need explicit type transport.
The wrong-context test uses a fresh heartbeat epoch and an actual
2,000,000-raw-heartbeat limit; heartbeat/depth exhaustion is rethrown.

For a polynomial over the same selected extension,
{name Hex.RCF.RealCoefficients.ScalarQuote.quotePolyWith}`ScalarQuote.quotePolyWith`
quotes the coefficient array through its finite sign reader and composes the
owner's `Codec.readPoly_refines`. The stored final coefficient's public sign/zero
laws certify the normalized-vector invariant. An empty vector is handled
separately; a trailing zero rejects. The public polynomial roundtrip law then
assembles the original reader equation without computing normalization or
structural coefficient equality during proof checking.
Pass the complete `Codec.readPoly` expression: the helper keeps its exact
coefficient type, zero and equality instances, codec arguments and literal.
The resulting equation concerns that original canonical polynomial reader.

```lean
open Lean Hex.RealFormula in
open Hex.Reflect in
open Hex.RCF.RealCoefficients in
meta def quoteSuppliedPolynomial
    (reader facts : Expr)
    (predecessor : RootQuote.DecoderM)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  RootQuote.runWith
    (ScalarQuote.quotePolyWith
      reader facts predecessor)
    config used
```

The regression polynomial contains two copies of −2√2. The checked original
reader restores both positions. Its first coefficient has this ordinary-real
interpretation in the selected context:

```lean
open Hex.RCF.SelectedRootTests in
open Hex.RCF.SharedQuoteTests in
example :
    Data.original.value
      (restored.coeff 0) =
      -2 * Real.sqrt 2 :=
  value_zero
```

The fresh importing audit pins seven reachable theorem bodies and three data
definitions, their actual owner refinement and supplied sign evidence, and
the complete standard-three axiom closure. All pass the producer-reduction guard, which also forbids canonical
`Element.codec` unfolding. This
polynomial quote consumes 1,579 proof nodes; composing scalar and polynomial
quotation consumes 2,397 in the same request. Assigned polynomial reader
metavariables have the same charges as their expanded inputs.

`RootQuote.runWith` supplies the transaction for a sequence of `quoteWith`
actions. `RootQuote.run` supplies it for a reader with `DecoderM` callbacks.
Callbacks in this monad consume the same reflection budget. A decline restores
the callback's environment changes while retaining its charges; a structured
failure is terminal. The returned usage also includes charges made after the
last quoted proof. Exact and one-below composed limits, missing scalar facts,
and rejection after successful polynomial quotation are checked. Rejection
restores all auxiliaries created earlier in the request.

This scalar API does not reconstruct provider or predecessor histories,
produce missing signs, or install a general source-goal solver. The strict
compiled missing-record obligation for whole readers remains separate.

`ScalarQuote.decoderWith` composes checked scalar decoding through several
selected-field predecessors. Its lookup receives each exact canonical codec
expression and supplies the sign facts already checked for that context. The
rational callback handles the base field; every nested quote shares the enclosing
request's budget and transaction.

```lean
open Lean Hex.RealFormula in
open Hex.RCF.RealCoefficients in
meta def quoteSelectedReader
    (reader registry : Expr)
    (factsFor : Expr → Reify.ReifyM (Option Expr)) :=
  RootQuote.run reader
    (ScalarQuote.decoderWith factsFor
      (fun expression => liftM (RationalQuote.decoder registry expression)))
```

The two-level regression visits both selected predecessors exactly once and
retains their 38 source nodes. It uses 14,374 proof nodes; one node less exhausts
at the final 925-node charge after 13,449 consumed nodes. Missing facts decline
without invoking another scalar decoder. Wrong-context facts, kernel errors
and exhaustion remain terminal and restore the enclosing state.

An ordinary `module` consumer also runs the callback factory and exports the
checked scalar reader equation. Its sign follows from the owner's restoration
law, without unfolding the stored element's implementation:

```lean
open Hex.RCF.RecursiveScalarPublic in
example : restored.sign = 1 := sign
```

A fresh importing audit checks the two-level fixture and this public consumer:
34 actual theorem bodies and five definitions, complete standard-three axiom
closure, and no native producer or canonical-codec reduction. This helper consumes
explicit facts; it does not authenticate original source expressions, discover
predecessor histories, produce missing sign evidence or install the general tactic.
