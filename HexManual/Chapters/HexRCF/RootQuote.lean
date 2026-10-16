/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients
import HexRCF.ScalarQuoteCases
import HexRCF.SharedQuoteCases
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
evidence. Non-readers and unsupported shapes raise terminal exceptions. An exhausted
reflection budget remains exhaustion; exceptions, heartbeat limits, recursion
limits and cancellation remain terminal. No error selects another solver.
The failure regressions include a changed count with its unchanged matrix,
well-typed forged equations, inadmissible proposals and callback mutations before
decline or failure. Both dependent conditional branches are checked. The helper
forces ordinary kernel checking even when the caller disables it. A successful
call restores caller metavariables and retains checked auxiliaries together
with the environment effects of accepted callbacks. Rejection and failure restore
the complete saved state.

The quote regressions use `maxHeartbeats := 12000000` and `maxRecDepth := 8192`;
the fresh body audit uses depth 32768. Success under Lean's default limits has
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

The fresh audit rechecks 12 reachable quotation-case theorem bodies, including this value
identity, with only the standard three axioms and no producer reduction.
One source equation is the exact previously checked constant with an identical
type; its diagnostic trace is required to contain zero reductions. The other
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
that imports only the optional umbrella.

For a polynomial over the same selected extension,
{name Hex.RCF.RealCoefficients.ScalarQuote.quotePolyWith}`ScalarQuote.quotePolyWith`
quotes its finite sign reader and composes the owner's `Codec.readPoly_refines`.
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

The fresh importing audit pins six reachable theorem bodies and three data
definitions, their actual owner refinement and supplied sign evidence, and
the complete standard-three axiom closure. All pass the existing
producer-reduction guard. This
polynomial quote consumes 1,065 proof nodes; composing scalar and polynomial
quotation consumes 1,882 in the same request.

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
