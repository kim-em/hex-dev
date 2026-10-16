/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients
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
