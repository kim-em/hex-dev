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

The [cubic regression](../../../conformance/HexRCF/RootQuoteSource.lean) reads a
supplied replay for `X³−3` on the open interval `(−8,8)`. A fresh public consumer
proves that the accepted descriptor retains the exact context, polynomial,
endpoints and root-selection metadata. A separate audit checks the actual proof
bodies and complete standard-three axiom closure. All supplied JSON fields are
frozen constructors, including the rational scalar arrays `[0,n,1]`. The test's
scalar callback supplies the public rational decoding equations, which are
checked at every demanded decode. A separate constructor audit excludes producer
calls from the supplied data. Generic scalar recognition, source/provider-history
authentication and context reconstruction remain separate work.

Invalid replay returns structured invalid-provider evidence. An exhausted
reflection budget remains exhaustion; exceptions, heartbeat limits, recursion
limits and cancellation remain terminal. No error selects another solver.
The failure regressions include a changed count with its unchanged matrix,
a wrong scalar proof and callback mutations before decline or failure. A
successful call retains its checked proof auxiliaries and restores caller
metavariables. Rejection and failure restore the complete saved state.

This API does not register a tactic handler or establish complete root coverage.
The acceptance equation alone does not authenticate original source coefficients,
provider histories or a real model. Its conformance build is proof work rather
than a compiled replay benchmark; the separate strict missing-record obligation
for compiled readers remains.
