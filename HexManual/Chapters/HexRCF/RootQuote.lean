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
import HexRCF.SignPacketQuote
import HexRCF.PublicSignPacketValues
import HexRCF.RootHeaderValues
import HexRCF.RootContextConformance
import HexRCF.FrozenSignatureProofs
import HexRCF.ProofFunctionPublic
import HexRCF.QuotientQuotePublic
import HexRCF.TreeQuotePublic
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Quoting a supplied root replay" =>
%%%
tag := "hex-rcf-root-quotation"
%%%

{name Hex.RCF.RealCoefficients.RootQuote.quote}`RootQuote.quote` accepts a Lean
expression for an `Except ε α` replay reader, including structured errors. It returns the reconstructed
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

Quotation follows the representative of a closed quotient when selecting
reducibility boundaries. This lets a formula polynomial stored in a tree map
expose its term list. Protected replay functions and canonical coefficient
decoders retain their existing boundaries. The public regression checks the
original reader for a two-term polynomial:

```lean
open Hex.RCF in
example :
    QuotientQuote.reader = some 7 :=
  QuotientQuotePublic.accepted
```

Its exact 92-node budget succeeds, one node less exhausts, and a wrong term
count rejects. The controls check caller-state restoration; a fresh importing
audit checks nine theorem bodies and four definitions with the unchanged
producer guard and complete standard-three axiom closure.

Tree replay uses its public leaf and split equations before opening the local
node checks. Keeping that boundary explicit avoids kernel conversion through
an entire replay merely to compare two Boolean expressions. The checked
readers retain different values for a valid split and its swapped children:

```lean
open Hex.RCF in
example :
    TreeQuote.splitTrue.toOption =
      some 31 :=
  TreeQuotePublic.split_true

open Hex.RCF in
example :
    TreeQuote.splitFalse.toOption =
      some 37 :=
  TreeQuotePublic.split_false
```

The second reader selects its diagnostic branch; it does not accept the
changed certificate. Readers returning an error abort quotation and restore
caller state. The controls also check exact and one-node-below budgets.
These reader equations still need source binding and real interpretation
before they can prove a real goal.

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
Its fresh importing audit checks 208 actual generated theorem bodies under
kernel producer diagnostics, with only the standard three axioms.

The [cubic regression](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/RootQuoteSource.lean) reads a
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
decline or failure. Both dependent conditional branches are checked. Each
selected branch proof is kernel checked separately before it is used in the
conditional equation. The helper
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
including its primitive projection form. `RootQuote` also transports accepted
canonical callbacks for the constant `ValueCodec.decode` form through the
same abstract codec; both forms have emitted proof-body regressions. Metadata
annotations are ignored for classification while the original term is retained.
Decode transport and nested reader steps are checked with an abstract codec before applying the concrete codec
and its checked equation. The original reader expression must expose that
predecessor codec; expand a hiding definition first. Dependent proof terms may
prevent abstraction; type and kernel failures remain terminal. A late rejection restores
the completed callback's auxiliaries. The fresh importing audit rechecks all
65 reachable callback/module theorem bodies and 14 definitions, forbidding
both native producers and canonical-codec unfolding. Exact and one-below nested
budgets also cover the added transport work: 9,143 proof nodes, with exhaustion
at the final 1,006-node charge after 8,137 nodes were consumed. The predecessor
callback is required to run exactly once and retain 17 source nodes.

All quotation regressions use `maxHeartbeats := 12000000`. The original root and rational
cases use `maxRecDepth := 8192`; scalar, sign-packet, shared, callback/module examples and
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
request's budget and transaction. A declining lookup can be probed again after
reduction; its charges are retained on every call.

```lean
open Lean Hex.RealFormula in
open Hex.RCF.RealCoefficients in
meta def quoteSelectedReader
    (reader registry : Expr)
    (factsFor :
      Expr → Reify.ReifyM
        (Option Expr)) :=
  RootQuote.run reader
    (ScalarQuote.decoderWith factsFor
      (fun expression =>
        liftM <| RationalQuote.decoder
          registry expression))
```

The two-level regression checks one visit to its selected context followed by
one visit to its selected predecessor. Its lookup adds 19 source nodes per visit;
the two charges retain 38 source nodes. It uses 14,374 proof nodes; one node less
exhausts
at the final 925-node charge after 13,449 consumed nodes. Missing facts decline
without proposing another decode to the base callback after refusal.
Wrong-context facts and exhaustion remain terminal and restore the enclosing state.
Generic kernel-error restoration is covered by the root-quotation regressions.

An ordinary `module` consumer also runs the callback factory and exports the
checked scalar reader equation. Its sign follows from the owner's restoration
law, without unfolding the stored element's implementation:

```lean
open Hex.RCF.RecursiveScalarPublic in
example : restored.sign = 1 := sign
```

A fresh importing audit checks the two-level fixture and this public consumer,
including accepted annotated decodes and a charged decline followed by acceptance:
87 actual theorem bodies and five definitions, complete standard-three axiom
closure, and no native producer or canonical-codec reduction. The direct constant
and annotated cases use 12,792 and 12,801 proof nodes. A successful inner decline
and retry uses 15,069 proof nodes and retains all three 19-node source charges.
This helper consumes explicit facts; it does not authenticate original source expressions, discover
predecessor histories, produce missing sign evidence or install the general tactic.

`ScalarPacket.quoteWith` checks a supplied optional sign-packet reader. Its
prepared context has a checked equality to the original context; a caller can
first quote a parent descriptor, freeze that data, and prove the equality.
The helper replaces only that context while reading the supplied packet, then
transports acceptance back to the exact original reader and restores its fact.
The original model, codec, polynomial, sign and graph arguments remain attached.

```lean
open Lean in
open Hex.RCF.RealCoefficients in
meta def quoteSuppliedSignPacket
    (reader prepared same : Expr)
    (predecessor :
      RootQuote.DecoderM) :=
  RootQuote.runWith
    (ScalarPacket.quoteWith
      reader prepared same predecessor)
```

The regression quotes the parent descriptor and one packet for the polynomial
−2X at the selected positive square root of 2. The resulting fact alone supplies
the sign evidence for the canonical coefficient decoder:

```lean
open Hex.RealClosure in
open Hex.RCF.SelectedRootTests in
open Hex.RCF.SignPacketQuote in
example :
    Option.map Data.original.value
      (Except.toOption
        ((Algebraic.Element.codec
          (context := Data.native)
          Data.base.codec).decode
            literal)) =
      some (-2 * Real.sqrt 2) :=
  decoded_value
```

Quoting the parent and packet in one request consumes 121,490 proof nodes.
With the frozen parent and its equality already available, the packet consumes
79,531; a limit one node lower exhausts at the final 23-node charge. Decoding the
coefficient from that fact consumes 966 more nodes in its separate request.
The controls check caller metavariable restoration after successful decoding
and final exhaustion, reject an empty graph, and reject a forged context equality
before decoding. A valid graph paired with the wrong claimed sign or polynomial
is also rejected after decoding, restoring the mutated caller. The importing
audit excludes the old fixture fact list. Accounting sums the syntax checked at
each stage, including repeated occurrences; these are not unique DAG-node counts,
timing or scaling comparisons.

The caller still supplies and authenticates the parent history and packet.
Predecessor arithmetic retains its supplied implementation; this helper does
not establish strict compiled missing-record rejection for deeper parents or
install the general source-goal tactic.
The wholly frozen public-module packet example additionally requires a public
signature-codec literal equation from the owner. The passing fixture and its
fresh importing audit use the existing legacy fixture imports; they do not
establish that fully numerical public-module path.

A separate public-module example quotes a packet for X at the selected real
root of X³−3. Its context slots retain closed applications of the canonical
signature encoder. Both graph nodes and nested moments use that same format;
this example does not assume an equation between the encoder and a frozen
numerical signature. The original optional reader supplies the sole sign fact
used to decode the coefficient. The resulting coefficient has the selected
root's ordinary real value:

```lean
open Hex.RCF.PublicSignPacket in
example :
    coefficientReal =
      Hex.RCF.RootQuoteTests.realRoot :=
  coefficient_value

open Hex.RCF.PublicSignPacket in
example : 0 < coefficientReal :=
  coefficient_positive
```

For a dependent match, quotation moves trailing branch-equality proofs along
the checked equation for the match's subject. This uses ordinary equality
elimination with an abstract subject, then instantiates the checked equation.
Moved proofs are checked separately before later replay steps. The result type
must stay fixed. Independent trailing data is retained. A function with one
proof argument can also move when its result type reduces to a fixed type.
The original function is retained and only its proof input is transported.
Other data indexed by the changed subject or its branch proofs is still refused,
including functions returning such data.
The public consumer checks the preserved result:

```lean
open Hex.RCF in
example :
    DependentQuote.continuedFunction =
      some 29 :=
  ProofFunctionPublic.continued
```

During replay-law
conversion, an explicit checked function boundary is first kept abstract, then instantiated
with the actual function and its public equation. The fresh importing audit
checks the resulting private bodies as well as their full axiom closure.
Codec-dependent branch proofs are generalized with the codec constructor during
reader conversion, including successive canonical decodes. A custom callback
should propose the exact demanded read expression. Literal Boolean values are
handled without consulting that callback.
Wrong signs, changed polynomials and context swaps in either nodes or nested
moments are checked refusal cases. These helpers consume supplied histories
and evidence; they do not install the general real-coefficient tactic.


{name Hex.RCF.RealCoefficients.RootHeader.quoteWith}`RootHeader.quoteWith`
accepts the complete original `RootReplay.readDescriptor` application. It quotes
that reader, obtains the independently parsed raw subject through the public
`readDescriptor_subject` law, and checks that the reconstructed root has exactly
that raw subject. All original instance arguments are retained. The caller runs
the action inside `RootQuote.runWith`, so both reads and the final binding share
one budget and transaction. No pre-existing equation for the proposed root's
header is required.

The public regression constructs a new root and context from that result,
quotes the sign packet for X with fully numerical graph fields, and decodes a
coefficient using its fact. The
coefficient denotes the newly reconstructed root and is positive:

```lean
open Hex.RCF.RootHeaderPacket in
example : coefficientReal = realRoot :=
  coefficient_value

open Hex.RCF.RootHeaderPacket in
example : 0 < coefficientReal :=
  coefficient_positive
```

The fresh importing audit includes the generated binding, packet reader,
coefficient decoding and real-value proofs. It rejects dependencies on the
older fixture's handwritten header and reader equations. Invalid root-reader
versions and counts restore caller state; packet controls also change the
polynomial, sign and node or nested-moment context.

The default quotation rules recognize `Signature.codec.decode` applied to the
canonical encoding of its actual signature argument, using the existing public
roundtrip law. This handles distinct signature subjects without a fixture
callback. It does not connect a separately frozen numerical signature to that
encoding. {name Hex.RCF.RealCoefficients.SignatureQuote.decoder}`SignatureQuote.decoder`
uses the owner's public literal equation and a checked binding of the supplied
JSON to its exact signature. It handles signature payloads selected from frozen
graph fields without running the signature parser during proof construction.
Distinct signature subjects, wrong bindings, exact budgets and one-node-below
budgets are checked in a fresh importing regression:

```lean
open Hex.RCF.FrozenSignature in
example : readFirst.toOption =
    some first :=
  readFirst_checked

open Hex.RCF.FrozenSignature in
example : readSecond.toOption =
    some second :=
  readSecond_checked
```

The cubic packet retains frozen numerical node and nested-moment signatures
for its rational predecessor. A signature's serialization identity does not
validate a registry or selected root, and does not construct literal bindings
for arbitrary root frames in a deeper tower. These helpers consume supplied
readers and histories; they do not discover an
arbitrary real source's selected embedding or install the general tactic.


{name Hex.RCF.RealCoefficients.RootContext.packWith}`RootContext.packWith`
then assembles an actual native root context from a closed retained parent and
its checked descriptor. It keeps the existing native operations, checks the
child signature, and returns the frame's encoding equation. The frame remains
the owner's `rootData` serialization expression. Constructing this typed
context does not freeze that expression or authenticate an arbitrary history.

The same decoded coefficient can be interpreted through the owner's ordinary
real model of the packed context, retaining its selected value and sign:

```lean
open Hex.RCF in
open RootContextCases in
open RootHeaderPacket in
example : model.value coefficient =
    realRoot :=
  value_checked

open Hex.RCF in
open RootContextCases in
open RootHeaderPacket in
example : 0 < model.value coefficient :=
  positive_checked
```

The packing budget covers context and signature proof construction. Model
construction is checked separately; its cost is not included in that packing
count. Exact and one-node-below budgets are tested. A descriptor for the parent
carrier cannot be packed into its child carrier, and the failing call restores
caller assignments and declarations. Fresh importing checks audit the actual
metadata, model and value proofs. The new packing bodies must not evaluate
root-data serialization or graph encoding, in addition to the existing native
producer exclusions. Fully numerical frame/history reconstruction and the
general source-goal tactic remain separate obligations.

{name Hex.RCF.RealCoefficients.RootPrepare.prepareWith}`RootPrepare.prepareWith`
prepares the native context of a reconstructed descriptor for subsequent
quotation. It checks closed inputs and the exact raw-header binding, then
retains the descriptor and context behind checked private definitions. Its
`source` is the original constructed context; `context` is the retained one,
and `same` proves their equality. `rootEq` also retains the descriptor identity.
The supplied cleanliness function is preserved.

```lean
open Lean Hex.RealFormula in
open Hex.RCF.RealCoefficients in
meta def prepareRootContext
    (reader clean : Expr)
    (scalar : RootQuote.DecoderM) :
    Reify.ReifyM RootPrepare.Result := do
  let header ← RootHeader.quoteWith
    reader scalar
  RootPrepare.prepareWith header clean
```

Run this action and subsequent quotation in one `RootQuote.runWith` request.
Combine its decoder with the exact predecessor's scalar and signature
decoders, and use `ScalarPacket.quoteWith` with `context` and `same` to restore
the original reader's equation. The shared proof budget includes retained
data, equations, simplifier visits and generated proof expressions. The
simplifier's step limit is separately configurable; its exceptions remain
terminal. Retention does not freeze root frames, authenticate a real source,
or construct an ordinary-real model. Those conclusions require their existing
separate bridges.
