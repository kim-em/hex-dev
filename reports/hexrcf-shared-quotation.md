# Sharing a reflection request across scalar and polynomial quotation

[`RootQuote.runWith`](../adapters/HexRCF/RealCoefficients/RootQuote.lean)
runs checked quotation actions with one reflection budget and transaction.
`run` supplies that boundary for a reader with `DecoderM` callbacks. Nested
`quoteWith` actions retain the same state; work performed by a declining
callback remains charged, while its environment changes are restored.
Failures propagate without another solver. Success restores caller
metavariables, and rejection restores every earlier auxiliary declaration.
Returned usage includes charges after the final quoted proof. The existing
`RootQuote.quote` API for ordinary `MetaM` callbacks remains compatible.

[`ScalarQuote.quotePolyWith`](../adapters/HexRCF/RealCoefficients/ScalarQuote.lean)
accepts a complete original `Codec.readPoly` application. It retains the exact
coefficient type, zero/equality instances, literal and full codec arguments,
quotes the owner's finite `Element.signCodec` reader, and composes the existing
`Codec.readPoly_refines` / `Element.signCodec_sound` laws. The resulting ordinary
kernel equation is for the original canonical polynomial reader with the same
predecessor codec. Scalar and polynomial quotation use the same checked codec
signature boundary. Assigned inputs instantiate before work accounting. Input size is charged
before type checking and reduction. Both helpers require the facts list's declared element type to use the original
context under reducible transparency; aliases in that index require explicit
checked type transport. Their final proofs are checked against explicit original-reader
targets. An assigned polynomial reader has the same charge as its expanded
input.

The [case driver](../conformance/HexRCF/SharedQuoteCases.lean) restores both
positions of a polynomial containing repeated coefficient −2√2. Its exact
stored coefficients and the first coefficient's own selected-real value are
proved. The [fresh importing audit](../conformance/HexRCF/SharedQuoteConformance.lean)
re-adds six reachable theorem bodies and three data definitions to the ordinary
kernel with enabled producer diagnostics. All pass the existing producer guard;
the complete transitive axiom closure is exactly `propext`, `Classical.choice`
and `Quot.sound`. Actual owner refinement/sign laws and the supplied checked
scalar packet are required dependencies. An ordinary `module` consumer through
the umbrella also checks the emitted reader bridge.

The finite scalar quote consumes 818 proof nodes, the polynomial quote 1,066,
and the two composed in one request 1,884. Continued/exact/one-below budgets,
post-quotation source charges, charged callback decline, missing facts,
terminal callback failure and late rejection after successful polynomial
quotation are checked. These are request-accounting counts, not claims of
physical sharing or expanded execution cost.

At source `31bc27b91906882443f77490510a4d929f6a4e61`, the six-body/three-definition
shared audit and inherited 13-body/three-definition scalar audit pass the
ordinary kernel and producer guard. The updated focused chapter/audit selection
passes 11,767 jobs in 15.015 s, peak 1.7 GiB/no swap. The full 11,785-job
compatibility selection passes in 4.389 s, peak 269.5 MiB, reusing dependencies
from the retained preceding attempt. That attempt exits1 solely for three
nonexistent target names; its successful actual proof audits do not make the
whole attempt a passing build. The corrected selection includes the actual
`HandlerTests`, `ReifyTests` and `DecisionTests` modules, both libraries,
root/rational/scalar/shared audits, the ordinary umbrella consumer, named
constants and manual chapter. These times include cached dependencies.

Source hashes, commands, full rendering, metadata scopes and inspected
1440 px/390 px captures are in the [current record](data/hexrcf-shared-quotation/resource/context.json).
The [earlier record](data/hexrcf-shared-quotation/context.json) retains the
independently pinned d951490 evidence, initial cde546ecf9 rendering, observed
16 px/4 px narrow-example overflows, all captures and their changed examples.
A live service-limit observation is distinguished from the terminal result
summary. Dependency/umbrella/copyright/line/admission/relative-link/diff checks
pass with their recorded scopes. Own Lean/browser jobs are serial under a
shared hard 32 GiB cap, no swap and two Lean threads.

The retained failed diagnostics explain the choice of the existing whole-reader
refinement law. Direct canonical-array transport triggers a prohibited native
sign reduction; experimental generic array-map rewrites do not eliminate it
and increase the scalar request count to 85,181 and 103,119 at their respective
sources. One experiment was operator-interrupted, not a passing audit, despite
systemd's operator-stop result label. These attempts are not final-source proof
evidence, their transient sources are not all retained, and their build times
are not a matched AB/BA or scaling study. No speedup is inferred.

This is a supplied-reader frontend quotation boundary. It does not authenticate
generic original source/proposal/provider/predecessor histories, produce missing
signs, establish generic root coverage or accepted completeness, finish finite
realization, repair the native inverse/xgcd stress timeout or discharge strict
compiled whole-reader missing-record rejection. Full #10358 remains open.
