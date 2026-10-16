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
signature boundary. Input size is charged before type checking and reduction.

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

The finite scalar quote consumes 817 proof nodes, the polynomial quote 1,065,
and the two composed in one request 1,882. Continued/exact/one-below budgets,
post-quotation source charges, charged callback decline, missing facts,
terminal callback failure and late rejection after successful polynomial
quotation are checked. These are request-accounting counts, not claims of
physical sharing or expanded execution cost.

At source `d951490a7ff0a5be7023cb05b67bfa602c6ca11d`, the 11,785-job affected
selection passes both libraries, rational/handler compatibility, all relevant
root/rational/scalar/shared audits, the 42-body named-constant audit and the
manual chapter. Runtime 1 min 29.052 s, CPU 2 min 9.713 s and peak 2.4 GiB/no swap
include reused dependencies. Source hashes, final full rendering and inspected
1440 px/390 px captures are in the [source-bound record](data/hexrcf-shared-quotation/context.json).
The record also retains the initial source's 14,323-job rendering, the observed
16 px/4 px narrow-example overflows and their captures, and the changed final
examples. Dependency/umbrella/copyright/line/admission/relative-link/diff checks
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
