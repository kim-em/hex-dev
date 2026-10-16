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
signature boundary. Assigned inputs instantiate before work accounting. Input
size is charged before type checking and reduction. Both helpers require the
facts list's declared element type to use the original context under reducible
transparency; aliases in that index require explicit checked type transport.
Their final proofs are checked against explicit original-reader targets. An assigned polynomial reader has the same charge as its expanded
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

The inherited scalar controls check expanded assigned fact lists and pin the
final transport charge separately from fact preflight. The one-below budget
report must identify that final charge. At validation source
`55edc30ad0941239144004260cd5ca1af63580b5`, the full 11,785-job selection passes
in 1 min 27.126 s, CPU 2 min 32.959 s, peak 1.9 GiB/no swap. It includes both
libraries, all root/rational/scalar/shared quotation audits, the ordinary module
consumer, 42 named-constant theorem bodies, the actual `HandlerTests`,
`ReifyTests` and `DecisionTests` modules and the manual chapter. The subsequent
merge at `e574e3fc3b29722124d11daec11510a8dcd1c52a` adds only scalar report
artifacts; all listed code hashes match the validated source.

The final 14,323-job full manual rendering passes in 2 min 52.701 s, peak
2.3 GiB/no swap. All eight final captures were opened, and local targets fit
both 1440 px and 390 px. Source hashes, commands, logs and metadata scopes are
in the [current record](data/hexrcf-shared-quotation/transport/context.json).
The [31bc27b919 record](data/hexrcf-shared-quotation/resource/context.json) keeps
the earlier resource checks and rendering. Its failed first full selection
used three nonexistent target names; the corrected selection passed. The
[d951490 record](data/hexrcf-shared-quotation/context.json) also retains the
initial cde546ecf9 rendering, observed 16 px/4 px narrow-example overflows,
all captures and changed examples. A live service-limit observation is
separate from each terminal result summary. Dependency/umbrella/copyright/
line/admission/relative-link/diff checks pass with their recorded scopes.
Own Lean/browser jobs are serial under a shared hard 32 GiB cap, no swap and
two Lean threads. Build observations include cached dependencies.

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
