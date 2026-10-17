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
signature boundary. Assigned inputs instantiate before work accounting. Sign
facts are charged before checking their declared type/context. The reader and
literal are charged before quotation type checking and reduction; codec
preflight occurs first. Both helpers require the
facts list's declared element type to use the original context under reducible
transparency; aliases in that index require explicit checked type transport.
Their final proofs are checked against explicit original-reader targets. An assigned polynomial reader has the same charge as its expanded
input.

The [case driver](../conformance/HexRCF/SharedQuoteCases.lean) restores both
positions of a polynomial containing repeated coefficient −2√2. Its exact
stored coefficients and the first coefficient's own selected-real value are
proved. The [fresh importing audit](../conformance/HexRCF/SharedQuoteConformance.lean)
re-adds seven reachable theorem bodies and three data definitions to the ordinary
kernel with enabled producer diagnostics. All pass the existing producer guard;
the complete transitive axiom closure is exactly `propext`, `Classical.choice`
and `Quot.sound`. Definition checks validate typing and reductions during that
check; they do not evaluate or normalize stored data or establish the absence
of unexecuted producer calls. Actual owner refinement/sign laws and the supplied checked
scalar packet are required dependencies. An ordinary `module` consumer through
the umbrella also checks the emitted reader bridge. The direct ScalarQuote
module consumer runs the actual polynomial helper on both empty and stored
nonzero polynomials, and uses its emitted proofs in ordinary theorems. Emitted scalar and polynomial data definitions are
also explicitly compiled for compiled clients.

The finite scalar quote consumes 818 proof nodes, the polynomial quote 1,579,
and the two composed in one request 2,397. These counts are asserted in the
case driver. Continued/exact/one-below budgets,
post-quotation source charges, charged callback decline, missing facts,
terminal callback failure and late rejection after successful polynomial
quotation are checked. These are request-accounting counts, not claims of
physical sharing or expanded execution cost.

Canonical `Element.codec` decoding with an explicit codec head stays protected
throughout replay. Expand codec aliases first; that protection excludes aliases. A
callback must supply the exact checked decode equation, or quotation fails
closed. `DecoderM` declines only by returning `none`; a structured error is
terminal even when its constructor is named `providerDeclined`. The nested
polynomial callback driver uses an existing selected-root extension and
requires exactly one predecessor callback and its retained 17 source-node charge.
It also checks a protected bare decoder, a wrong sign only in the second
coefficient, trailing zero coefficients and malformed polynomial heads, with
failure-state restoration. The importing kernel audit additionally forbids
canonical `Element.codec` reduction. All 47 reachable callback/public-module
theorem bodies and 14 definitions pass that stronger guard. The exact
demanded decode helper `quoteDecodeWith` and nested step transport check
projection equalities with an abstract codec, then apply the concrete codec and
its checked equation. Original readers must expose that codec in their syntax;
a late hidden-codec refusal restores completed callback auxiliaries. Nested
exact/one-below budgets pin 9,143 proof nodes and the final 1,006-node charge
after 8,137 consumed nodes. Structured `providerDeclined` is tested as terminal;
ordinary negative tests rethrow heartbeat/depth/internal failures. Unsupported
dependent proof abstraction remains a terminal type/kernel failure.

Polynomial quotation reconstructs the exact decoded coefficient vector as a
`DensePoly` with a checked normalized-vector invariant. An empty vector needs no
scalar evidence; the final stored nonzero coefficient uses the owner's
`restore_sign` and `sign_eq_zero` laws. A trailing zero rejects. The public
`polynomialAccepted` bridge composes the existing `ofCoeffs_toArray` law and
actual `readPoly` definition, so its kernel proof does not compute
normalization or compare coefficients through dependent array-bound proofs.
The full codec argument spine and original zero/equality instances survive.
Exploratory direct field-projection, simplifier and definitional-abstraction
attempts failed; no such branch or diagnostic printing remains in production.

At source `ce6f235e67e3f181755e2a82996d06d179bfef03`, the hardened
14,343-job library/compatibility/audit/manual selection passes in 3 min 15.317 s,
CPU 3 min 56.863 s, peak 2.3 GiB/no swap. A separate ordinary importing module
consumes the emitted nonzero polynomial equation. Public compiled data names
keep generated private proof names out of its exported type; an initial inline
export failed that consumer and remains retained. The 47/14 audit includes this
consumer. New theorem applications pass the original instances positionally;
owner signatures are checked. The empty-vector law avoids inspecting a reduced
proposition by argument position, and two new Meta reductions are charged.

The final 14,322-job render passes in 11.806 s, CPU 13.858 s, peak 1.5 GiB/no
swap. All ten final desktop/narrow captures were opened; changed quotation
content fits 1440/390 px. Primary and supplemental capture runs peak at 8.1 GiB
and 6.2 GiB respectively without swap. Source/log/capture hashes and exact
metadata commands are in the [hardening record](data/hexrcf-shared-quotation/hardening/context.json).
All five source checks and report relative-link checks pass. These cached
build observations are not scaling or matched performance comparisons.

At source `23df34b81fe303b671c2820b889833f8e3fdc7d9`, the full14,343-job
selection passes in4min8.465s, CPU5min29.964s, peak3.2GiB/no swap. It includes
both libraries,46/12 callback/module and7/3 shared audits, inherited13/3 scalar
and42 named-constant bodies, rational/root/handler/reifier/decision compatibility
and the complete manual. The full14,322-job manual render passes in15.908s,
CPU15.674s, peak2GiB/no swap. All10 final desktop/narrow captures were opened;
the changed quotation targets fit1440px/390px. Primary and supplemental browser
passes peak at8.1GiB and4.9GiB respectively, without swap. The first final-render
invocation used the repository directory instead of the scratch renderer and
failed with an unknown target; its log remains retained.

The [23df source-bound record](data/hexrcf-shared-quotation/review-final/context.json)
retains source/artifact hashes, actual audit inventories, all completed public
module and rewrite experiments, final logs, cap wrapper and captures. Metadata
checks pass. Earlier records retain their source-specific counts and results;
the new request counts are not physical-sharing, AB/BA or scaling evidence.

At source `cb5f98ae9ef1c1afc994d39eeb45f0f1e8929729`, the full 14,342-job
validation passes in 3 min 58.464 s, CPU 5 min 8.279 s, peak 3.3 GiB/no swap.
It includes the 18/8 callback/module audit, the existing 6/3 shared and 13/3
scalar audits, 42 actual named-constant theorem bodies, rational/root and
handler/reifier/decision compatibility, both libraries and the manual. The
14,323-job render passes in 23.495 s, CPU 23.688 s, peak 2.2 GiB/no swap.
All ten desktop/narrow captures were opened, including the new predecessor
policy. Local quotation-section targets fit 1440 px and 390 px; no whole-manual
overflow claim follows. The primary browser pass peaks at 8 GiB and the policy
capture at 2.8 GiB, both without swap. These cached-dependency observations are
not matched comparisons or scaling results.

The [earlier source-bound record](data/hexrcf-shared-quotation/review/context.json)
retains selected source hashes, complete logs, failed setup/audit attempts,
commands, inventories and captures with verified artifact digests. Its source
commit identifies the full checkout. The initial nested audit exposed a
canonical-codec reduction and then a native-sign reduction; the abstract-codec
transport preserves the stronger guard. A free-context quotation experiment
failed; the successful direct module consumer uses the existing closed checked
cubic context. It does not establish generic free-context quotation.

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
in the [55edc30a record](data/hexrcf-shared-quotation/transport/context.json).
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
