# Quoting coefficients with checked sign facts

[`ScalarQuote.quote`](../adapters/HexRCF/RealCoefficients/ScalarQuote.lean)
quotes the owner's finite `Element.signCodec` reader using supplied checked
`SignFact` values, then composes `Element.signCodec_sound`. It returns an
ordinary-kernel equation for the exact original `Element.codec` application
and literal, with the same supplied predecessor codec. It does not assert a
refinement to a different predecessor decoder.

The complete original codec argument spine is retained for the strict reader
and transport theorem. Monomorphic universe and signature arity checks guard
that construction. Assigned metavariables are instantiated before input and proof work is
charged. Reader type checking and reduction follow that charge. Fact contexts
must match the original context under reducible transparency; other aliases
require explicit checked type transport. Wrong-context facts reject before
decoder callbacks run. The final proof target is constructed explicitly from
the original named `ValueCodec.decode` application.

The [case driver](../conformance/HexRCF/ScalarQuoteCases.lean) restores the
coefficient for polynomial `[0,-2]` in the selected positive square-root-of-two
context. Its exact stored polynomial/sign and its own ordinary-real value
`−2 * Real.sqrt 2` are proved. Independent public source equations for zero and nonzero values have the
same types as the returned equations and use their already checked constants.

The [fresh importing audit](../conformance/HexRCF/ScalarQuoteConformance.lean)
pins 13 reachable theorem bodies and the three reachable data definitions
`restored`, `literal` and `empty`. All are re-added to the ordinary kernel
with enabled producer diagnostics. The independent zero and nonzero source aliases must have identical types
and checked body constants and perform zero reductions; the other theorem checks require nonempty traces.
Literal data definitions may have empty traces. No prohibited producer reduces.
The complete transitive axiom closure is exactly `propext`, `Classical.choice`
and `Quot.sound`. Actual owner decoder/sign laws and checked scalar evidence
are required dependencies. The full name inventories are in the retained log.

[`ScalarQuotePublic`](../conformance/HexRCF/ScalarQuotePublic.lean) also uses
the ordinary bridge in a `module` consumer importing only the optional
umbrella. The scalar example consumes 818 proof nodes. Exact and one-below
limits, continued proof/source usage, caller metavariables after success,
late transport exhaustion, zero without facts, missing/wrong facts, wrong
contexts, malformed/partial codecs, non-array/wrong-field-count/trailing-zero
literals and admitted proposals are checked. Failure restores all state,
including auxiliaries from an earlier successful strict quotation. Missing
evidence does not start another solver.

At source `973997c0c15e8059ecf14929c2743613f8e874f9`, the 11,783-job
affected selection passes both libraries, rational compatibility,
root/rational/scalar quotation, the ordinary-module consumer, the 42-body
supplied pi/e audit and the checked manual chapter. Runtime 1 min 26.754 s,
CPU 2 min 19.767 s and peak 1.8 GiB/no swap include reused dependencies.
Assigned readers and expanded assigned literals receive the same charges as
their direct forms. Wrong-context rejection is checked with a fresh actual
`Core.Context.maxHeartbeats` limit of 2,000,000 raw heartbeats; heartbeat and
recursion-depth errors are rethrown rather than counted as successful refusal.
The earlier `withOptions` setting did not enforce that core limit; its
[historical record](data/hexrcf-scalar-quotation/revision/context.json) states
that limitation. Malformed codec applications are tested; corrupting library
declaration signatures is not a test control.

The full renderer, inspected captures, exact source/artifact hashes, commands,
name inventories and successful/failed diagnostics are retained in the
[current source-bound record](data/hexrcf-scalar-quotation/final/context.json).
Earlier [source-bound evidence](data/hexrcf-scalar-quotation/context.json)
remains separately pinned. Transient failed-development sources are not all
retained. Dependency/umbrella/copyright/line/relative-link/diff checks pass.
The fixed admission scanner covers 675 existing cones / 1,585 modules; generated
proof dependencies receive the separate complete axiom audit above.

All own Lean and browser jobs are serial under a shared hard 32 GiB limit,
with no swap and two Lean threads. Build observations and proof-node counts
are not matched AB/BA samples, scaling results or speedup claims.

This authenticates supplied scalar literals in a given selected context.
Generic original source/proposal/provider/predecessor authentication, missing
evidence production, the general tactic/accepted completeness, realization,
strict compiled whole-reader missing-record behavior and remaining runtime/
scaling obligations are not completed by this API. Full #10358 remains open.
