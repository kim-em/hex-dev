# Quoting coefficients with checked sign facts

[`ScalarQuote.quote`](../adapters/HexRCF/RealCoefficients/ScalarQuote.lean)
quotes the owner's finite `Element.signCodec` reader using supplied checked
`SignFact` values, then composes `Element.signCodec_sound`. It returns an
ordinary-kernel equation for the exact original `Element.codec` application
and literal, with the same supplied predecessor codec. It does not assert a
refinement to a different predecessor decoder.

The complete original codec argument spine is retained for the strict reader
and transport theorem. Monomorphic universe and signature arity checks guard
that construction. The reader's size is charged before its type check and
reduction. Wrong-context facts reject before decoder callbacks run.

The [case driver](../conformance/HexRCF/ScalarQuoteCases.lean) restores the
coefficient for polynomial `[0,-2]` in the selected positive square-root-of-two
context. Its exact stored polynomial/sign and its own ordinary-real value
`−2 * Real.sqrt 2` are proved. The independent public source equation has the
same type as the returned equation and uses its already checked constant.

The [fresh importing audit](../conformance/HexRCF/ScalarQuoteConformance.lean)
pins 12 reachable theorem bodies and the three reachable data definitions
`restored`, `literal` and `empty`. All are re-added to the ordinary kernel
with enabled producer diagnostics. The exact source alias is required to
perform zero reductions; the other theorem checks require nonempty traces.
Literal data definitions may have empty traces. No prohibited producer reduces.
The complete transitive axiom closure is exactly `propext`, `Classical.choice`
and `Quot.sound`. Actual owner decoder/sign laws and checked scalar evidence
are required dependencies. The full name inventories are in the retained log.

[`ScalarQuotePublic`](../conformance/HexRCF/ScalarQuotePublic.lean) also uses
the ordinary bridge in a `module` consumer importing only the optional
umbrella. The scalar example consumes 817 proof nodes. Exact and one-below
limits, continued proof/source usage, caller metavariables after success,
late transport exhaustion, zero without facts, missing/wrong facts, wrong
contexts, malformed/partial codecs, non-array/wrong-field-count/trailing-zero
literals and admitted proposals are checked. Failure restores all state,
including auxiliaries from an earlier successful strict quotation. Missing
evidence does not start another solver.

Source `d2627df9111717a92029321280b2b92955e095d8` passes the 11,783-job
affected selection: both libraries, rational compatibility, root/rational/scalar
quotation, the ordinary-module consumer, the deep supplied pi/e audit and the
checked manual chapter. The 1 min 26.026 s build peaks at 3.4 GiB/no swap;
final audit inventories/manual text pass an 11,765-job selection in 23.652 s,
peak 4.3 GiB/no swap. The final cached 11,783-job selection takes 5.003 s,
peak 443.4 MiB. These include reused dependencies, not isolated tactic timings.
The full 14,318-job renderer passes in 3 min 39.250 s, peak 4.3 GiB/no swap.
All eight captures were opened; all 19 local targets fit both 1440 px and 390 px.
Exact hashes, commands,
all name inventories and successful/failed diagnostics are in the
[current source-bound record](data/hexrcf-scalar-quotation/revision/context.json).
Earlier [source-bound evidence](data/hexrcf-scalar-quotation/context.json)
remains separately pinned; transient failed-development sources are not all
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
