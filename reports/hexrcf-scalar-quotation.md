# Quoting coefficients with checked sign facts

[`ScalarQuote.quote`](../adapters/HexRCF/RealCoefficients/ScalarQuote.lean)
quotes the owner's finite `Element.signCodec` reader using supplied checked
`SignFact` values. It then composes the public `Element.signCodec_sound`
theorem to return an ordinary-kernel equation for the exact canonical
`Element.codec` application and original literal. This is canonical at the
current level with the same supplied predecessor codec, not an unproved
refinement to a different lower-level decoder.

The caller supplies a complete `Element.codec` expression and predecessor
quoting support. Every original implicit codec argument is retained when
constructing the strict reader and transport theorem. This avoids a kernel
type-comparison path that can unfold native sign production merely because
definitionally equal base aliases were reinferred differently. The helper
uses the existing owner records, codecs and laws; it introduces no arithmetic,
coefficient carrier or per-operation framework.

The [case driver](../conformance/HexRCF/ScalarQuoteCases.lean) uses the existing
independently checked scalar packet for polynomial `[0,-2]` in the selected
positive square-root-of-two context. It proves the returned value's exact
stored polynomial/sign and **its own** ordinary-real value `−2 * Real.sqrt 2`.
The independent public source equation has exactly the intended codec and
literal. Its declaration type is structurally identical to the returned
reader equation; the source proof is that previously checked constant.

The [fresh importing audit](../conformance/HexRCF/ScalarQuoteConformance.lean)
pins 12 reachable theorem bodies in the quotation-case module. Eleven pass
the existing kernel producer guard with nonempty diagnostics. The source
constant is separately checked with diagnostics enabled and is required to
perform zero reductions. This is stronger than accepting an empty trace
without checking why: its body and type must first be exactly the expected
constant and type. All twelve are ordinary-kernel checks. Their complete
transitive axiom closure is precisely `propext`, `Classical.choice` and
`Quot.sound`; actual owner decoder/sign laws and checked scalar evidence
are required dependencies.

The literal example consumes 817 proof nodes. Exact and one-below limits,
continued proof/source usage, zero without a sign fact, missing or wrong
facts, malformed/partial codecs and admitted fact proposals are checked.
The one-below limit is verified to exhaust **after** the strict quotation
succeeds; declaration/metavariable inventories must still be restored.
Neither missing evidence nor a failed transport starts the canonical decoder
or another solver. Imported predecessor facts and their own decoding remain
explicit prerequisites.

At source `def227e02ae1ba6fbebdd1c7d60c58c3a99d473d`, the 11,775-job selection
passes both RCF libraries, rational compatibility, scalar and rational
quotation audits, the fresh supplied pi/e body audit and the checked manual
chapter. The 20.340 s runtime includes cached dependencies. The final manual
paragraph breaks are included in the separate full renderer. Full rendering
passes 14,318 jobs in 7 min 52.410 s, CPU 7 min 15.772 s, peak 9.8 GiB/no swap.
All eight final desktop/narrow captures were opened; all 19 quotation-section
targets fit both 1440 px and 390 px widths. Metadata/DAG/umbrella/copyright/
line/admission/diff checks pass; the admission scan covers 675 cones and
1,585 local modules. The [source-bound record](data/hexrcf-scalar-quotation/context.json)
retains hashes, raw successes and failed diagnostics, exact live cap/command
settings, figures and scope. Earlier failed experiments are not final-source
proof evidence, and their transient sources are not all retained.

All own Lean builds and browser rendering are serial under a hard aggregate
32 GiB cap with swap disabled; Lean uses two threads. These shared-host build
observations and proof-node counts are not matched AB/BA performance samples,
a scaling result or a speedup claim. The initially observed native sign
reductions remain in the raw failed logs; the final producer guard is unchanged.

This authenticates supplied scalar literals in a given selected context. It
does not reconstruct generic original source/proposal/provider/predecessor
histories, produce missing evidence, install a general tactic handler, prove
accepted completeness or complete finite realization. Strict compiled
missing-record rejection for whole replay readers and the stronger native
stress requirement remain open. Full #10358 is not complete.
