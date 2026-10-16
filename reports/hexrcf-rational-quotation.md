# Generic rational equations for root quotation

[`RationalQuote.decoder`](../adapters/HexRCF/RealCoefficients/RationalQuote.lean)
provides a generic callback for canonical rational-base payloads, avoiding the
fixture-specific finite scalar whitelist. It recognizes `[0,n,d]`, with a
positive denominator coprime to the numerator.
The complete codec record must be definitionally equal to the supplied
registry's rational-base codec under reducible transparency. Eligibility does
not unfold a selected-root child context. An argument whose inferred type is not the registry type is a terminal
input error. Complete checking still occurs when quotation consumes its proof.
Ordinary definition aliases or already unfolded base codecs may decline. Matching a decoding application alone is
insufficient: a regression keeps the decoding function unchanged while
replacing the encoder and requires refusal.

Native rational arithmetic proposes the value. Ordinary proofs establish its
exact numerator and denominator through the owner's public
`NumberField.decode_payload` equation. `RootQuote.quote` checks that equation
against the exact demanded decode and charges its proof before use. No new
arithmetic, root representation, registry or solver is introduced. The helper
is included in the existing optional umbrella and default adapter target.

The [cases](../conformance/HexRCF/RationalQuoteCases.lean) check zero,
positive/negative fractions, a larger canonical denominator, malformed and
noncanonical payloads, and incompatible codecs. They export the reconstructed
values separately from their public equations, keeping private reconstruction
proofs out of public theorem types. The same generic callback independently
quotes the existing frozen cubic input without using its earlier acceptance
theorems. Its quotation consumes 195,128 proof nodes under the recorded limits;
this is accounting for this input, not a scaling result.

The [fresh importing audit](../conformance/HexRCF/RationalQuoteConformance.lean)
rechecks 188 actual generated theorem bodies under active kernel producer
reduction diagnostics. Its complete transitive axiom closure is precisely
`propext`, `Classical.choice` and `Quot.sound`. Actual public decoding and replay laws are required dependencies. The previous
cubic acceptance modules are absent from the importing environment. The cubic
proof alone must depend on `decode_payload` and must not depend on the previous
finite callback law `decode_integer`. The existing cubic source/real-witness and 220-body
quotation audit also pass in the combined selection.

At the initial source `d938fb5aa97c0c520eca47ef0ac8d492f6000cf8`,
the affected 11,765-job selection passes both RCF libraries, rational handler/reifier/decision
compatibility, algebraic-input/source-preparation conformance, both quotation
audits and the updated manual chapter. Its 10.880 s runtime reuses already
compiled dependencies and successful conformance work. That initial 183-body audit rebuilt in 12 s; the final 188-body scope is recorded
separately below. These are shared-host build observations, not a cold build,
matched performance comparison or general speedup. Historical failed
publication/formatting attempts and successful prototype logs are retained
with their narrower scope distinguished.

The full 14,316-job manual renderer passes in 3 min 33.170 s, peak 3.5 GiB/no swap.
All eight desktop/narrow captures were opened. All 11 paragraph/code targets
in the quotation section fit both 1440 px and 390 px widths with zero local
overflow. This does not claim absence of overflow elsewhere in the book.
Metadata, dependency/umbrella, copyright, source-line, admission and diff
checks pass; the admission scan covers 674 cones/1,584 local modules.
All own builds and browser rendering are serial under a hard aggregate 32 GiB
cap and no swap. Lean builds use two Lean threads. Exact source hashes, commands, raw logs,
render/capture artifacts and scope are in the
[source-bound record](data/hexrcf-rational-quotation/context.json).

This quotes supplied rational-base readers. It does not authenticate original
source coefficients, proposals, registry/provider or predecessor histories, handle extension-context scalars,
supply a general tactic handler, establish accepted completeness, or fix strict
compiled missing-record rejection. The stronger native algebraic-input case
still reaches its diagnostic deadline; see the separate
[rational-point record](hexrcf-rational-points.md). Full #10358 remains open for
those obligations and its remaining realization and performance evidence.

The [revised source record](data/hexrcf-rational-quotation/revision/context.json)
pins `0b3ed6a720d1716d11ffb648b84c4728bc5635e8`. Its 11,766-job selection
passes both quotation audits, rational compatibility, algebraic source/input
consumers and the checked manual chapter. Its 188 generated theorem bodies are
required exactly, including a separate frozen negative-fraction input with raw
`Int.negSucc`. A well-typed selected-root child codec declines within 200,000 raw
heartbeats (`maxHeartbeats 200`). The all-rational original-input build retains every owner as a parent
point, checks both quantifier verdicts and refuses a late original zero guard.
The revised full 14,316-job renderer passes in 4 min 14.158 s, peak 5.8 GiB/no
swap. All eight revised captures were opened; the same 11 quotation-section
targets fit both widths. These source-specific observations supersede the
earlier source's coverage claims without discarding its completed evidence.
