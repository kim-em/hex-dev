# Frozen ordinary selected-root row

The [fresh source proof](../conformance/HexRCF/SelectedRoot/Proofs.lean) concludes
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2` through the original native
selected field. It retains the equation and both bound atoms at one ordinary
real root. The existing `TotalAlgebraicProofs.further_section` is an independent
polynomial-quotient tactic cross-check.

The fixture has one coefficient, three source atoms, degree-two parent and
child defining polynomials, and two selected-root levels. Its frozen JSON has
86,316 bytes. The lower and upper root graphs contain one vertex each, the
source row five, and the 37 scalar packets one each: 44 stored graph vertices
and 44 expanded tree occurrences. This fixture establishes no DAG-sharing gain
or degree/atom/width/precision/depth scaling verdict.

The upper root is `Descriptor.ofChecked` over independently parsed raw data
and a structurally expanded literal graph. Cached predecessor operations are
used for both specialization and replay. Kernel diagnostics require active,
nonempty counters and reject unfolds of the listed native root/sign producers
while checking all 37 scalar-packet acceptances, three upper-data parser
acceptances, the upper-root check, the row check and five collected refusals.
The rational parent construction, separately elaborated source theorems and
direct codec/zero-divisor controls are outside this diagnostic guard; they
still receive ordinary kernel and axiom checks. Zero unresolved requests is
checked separately. Scalar restoration retains literal key/sign fields using
the owner's `Context.readSignFact_fields`; subsequent field lookup needs the
rational key parser rather than the entire certificate reader.

## Ordinary build observations

These are operational Lake build captures on a shared host, with default build
parallelism. They are not fixed-schedule scientific comparisons and support no
speedup claim. No completed observation was discarded or retried for host
activity. [Context and exact source hashes](data/hexrcf-selected-root/build-context.json)
record the post-build host activity; this is not a pre-run quiet-host test.

| Build | Elapsed | Largest child RSS | Capture scope |
| --- | ---: | ---: | --- |
| [Frozen fixture](data/hexrcf-selected-root/fixture-build.log.gz) | 140.12 s | 9,271,492 KiB | All original 21 fixture outputs removed once; owner/adapter dependencies warm. Includes data, scalar acceptance, root/row quotation, fresh original-goal proof, refusals and complete audits. |
| [Guarded replay/refusals](data/hexrcf-selected-root/guarded-build.log.gz) | 140.75 s | 9,258,528 KiB | Incremental fixture rebuild with all generated scalar/parser acceptances guarded, redundant root replay removed and the false-to-true row forgery rejected. Dependencies and unchanged fixture modules warm; [exact source/context](data/hexrcf-selected-root/guarded-build-context.json). |
| [Affected adapter/conformance/manual](data/hexrcf-selected-root/affected-build.log.gz) | 353.86 s | 14,809,424 KiB | Default optional adapter, all RCF conformance modules, handler/reifier regressions and manual. Some outputs, including the fixture, were already warm. The existing RCF chapter built in 205 s. |

RSS is the largest waited-for child, not an aggregate concurrent-memory
measurement. No compiled family-driver timing is included.

The public row API requires a faithful real parent model and authenticated
source inputs. Its divisor theorem concerns the supplied values; source
identity/guard collection remains a caller obligation. A false row is a
counterexample at that point, not a false existential decision. Complete root
coverage, generic frontend certificate production/progress and general finite
joint nested/successive-infinitesimal realization remain outside this fixture's
evidence. The full [adapter inventory](hexrcf-adapter-evidence.md) retains those
completion limits.


## Byte decoding of the same selected row

[SelectedBytes](../adapters/HexRCF/RealCoefficients/SelectedBytes.lean) composes the
owner's byte decoder with the existing selected-root row checker.
`checkBytesWith_eq` preserves every result under the same eight equal supplied
operations. `bytes_evidence`, `bytes_domains`, `bytes_spec`, `bytes_sound` and
`bytes_false` recover the actual decoded packet, original supplied divisors and
truth at the same ordinary selected point. `bytes_decoded`, `bytes_rejected`
and `bytes_zero` preserve row refusals, unchanged decoder errors and zero-divisor
precedence. The outer `Except String` retains decoding and authentication
failures, including version, root-binding and stored-sign failures. Evidence
rejection can occur in either layer;
diagnostic strings select no solver. This is not the full frontend's typed
search-exhaustion contract.

`Codec.Limits` bound lexical decoding only. Compiled canonical arithmetic, or
cached arithmetic on a fact miss, can run native production outside those
limits. Whether decoding avoids production depends on the supplied value codec;
the fixture uses the strict sign-fact codec. Its kernel proofs compose the
writer/parser laws without evaluating production branches. Equal supplied
operations alone do not guarantee production-free compiled replay.

The [fresh byte proof](../conformance/HexRCF/SelectedRoot/ByteProofs.lean) concludes
the original real sentence from the actual 38,990-byte owner encoding. The
[kernel writer binding](../conformance/HexRCF/SelectedRoot/ByteData.lean) checks the
constructor bytes, and the separate [lexical-bound theorem](../conformance/HexRCF/SelectedRoot/ByteBounds.lean)
feeds the owner's `parse_write` law. It checks byte, nesting and integer-token
limits rather than assuming parser success. The [complete audit](../conformance/HexRCF/SelectedRoot/ByteAudit.lean)
checks all 167 literal definitions, including private auxiliaries if reached,
with only the listed UInt8 primitives; it separately checks complete theorem
axiom inventories. It also rechecks five byte acceptance proof bodies with
active, nonempty kernel diagnostics excluding the listed native producers.
The byte count is an ordinary-kernel checked conclusion. [Controls](../conformance/HexRCF/SelectedRoot/ByteChecks.lean)
include an ordinary-kernel false row/counterexample and wrong-coefficient
refusal, plus compiled malformed/truncated/byte/depth/digit/stale/context/zero-precedence
checks and byte-level coefficient/row-sign forgeries in both result layers. Compiled answers are not proof evidence.

The existing deterministic converter also proposes this byte module from the
retained JSON. Its exact equality to the owner writer is proved in Lean.
No producer, refinement, root isolation, gcd or BKR search is invoked by the
converter.

[Retained source hashes and build context](data/hexrcf-selected-bytes/build-context.json)
scope the historical quotation and affected-build captures. In the [byte audit build](data/hexrcf-selected-bytes/byte-audit.log.gz),
the historical source versions built with dependencies warm: `ByteBounds` module wall time
was 182 seconds, `ByteData` 38 seconds and `ByteProofs` 14 seconds.
Those timed `ByteData`, `ByteProofs` and converter inputs predate the final
files; only `ByteBounds` is unchanged. This build did not capture peak memory. The [affected build](data/hexrcf-selected-bytes/affected-build.log.gz)
passed 13,619 Lake jobs in 255.57 seconds, with largest-child RSS 12,467,252 KiB;
the byte modules were already warm. These are operational observations,
not paired comparisons, a cold full-tactic timing or a scaling claim.

The [integration build](data/hexrcf-selected-bytes/integrated-build.log.gz)
passes 13,841 Lake jobs against the merged owner APIs, including the optional
adapter, byte audit and manual. The [affected conformance build](data/hexrcf-selected-bytes/integrated-conformance.log.gz)
passes 10,992 jobs, including all RCF conformance and rational handler/reifier
compatibility. The context record pins their exact source inputs separately
from the historical cost observations. The separate
[acceptance build](data/hexrcf-selected-bytes/acceptance-build.log.gz) checks the
byte count, forgeries, truncation and five proof-body diagnostics in 10,931 jobs;
its source inputs are pinned in the same context record.

The model/source obligations and pointwise false interpretation above remain.
Bytes for a supplied immutable context do not provide arbitrary context-catalog
reconstruction, complete root coverage, algebraic accepted-certificate progress
or finite joint nested/successive-infinitesimal realization.

## Original-packing arithmetic

The [original-packing regression](hexrcf-selected-packing.md) replays row
arithmetic using 42 records captured from historical row collection plus one additional vanishing
polynomial. Named packet-to-record laws, canonical-zero and missing-key
controls and complete literal/axiom/proof-body audits validate this separate
route. Coefficients, the upper root and packet decoding still use the existing
scalar fixture; this is not a generic context or finite-Gamma exporter.
