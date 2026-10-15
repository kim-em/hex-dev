# Complete replay with supplied operations

The [baseline context record](data/hexrcf-cell-operations/context.json) binds
the selected source trees, retained logs and artifacts. Eight corrected desktop/narrow
captures were opened and inspected; the changed targets have zero local
horizontal overflow. The live memory-limit properties and bounded build
wrappers are retained with the validation evidence.
The [control validation record](data/hexrcf-cell-operations/controls-context.json)
binds the expanded refusal and actual-record dependency checks separately.

[`CellOperations`](../adapters/HexRCF/RealCoefficients/CellOperations.lean)
uses the owners' existing `Replay.Operations` dictionary to check a complete
literal root/cell packet. Its operation equalities retain the ordinary
coefficient storage and original context. The shared sector parser
`CellPacketRead.readUsing` keeps the canonical root/cut indices while validating
supplied row, point, descriptor and linear-head evidence. There is no new
formula language, coefficient representation or arithmetic certificate framework.

`check_eq` identifies the entire result with `CompleteReplay.check`, including
all errors and both verdicts. `check_domains` concludes nonzeroness for every
supplied original-divisor value; `check_sound` proves the shared input sentence
at the model's fixed coefficient valuation.
`accept?` supplies the optional success predicate expected by the owners'
record assembler. Only `.ok true` succeeds there; callers retain `check` for
its typed failures and false diagnostic. Replay does not invoke a producer.

[`RealModel.build`](../adapters/HexRCF/RealCoefficients/RealModel.lean)
constructs an ordinary-real model of a closed retained tower from its supplied
real base model and actual root descriptors, frames and encoding proofs. It
checks each prefix's context and uses `Tower.Model.root`. Successful calls
restore the caller's metavariable state and keep private checked auxiliaries;
failed calls restore the elaborator state. A model still needs source-value
identities before it can justify an original goal. This API does not assert
that an infinitesimal ambient field embeds into the ordinary reals.

The default [operation conformance](../conformance/HexRCF/CellReplay/Operations.lean)
audits 26 actual proof bodies and checks supplied-operation execution with the
existing strict 21-seed coefficient codec. Controls cover both verdicts, false
refusal, late original zero guards, missing cell layouts/sections and stale
radical bindings. The [source quotation](../conformance/HexRCF/CellReplay/OperationsKernel.lean)
rechecks a fresh original goal through `CellQuote.finishOperations`, the
operation equality and canonical soundness theorem. It reuses independently
checked fixture acceptance and
finite codec laws; it is not a fresh reduction of the complete literal reader.
The [public module](../conformance/HexRCF/CellReplay/OperationsPublic.lean)
imports only the optional umbrella and proves generic source soundness and
late-zero refusal. All these actual bodies pass ordinary-kernel checks with
only the standard three axioms. The quotation controls reject false or malformed
predicates, an unrelated proposed proof and a changed source, while a test-only
observer checks both metavariable and local-declaration rollback without
restoring state on behalf of the API.

The default [assembled source](../conformance/HexRCF/CellReplay/Assembled.lean)
instead obtains its operation records through the actual native assembly APIs,
checks the complete literal packet, and quotes the original statement
`∃ x : ℝ, x² - √2 ≥ 0 ∧ x² - √2 ≤ 0 ∧ 0 = 0` through that public entrypoint.
Its [fresh consumer](../conformance/HexRCF/CellReplay/AssembledKernel.lean)
derives `∃ x : ℝ, x² = √2` and audits the actual checked bodies, rather than
only cached axiom metadata. Required dependencies include the supplied-operation
acceptance law, canonical soundness and selected-root model. The audits forbid
the older fixture acceptance/source theorems and producers in the proof.
Separate controls reject the negative-conjugate formula, a √3 source with the
supplied √2 valuation identity, and both caller-identity and program-side guard
count mismatches. Each control asserts its expected diagnostic, checks
metavariable/declaration rollback and propagates every unrelated exception,
including untagged kernel resource failures. Both body audits require
`Element.replayMul_eq` and share a forbidden list covering fixture acceptance,
source proofs, the fixture operation dictionary and producers. A fresh consumer
requires completion of every source refusal, and a declaration reference requires
its audit to finish. These are default conformance roots, without a new CI job.

`CellQuote.finishOperations` first checks the exact supplied acceptance
equation in the ordinary kernel. An expected-proposition annotation retains
the original equation when a reader returns a conversion proof whose inferred
type is reduced to reflexivity. The annotation adds no evidence: the kernel
checks its argument against the original predicate. The API then transports
acceptance with `CellOperations.accept?_iff` and delegates original formula,
valuation and divisor authentication to `finishPacket`.

The [model conformance](../conformance/HexRCF/RealModelConformance.lean)
checks the rational base, the actual selected-root model's coefficient identity
with √2, mismatched base models and depth refusal. Source preparation also
checks a nonzero coefficient with an original zero divisor nested under its
square-root subject. Both proposals' zero statuses are checked before native
production must return exactly `.divisor`. The retained mixed-role control has
one named coefficient and one original divisor. Source versions and narrower
diagnostic attempts are identified in the context record.

A separate build-only experiment composes the actual merged
`NativeChain.ofContext`, `NativeChain.models`, `NativeModels.assembly` and
`NativeAssembly.complete` APIs with `CellOperations.accept?`. It retains the
existing depth-one selected-root context, strict coefficient codec and literal
root/cell JSON. The successful standalone packet experiment calls
`checkedRecordProof`, which checks the conversion from the **original** reader
predicate in the ordinary kernel before exposing the result. It completes
reached-record collection and full packet acceptance. It does not authenticate
arbitrary quoted proposals or construct general frozen histories.

The standalone packet selection passes 11,201 jobs (5m52.876s, 6 GiB peak,
zero swap). Its successful trace segment records 298.890s in reached-record
collection and 37.866s between collection completion and final acceptance.
The context record identifies the segment. One stack observation sees kernel theorem checking;
it is not a cumulative cost profile. This is a targeted assembly diagnostic,
not a numerical benchmark, scaling law or speedup comparison.

These build-only observations use different source versions and cache states.
The context record identifies their exact scopes and retains the completed,
failed and interrupted runs. They are not matched performance comparisons.

| Retained log | Validation scope | Wall time | Peak memory |
| --- | --- | --- | --- |
| `native-source-assembly-4.log` | Original source, inline quotation and body audit | 6m31.165s | 5.5 GiB |
| `native-source-ordinary-1.log` | Fresh consumer with cached source | 13.743s | 1.3 GiB |
| `native-source-assembly-5.log` | Public quotation API and fresh consumer | 6m57.341s | 6.3 GiB |
| `cell-assembled-1.log` | 11,137 jobs, baseline portable controls | 10m28.442s | 8.8 GiB |
| `cell-assembled-2.log` | 14,337 jobs, corrected portable controls | 6m51.985s | 6.1 GiB |
| `cell-assembled-3.log` | Model/manual validation, assembled modules cached | 3m6.947s | 5.9 GiB |
| `cell-operations-model-manual-3.log` | Narrow-layout manual rebuild | 2m55.436s | 3.7 GiB |
| `cell-assembled-final.log` | 14,337 jobs, cached validation at `73d0818c41` | 5.246s | 334.9 MiB |
| `cell-operations-review-assembly-1.log` | Expanded source refusals and actual-record audits | 6m52.875s | 10.5 GiB |
| `cell-operations-review-integration-1.log` | 14,337 jobs, cached assembled proof modules | 14.740s | 1.3 GiB |

The source/consumer selections have both completion markers. The assembled
costs remain a limitation of this retained-field route and do not establish
practical general tactic performance. The typed acceptance theorem is shared
across refusal controls; the positive source check separately exercises the raw
conversion proof through the public quotation API.

The manual example uses a short `Operations` name and a split `RadicalCert`
type to fit narrow pages. The clipped diagnostic capture and its exact source
are retained separately from the eight inspected corrected views. All own
Lean/Lake/render/browser work is serial under an aggregate 32 GiB limit with
no swap and two Lean threads.

General frozen source/provider/predecessor histories, authenticated quoted
proposals, all-live transport, strict compiled rejection of arbitrary omitted
arithmetic records, general original-source accepted completeness and remaining
realization/stress/performance obligations remain open. In particular, native
missing-record fallback is distinct from kernel acceptance of a saturated
packet. The legacy fixture experiment also does not resolve the separately
reported public-module `Codec.readGraph` reduction boundary.
