# Complete replay with supplied operations

The [context record](data/hexrcf-cell-operations/context.json) binds the selected
source trees, retained logs and artifacts. Eight corrected desktop/narrow
captures were opened and inspected; the changed targets have zero local
horizontal overflow. The live memory-limit properties and bounded build
wrappers are retained with the validation evidence.

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
Wrong-conjugate and omitted-original-zero-divisor controls must fail without
leaking metavariables or declarations; interrupts and resource exhaustion remain
terminal. A final declaration reference also requires the fresh consumer's
audit to finish. These are default conformance roots, without a new CI job.

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
production must return exactly `.divisor`. The initial flat/grouped controls
incorrectly expected one coefficient: the existing source translator abstracts
named subjects while leaving surrounding arithmetic in the shared schema.
The final control retains one named coefficient and one original divisor.
The diagnostic failures remain retained and are not final-source validations.

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
zero swap). Its final trace records 298.890s in reached-record collection and
37.866s between collection completion and final acceptance. Earlier appended
lines belong to a failed type-inference attempt; the successful segment is
identified separately. One stack observation sees kernel theorem checking;
it is not a cumulative cost profile. This is a targeted assembly diagnostic,
not a numerical benchmark, scaling law or speedup comparison.

The first successful original-source assembly experiment takes 6m31.165s
at 5.5 GiB peak, followed by a fresh consuming module in 13.743s at 1.3 GiB
with its source dependency cached. The same experiment using the public
quotation API takes 6m57.341s at 6.3 GiB, including its fresh consumer. These
observations use different source versions and do not establish a comparison.
The first portable repository regression passes 11,137 jobs in 10m28.442s
at 8.8 GiB, with both source and consumer completion markers. Its subsequent
refusal-test corrections propagate interrupts and observe declaration rollback
without a test-side state-restoring catch. Intermediate failed or stopped
experiments remain recorded with their narrower scopes.

An earlier manual/optional/conformance selection passes 14,304 jobs. This is
a cached completion after the first selection built the manual and other
regressions but failed the initial mixed-zero test. The final selection takes
6.681s at 618.1 MiB peak with zero swap; those incremental values are not a
before/after comparison. After the public quotation API was added, its broader
selection passes 14,304 jobs in 7m14.992s at 6.4 GiB peak. The corrected
assembled-source selection passes 14,337 jobs in 6m51.985s at 6.1 GiB,
including both completion markers. Neither is a controlled comparison.
At source `d00786311dc609adc8b842102f09b4b27ecb726d`, the selection
passes 14,337 jobs in 3m6.947s at 5.9 GiB with zero swap. It reuses the
assembled proof modules and rebuilds the strengthened real-model tests and
updated manual. These assembly costs remain a limitation of this retained-field
route; they do not establish practical general tactic performance.
The final source `73d0818c4125caf101f45b37e702ee262b14364a` shortens the
manual example's displayed namespace and splits its long type line after a
narrow capture found clipping. Its manual rebuild passes in 2m55.436s at
3.7 GiB; the subsequent cached 14,337-job validation takes 5.246s at
334.9 MiB, with both assembled-proof completion markers. The failed capture
and its exact manual source are retained separately from the corrected captures.
The failed broader run and focused corrections remain retained. All own
Lean/Lake/render/browser work is serial under an aggregate
32 GiB limit with no swap and two Lean threads.

General frozen source/provider/predecessor histories, authenticated quoted
proposals, all-live transport, strict compiled rejection of arbitrary omitted
arithmetic records, general original-source accepted completeness and remaining
realization/stress/performance obligations remain open. In particular, native
missing-record fallback is distinct from kernel acceptance of a saturated
packet. The legacy fixture experiment also does not resolve the separately
reported public-module `Codec.readGraph` reduction boundary.
