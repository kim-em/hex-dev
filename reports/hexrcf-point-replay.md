# Frozen ordinary points and source quotation

`PointReplay.check` preflights every supplied original divisor, restores one
literal point through a strict coefficient codec, evaluates the complete
ordered specialized sign row, and folds the shared Boolean matrix. Its five
supplied equal operations in `checkWith` preserve every accepted/rejected result.
`row_signs` composes the owner's polynomial interpretation with shared
specialization. `check_fields` retains the decoded point, divisor result and
matrix evaluation; `check_domains` proves the original guards nonzero.
`check_sound` gives one ordinary real witness. `check_false` only disproves a
universal sentence at that point, never decides a false existential.

`PointBuild.build` uses the owner's actual sorted, deduplicated native family.
It proposes parent-field sections, rays and midpoints when boundary handles
are points or have linear heads. A linear quotient and region label are
untrusted search data. Replay checks the candidate's full source matrix;
it need not assume the candidate equals that selected root. Nonlinear
selected boundaries need further conversion and are outside this producer.
Original guards are preflighted before root production. `none` means no
supported witness, not a false verdict.

`Quote.finish` shares point and selected-section source transport and requires
the canonical checker's exact arity. `PointQuote.finish` freshly reifies the
original existential target and checks
its exact matrix, coefficient valuation and ordered divisor identities.
The canonical checker, acceptance and final source proof pass ordinary kernel
checking and complete axiom screening. Failure restores the environment and
metavariable state. Ordered divisor identities enforce the input policy;
the source equivalence
is unconditional. Their nonzero interpretation is separately established by
`check_domains`. The generic modules use public module imports and have
no `import all`; concrete fixtures use the pinned non-module import closure.

The [frozen tests](../conformance/HexRCF/PointReplayConformance.lean) use the
actual existing positive √2 predecessor and its supplied checked scalar facts.
They prove acceptance and an ordinary witness, reject an omitted literal,
retain a false point result, and reject a zero guard before malformed data.
An actual `x-α<0` atom at the decoded α gives a checked false sign row and an
API universal counterexample. A separate accepted α guard exercises the
`check_domains` conclusion.
The [source tests](../conformance/HexRCF/PointProduceConformance.lean) produce
new point packets and scalar evidence for freshly reified goals. Seed facts
start from an empty list and pass independent scalar packet replay; newly
reached arithmetic records are checked through the existing collector. No old
row-truth theorem supplies acceptance. Requested reduced keys must equal the
producer's literal key. Shared seed/acceptance declarations prevent repeated
graph interpretation. Both scalar and final acceptance use the kernel guard
that rejects the five listed native producers.

Nine source fixtures cover equality with √2, a point above it, a point between
1 and √2, two ordered divisor identities, a constant after leading-term
cancellation, an actual zero atom, a half-open dyadic domain, a zero-root
section and a left ray. Refusal
controls place each altered call beside its successful checker/valuation call:
a partial canonical checker, false and true universal sentences, a different true existential matrix, √3 substituted for
√2, an omitted divisor identity and changed natural divisor order. Recognition
must retain the coefficient valuation and guards in the matrix/quantifier
controls; the √3 control must retain the exact formula while changing only its
valuation. Each refusal preserves local constant count and metavariable
counters and assignments. The cancellation recognition control retains the
original zero divisor.

A [separate compilation unit](../conformance/HexRCF/PointOrdinaryConformance.lean)
quotes the between-roots source again and audits eight generic API laws plus
the source's complete axiom inventory. Frozen controls, source laws and fresh
proof inventories contain only permitted standard axioms. Local proof-body
scans retain point/scalar replay laws and reject five explicit producer names;
imported declaration bodies are leaves, not rechecked bodies.

This is fixed-parent ordinary-point quotation. It supplies no arbitrary
coefficient discovery, recursive context/provider-history restoration,
nonlinear-boundary conversion, complete frozen root/cell coverage or accepted
algebraic search completeness, and registers no new tactic handler. Existing
rational and real-coefficient `rcf` examples retain their behavior.

The [matched build-only probes](../scripts/bench/rcf_point_selection.py) compare
selected-section and direct parent-point quotation of exactly `∃ x, x=√2`.
Both fresh modules import the same two conformance factories and proof scanner.
This retained run binds the predecessor source `3e84663e72`, before shared
quotation, reused preparation and the additional false-row/branch controls; it is not a timing of
the revised helper.
The existing runner automatically leased CPU 50, used one Lean thread, ran
adjacent arms in AB/BA/AB/BA order and retained all eight completed arms. No
sample was excluded or rerun. Section replay generates four scalar seeds and
three reached records; direct point replay generates one seed and one reached
record. Both emitted proofs have the standard three axioms and local body
checks retain their actual replay law.

| Pair order | Selected section (s) | Parent point (s) |
| --- | ---: | ---: |
| AB | 27.322 | 15.857 |
| BA | 19.536 | 10.721 |
| AB | 21.727 | 12.528 |
| BA | 19.165 | 10.578 |

The medians are 20.631 and 11.625 seconds. The emitted `.olean` sizes are
1,313,120 and 693,912 bytes; median peak RSS is 7,628,360 and 7,554,778 KiB.
These observations include fresh elaboration, ordinary checking, quoted shared
declarations and imported fixture costs; they do not isolate replay alone.
The runner records up to 28 concurrent Lake/Lean processes as context, not a
sample exclusion. Its automatic resolution is `no-comparable-control`; no
null-control resolution bound is supplied. The consistent shorter point-arm
observations and smaller proof artifact answer this single root-selection
question, not general degree/precision/depth scaling or a full tactic speedup.
No separate canonicalization/source discovery costs are measured here.

Operational validation, source hashes and retained failures are recorded in
[the validation manifest](data/hexrcf-point-replay/context.json). The historical failures show exact AST binding (rather than polynomial
semantic equivalence), a proof simplification gap in an external prototype,
a missing namespace, unsupported linear selected handles in the initial
point-only proposer, and a wrong supplied-operation order. Their source
snapshots are not reconstructed, so they support no current correctness claim.
The manifest separates ordinary validation from the matched quotation
comparison; neither establishes general scaling.


[Revised validation](data/hexrcf-point-replay/review-context.json) binds the
shared quotation, exact arity, nine source fixtures, genuine false atom and
accepted-guard conclusions, supporting checker sources and the measurement
report to `960aa5ab935cbd6afff11bc2288d8449d6ef803a`. It retains all seven revised
build outputs, including intermediate harness/import failures. The successful
integration passes 11,683 jobs; shared selected-section/fresh regressions pass
11,089, and revised full render passes 14,166. Earlier logs explicitly precede
later arity/preparation changes. The historical matched samples retain their
own predecessor binding; no current-helper timing is inferred. Manual
proof probes remain build-only manual targets under the repository's existing
policy, not mandatory CI sweeps or executable benchmarks.
