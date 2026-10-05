# Kernel replay experiment

This experiment assembles proofs about the existing supplied-fact coefficient
arithmetic and `Dag.validateCached?` checker. Each accepted result is an equality
between the caller's actual Boolean expression and `true` or `false`, checked by
Lean's ordinary kernel. It simplifies structural checker equations, then asks
the kernel to reduce the resulting Boolean comparison. Replay does not evaluate
coefficient arithmetic natively or rewrite it to the ordinary implementation
that searches for signs.

The proof assembler disables error-to-`sorry` recovery, requires closed inputs
and proofs, and audits their transitive axioms. Only `propext`, `Classical.choice`
and `Quot.sound` are allowed. Unexpected kernel errors, resource exhaustion
and unrelated elaboration errors fail the command. Only a declaration type
mismatch permits trying the other Boolean result. `unproved` means neither
equality was assembled; it is not a proof that the checker returns `false`.
The probe also requires a missing-fact application on the demanded projection or pattern-match path, without searching
unapplied lambda bodies. An unrelated blocking definition fails the control.
Blocked definitions are unfolded to their actual recursors, which select the demanded operand. Committed controls cover two
blocked arithmetic operands, a blocked constructor field in a matcher,
an unrelated opaque Boolean, an incomplete proof, a real kernel timeout and
the shared exception classifier used by both binding and result decisions.
The arithmetic and matcher controls use closed terms and positive counterparts
that must reach missing evidence. The probe follows projections and recursor
arguments after unfolding definitions; unsupported shapes fail the control.
Axiom output for the missing-fact lemmas is checked against the three permitted axioms.

The controls include complete and missing scalar evidence, a false scalar claim,
the actual two-entry graph, a false unused entry, and a false endpoint sign.
A separate control checks the exact returned nodes and their order. The scalar
and endpoint computations have separate kernel-proved missing-fact equations.
The elaborator computes the diagnostic expression; its polynomial is not
checked against those equations.

`ProofProbe.lean` also proves that the actual finite coefficient decoder reads
one encoded graph with both fact lists. Both lists cover every stored
coefficient; only the complete list covers the nonconstant intermediate endpoint
calculation. The existing checker accepts the complete case; the proof assembler
cannot prove a Boolean result for the incomplete case.

Build and run the compiled proof wrapper:

```sh
lake build hexsigndet_kernel_replay_probe
lake env .lake/build/bin/hexsigndet_kernel_replay_probe
lake env .lake/build/bin/hexsigndet_kernel_replay_probe emit /tmp/graph.json
lake env .lake/build/bin/hexsigndet_kernel_replay_probe bytes-equal /tmp/graph.json
lake env .lake/build/bin/hexsigndet_kernel_replay_probe bytes /tmp/graph.json full true
lake env .lake/build/bin/hexsigndet_kernel_replay_probe bytes-bound /tmp/graph.json missing unproved
python3 experiments/KernelReplay/run.py /tmp/kernel-replay-results
```

The wrapper parses supplied bytes with the existing integer-only JSON parser and
quotes the parsed record as a constructor expression. The kernel checks proofs
about that exact expression. `bytes-equal` additionally proves equality with the
encoded fixture. `bytes-bound` proves that equality and requires the simplifier
to use both the binding and the fixture's proved decoder equation. Complete and
incomplete records exercise this requirement; it is deliberately restricted to
this test record.
These checks do not prove the native parser implementation correct. Altered
count and context fields can be tested with `bytes PATH full false`. The harness
also proves that the altered count passes decoding before replay rejects it.
An altered record supplied to `bytes-bound` fails the equality requirement
outright, even when the expected replay outcome is `unproved`. The harness
requires the binding-failure diagnostic and forbids a proved-binding or
`unproved` result in that control. It pins the fixture's byte size and digest,
retains every control's output, and imposes a 180-second operational timeout
per process.

The executable uses Lean's unsafe initializer-enabling API to load elaborator
extensions. This is not part of the arithmetic or proof acceptance boundary.
Imported fixture modules can construct their native test data during
initialization. The experiment establishes what proof assembly checks; it does
not establish that the whole process, including fixture setup, avoids searches.

This is a prototype, not the final public certificate interface. It reuses a
validated context and certified facts, does not reconstruct contexts from bytes,
does not reconstruct general nested coefficient contexts, and does not return
a native checked memo. The rational-predecessor producer below generates
intermediate certificates for one fixed context. The experiment leaves the
native fallback in `Element.missing` unchanged.
Consequently it does not establish strict native replay or Phase-4 completion.
Single-run proof assembly timings are diagnostic observations, not performance
evidence.

`Assemble.lean` supplies a reusable in-process proof assembler for a closed
Boolean expression. It returns either a checked equation for the actual
expression or the demanded missing-fact application, retaining the exact
context and original polynomial. Unrelated opaque expressions and kernel
errors remain errors. It uses no native coefficient evaluation.
The generic assembler does not certify that an arbitrary caller's expression
avoids sign production. The actual replay program and simplification rules
retain the supplied-fact packing boundary; a final interface must fix those
choices rather than permit arbitrary expressions or rewrites.

Its producer-side collector retries the actual checker after obtaining each
required fact from a supplier. It audits and kernel checks supplied facts and
returns the finite list used in the final checked equation. A missing supplier
result or exhausted fuel returns the unresolved request; neither establishes
a Boolean result. The collector calls its supplier when a fact is missing;
that supplied function may produce new certificates or read recorded packets.
The proof assembler itself never calls the supplier.

```sh
lake env .lake/build/bin/hexsigndet_kernel_replay_probe collect
```

The collection control starts with no intermediate facts for the actual
two-entry graph. It discovers the retained keys `2X` and `2X - 1` in the exact
coefficient context, selects their already proved facts from an inventory, and
checks the resulting complete calculation. Kernel equations check the keys
and contexts. An incomplete inventory stops at `2X - 1`; zero fuel never calls
the supplier; repeatedly supplied irrelevant facts stop at the fuel bound.
The controls also pin one-fact fuel exhaustion, count supplier calls, check a
false graph as false, select only two facts from a reordered larger inventory,
and reject a malformed fact proof and an unresolved proof hole. Kernel timeouts
cannot satisfy the malformed-proof rejection control.
This control collects facts automatically but does not produce new sign
certificates. General certificate production, context reconstruction and
deeper replay remain outstanding. The collector makes one proof-assembly
attempt per supplied fact plus a final attempt; these controls establish no
scaling or Phase-4 result.

`Generated.lean` supplies fresh certificates instead of selecting an inventory
of already proved facts. It starts the actual two-entry checker with an empty
fact list, obtains the demanded keys `2X` and `2X - 1`, and invokes the existing
prepared BKR producer at the coefficient context's selected root. It quotes
the resulting polynomial, integer sign and graph as literal integer-only JSON
data. The existing decoder, graph checker and `Context.readSignFact?` then
assemble the facts. Kernel-checked equations bind each packet to that reader's
actual acceptance or rejection; successful facts are audited and kernel checked
before collection uses them. The final graph equation also goes through the
ordinary kernel. The prototype fixes the rational interpretation in proof
assembly; it introduces no runtime law package or second query implementation.
The controls check the requested keys and contexts with kernel equations, and
require kernel-checked rejection of wrong signs, a different query, a stale
context identifier and forged counts.
The different query is `X` in place of `2X - 1`; both have value `1` at the
selected root `1`, but their literal polynomial bindings differ.

```sh
lake env .lake/build/bin/hexsigndet_kernel_replay_probe generated
```

The producer uses unsafe native evaluation to obtain a requested rational
polynomial and run existing production. Those results remain untrusted data:
quotation and native computation cannot establish acceptance. After generation,
a second collection reads only the recorded packets and checks the actual graph
again. Its supplier matches literal polynomial keys and calls the packet reader;
it never calls the producer. A forged packet leaves an unresolved request and
establishes no Boolean result. These packets are in-memory JSON values from the
same run; they are not written as bytes and parsed again. Generation, collection and
checking run within the same process. This fixture still starts from an already
validated coefficient context and a fixed upper-level graph; it does not produce
that graph or reconstruct its context from bytes. It demonstrates fresh
intermediate evidence at a rational predecessor, not general replay through
arbitrarily many coefficient fields. Its timing includes repeated collection
attempts and coefficient certificate checks, excludes process startup, and is a
diagnostic observation rather than Phase-4 evidence.

Acceptance always requires a kernel-checked equality for the supplied
expression. Looking for an opaque missing-fact expression inside unapplied
operation bodies would not establish that replay needs that fact.

## In-process readers

```sh
lake build hexsigndet_inprocess_replay_probe KernelReplay.LowerProof
.lake/build/bin/hexsigndet_inprocess_replay_probe
```

`InProcessProbe.lean` looks up proof-carrying facts established in the kernel
before execution, to pack intermediate Horner values and check endpoint
conditions. A missing nonconstant fact returns `none`. Each successful result
has a proof of literal equality with the existing ordinary operation or endpoint
predicate. The constant path retains ordinary predecessor sign evaluation.
Its compiled controls test lookup and rejection of these pre-proved facts;
they do not validate certificates at runtime. Establishing such facts from
checked certificates uses the companion's interpretation assumptions in proof
assembly, separately from the executable memo reader.

`LowerProbe.lean` instead uses the shared Horner order and ordinary polynomial
operations on the stored representatives. It applies the existing context
reduction after each partial sum, bounding intermediate degree when the clean
monic reduction policy applies. It reads the final expression's sign from an
already checked lower-level graph, without constructing intermediate algebraic
elements. A scalar difference is checked the same way. `LowerProof.lean` proves
that accepted signs equal the signs of ordinary evaluation and subtraction.
The interpretation assumptions occur in correspondence theorems; the executable
readers take no law arguments. These are mathematical value comparisons, and
do not replace literal certificate bindings with semantic equality. The lower
readers require supplied certificates even for constant queries, rather than
falling back to the predecessor's sign operation.

`InProcessMain.lean` exercises both readers in one process. Its 25 controls
cover missing evidence followed by successful replay, incorrect sign claims,
absent indices, different queries, stale context keys, finite and infinite
endpoints, constants and canonical zero, plus well-bound graphs with forged
counts or moment variations. The compiled lower-level evaluation
and difference controls validate the supplied graph at runtime. A zero-sign
certificate for the nonzero query `2X - 2` establishes `literal = 2` in the
extension: both denote `2` at the selected root `1`. A sign-equivalent
certificate for the wrong query rejects.
A separate example checks a difference that reduces to the zero polynomial.
Ordinary-kernel
examples check supplied-fact endpoint replay, lower-level sign selection and
the zero differences; axiom guards check the general correspondence proofs,
and fixtures instantiate both the evaluation and subtraction correspondences.
The lower-level Horner example needs its final endpoint certificate, without
the separate sign fact for the intermediate product required by the first
reader.

These readers return normal rejection without stopping the process. They are
component experiments, not a complete nested replay checker. Their coefficient
type remains generic: ordinary arithmetic over an algebraic predecessor can
still invoke that predecessor's sign search. The controls use rational
predecessor arithmetic. They also reuse certified contexts and literal graph
fixtures; fixture initialization may run production. They do not reconstruct
contexts from untrusted bytes or prove that an entire nested replay execution
avoids production. General polynomial-identity integration, evidence production,
deeper-level replay, independent final-interface conformance and Phase-4
performance evidence remain separate obligations.

`Nested.lean` checks two upper scalar-sign facts using one shared graph memo
and one lower fact list. All eight coefficient operations use supplied-fact
packing; `Context.changeOps` retains the original checked root and prepared
cache. Interpretation laws and `changeOps_signPoly` return facts in the
original context. The two input polynomials, `X` and `1`, both reduce to the
unit query and
select the same checked row. The output checks distinguish their original
polynomial keys and list order, as well as their claimed signs.

```sh
lake build hexsigndet_kernel_replay_probe
lake env .lake/build/bin/hexsigndet_kernel_replay_probe nested
```

The control starts with no intermediate lower facts, produces the two demanded
rational-predecessor certificates, and checks their literal packets. A separate
pass starts from the same empty list and reads only those recorded packets.
The kernel-checked result includes the two distinct input polynomial keys
and their signs. Missing or incomplete
child evidence leaves the calculation unproved. False signs, a different query
with the same sign, stale context IDs and corrupted moments in both the
selected and unused graph entries are rejected by the existing checker.

Each saved theorem proves the exact copied polynomial and integer sign,
together with the scalar-sign equality. One synchronous kernel declaration
check validates that combined statement and its proof.
The fact data remains transparent and refers to those theorem constants.
Registration uses the kernel environment API with checking explicitly enabled;
errors leave the declaration set unchanged. Controls inspect the returned
theorem references, require the actual registration call to reject a malformed
proof, and reject an unresolved proof hole. A separate control forces a failure
after the theorem check and verifies that the candidate declaration is not
committed. Kernel exception constructors distinguish those failures from
resource errors. The checks permit only the three standard axioms listed
above.

This control uses an existing validated upper context and a typed upper graph.
Only its lower certificates are freshly produced and retained as in-memory
JSON packets. General context/graph reconstruction from bytes, arbitrary-depth
replay, the public interface and required performance evidence remain
outstanding. `NestedProbe.lean` supplies the private definition bodies needed
for meta-level reduction and runs the same control during `lake build`.
