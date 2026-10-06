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

`HexRealClosureMathlib.KernelReplay` supplies a reusable in-process proof assembler for a closed
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
unit query and select the same checked row. The output checks their original
polynomial keys, list order and claimed signs.

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

Each saved theorem binds the normalized polynomial and integer sign to the
original data, together with the scalar-sign equality. One synchronous kernel declaration
check validates that combined statement and its proof.
The fact data remains transparent; its proof field refers to those theorem
constants.
Registration uses the kernel environment API with checking explicitly enabled;
errors leave the declaration set unchanged. Controls inspect the returned
theorem references, require the actual registration call to reject a malformed
proof, and reject an unresolved proof hole. A separate control forces a failure
after the theorem check and verifies that the candidate declaration is not
committed. Kernel exception constructors distinguish those failures from
resource errors. The checks permit only the three standard axioms listed
above.

`Context.readEvidenceWith?` checks a joint packet with equal supplied
predecessor operations and returns its scalar facts in the original context.
Its agreement theorem preserves exact acceptance and rejection for arbitrary
packets and operations satisfying those equalities. The nested control uses
this generic reader on a supplied joint packet and verifies that absent lower
arithmetic evidence prevents a kernel proof. Wrong joint signs, a different key
of the same list length, and a foreign selected-node context reject. Both agreement theorems are audited; the missing
request is checked against the exact predecessor and first retained key.

This control uses an existing validated upper context and a typed upper graph.
Only its lower certificates are freshly produced and retained as in-memory
JSON packets. General context/graph reconstruction from bytes, arbitrary-depth
replay, the public interface and required performance evidence remain
outstanding. `NestedProbe.lean` supplies the private definition bodies needed
for meta-level reduction and runs the same control during `lake build`.

`HexRealClosure.FactOperations` supplies all eight operations with explicit,
proved-equal predecessor operations. Polynomial multiplication receives both
addition and multiplication; inversion receives the one, addition,
subtraction, multiplication, inverse and division operations used by the
existing gcd/Bézout algorithm. The original element carrier and context stay
fixed when predecessor fact lists change. Packing also takes an explicit
reduction function proved equal to the original policy. For ordinary-kernel
replay, reduction must also use supplied predecessor operations: `Context.factReduce` retains the existing policy and monic-division
algorithm with explicit equal predecessor operations. Passing the original
reduction function can start lower sign searches. Compiled evaluation retains
the native fallback.

`FactOperations.lean` exercises these operations on an element in a second
extension whose coefficient retains a noncanonical polynomial in the first.
Addition requests the lower fact for `4X`; without that fact the kernel stops
in the first context. All eight arithmetic checks together request five lower
packets. A separate pass uses only the recorded packets, and removing any one
of the five leaves the check unproved at the exact omitted polynomial key.
A monic defining polynomial exercises the division loop with supplied lower
operations and the three independently specified keys `2X`, `−X` and `X`.
Fresh certificate production and a separate recorded-packet pass succeed;
omitting each packet stops at that exact retained key. Packing also receives
the supplied reduction and its equality proof, and retains the reduced constant
rather than the original linear polynomial.
A nonconstant upper result separately requires its own upper-context fact;
removing that fact stops at the exact upper context and original polynomial.
All nine operation and reduction laws are audited theorem declarations.
Accepted proofs use only the three standard axioms. The controls use fixed typed contexts; they do not establish
context reconstruction from bytes or general replay performance.

```sh
lake build hexsigndet_kernel_replay_probe
lake env .lake/build/bin/hexsigndet_kernel_replay_probe fact-operations
```

`Root.lean` reconstructs a checked root context from two supplied JSON records:
the existing six-field root subject and the existing graph encoding. The
predecessor context stays fixed. Stored algebraic coefficients require exact
sign facts through `Element.signCodec`; missing stored facts reject. The
reconstructed root re-encodes to the exact supplied subject and retains its
nonmonicity; it does not exercise the coefficient cleanliness predicate.
The graph has two entries, including an unused entry, and both are checked.

The control collects two fresh intermediate certificates with independently
specified keys `2X` and `2X − 1`. A separate pass uses only the recorded
packets. Ordinary-kernel checks pin each first-pass request to the original
predecessor context and reject absent stored facts, a parent label mismatch, an uncertified
derivative query and an incorrect unused moment count. The rejection checks
also prove the exact decoder error; the last three use the shared descriptor
rejection message. The derivative control rejects a query
that the root node does not certify; it does not test a wrong derivative sign
with otherwise valid query evidence. A valid graph with a selected count other
than one remains a separate kernel control to add. The parent label is supplied
by the caller; predecessor identity comes from the typed carrier and sign facts.
The native fixture encoder supplies untrusted JSON data, quoted as literal
constructors before checking. Neither fixture initialization nor quotation
establishes acceptance. The predecessor and its stored facts remain typed
fixtures; this is one-level reconstruction, not arbitrary-depth byte replay.
The byte control supplies literal `ByteArray` constructors for both records.
It proves their equality with the existing writer using its exact byte list,
checks the shared lexical limits, and applies the proved parser equation before
context reconstruction. `Codec.decodePair` supplies this byte adapter for the
existing context reader; its generic law preserves the reader's full result or
error. The control requires both parser equations to occur in the
final proof, stops at a missing intermediate sign fact, and rejects absent
stored facts and a prefix of the supplied subject with its final closing
bracket removed. The lexical precheck rejects that prefix. Executable checks
also cover the public descriptor byte adapter and a malformed second record.
Acceptance is checked under the
supplied operations, whose
agreement with the original operations is proved. This control covers the
writer's spelling of the records; it does not cover every whitespace or numeric
spelling accepted by the parser, or independently produced external fixtures.

The canonical prepared cache is constructed and transported by the public
context APIs. Neither the cache nor its root count is evaluated by this
control. Kernel evaluation covers descriptor replay and the monic test;
the two children are the facts demanded during that evaluation. Later queries
can require additional facts for preparation. Supplied Neg, Inv
and Div are covered by the generic equality law, but not evaluated here.

```sh
lake build hexsigndet_kernel_replay_probe
lake env .lake/build/bin/hexsigndet_kernel_replay_probe root
```

`KernelReplay.collectMany` keeps a separate typed finite fact list for each
coefficient context. A demanded missing fact is routed by its actual context,
not a level number or hash. Every returned fact is audited and kernel checked;
its full `SignFact` type must match that inventory before insertion. Unknown
contexts, missing packets and exhausted fuel leave the result unproved.
The final Boolean equation is checked with all inventories actually used.

The fact-operation control checks a lower joint graph and a nonconstant scalar
in the next extension. It collects the two lower facts and one upper fact,
then replays from empty inventories using only the recorded lower packets and
the supplied upper graph. Repeating the upper scalar reuses the same inventory.
Omitting the upper packet stops at its exact context and polynomial. Contexts
and the upper graph remain typed fixtures; this control does not reconstruct an
arbitrary-depth catalog or complete the required performance evaluation.

A second control uses two contexts over `Rat`, both labelled 7 and using the same reduction policy, selecting the
opposite roots of `X² - 1`. Their facts concern the same polynomial `2X` but
have opposite signs. The collector adds the negative-root fact only to the
second inventory, preserves the positive-root inventory, and rejects that
positive-root fact when requested for the negative root. The negative root
and its sign are validated by supplied Tarski/BKR certificates in the ordinary
kernel. A non-Boolean collection program rejects before invoking the supplier.

`FiniteTowerThom.lean` reconstructs the positive root of `x² − α` over
`α = √2` using its first derivative sign on the whole real line. Its literal
subject has a nonempty Thom word. Ordinary-kernel acceptance consumes the
collected lower packing and stored-value sign records. Removing the constant
`2` packing record stops replay at that exact missing coefficient without
invoking a producer. The descriptor reader reuses the tree already checked by
`Dag.replay?`; it checks subject shape, context and the selected sign count
without traversing the tree a second time. `Replay.readDescriptor_eq` proves
that this returns the same full descriptor or rejection as the original reader.

```sh
lake build KernelReplay.FiniteTowerProbe KernelReplay.FiniteTowerThom
```
