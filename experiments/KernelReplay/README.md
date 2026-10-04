# Kernel replay experiment

This experiment assembles proofs about the existing supplied-fact coefficient
arithmetic and `Dag.validateCached?` checker. Each accepted result is an equality
between the caller's actual Boolean expression and `true` or `false`, checked by
Lean's ordinary kernel. It simplifies structural checker equations, then asks
the kernel to reduce the resulting Boolean comparison. It does not evaluate
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
does not collect intermediate facts automatically, and does not return a native
checked memo. It leaves the native fallback in `Element.missing` unchanged.
Consequently it does not establish strict native replay or Phase-4 completion.
Single-run proof assembly timings are diagnostic observations, not performance
evidence.

Acceptance always requires a kernel-checked equality for the supplied
expression. Looking for an opaque missing-fact expression inside unapplied
operation bodies would not establish that replay needs that fact.
