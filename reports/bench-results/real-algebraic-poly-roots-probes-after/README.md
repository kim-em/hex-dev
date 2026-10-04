# Larger post-change polynomial-root probes

Both larger fixtures pass after the proved early rejection of nonreal roots:
`X^16−2` and `X^8−√2` return the complete expected ordered polynomial/sign/
multiplicity array. The manual compiled commands are `probe-rational16` and
`probe-quadratic8`; they call the same input constructor and root API as the
fixed registrations, and compare complete arrays before emitting a result.

The observed whole-child durations are 9.334 and 9.409 seconds respectively,
under the same 60-second operational cap. They include input preparation,
result checks, process startup and output. These are unpinned correctness/cap
probes, not operation-only scientific samples or a controlled speedup against
the historical capped runs. Their changed source makes them new probes, not
unchanged reruns. Their success does not extend the smaller scientific timing
ladder or advance the phase counter.

[record.json](record.json) preserves commands, outcomes, exact executable hash,
dirty-source parent and all changed computational source fingerprints.
Source snapshots and stdout/stderr are retained alongside it. The exact
executable and duplicate records remain persistently at the recorded paths.
The earlier failed probes remain in
[the original evidence](../real-algebraic-poly-roots-probes/README.md), rather
than being erased by these passing results.
