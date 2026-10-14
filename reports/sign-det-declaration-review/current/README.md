# Current SignDet companion reference evidence

The capture resolves all 226 individually assessed declarations in 451 compiled
constants attributed to the 37 companion production modules. Its axiom union is
`propext`, `Classical.choice`, `Quot.sound`. All seventeen private helpers have
paths to handwritten public interfaces. Five structure fields are recorded from
Lean metadata. The existing declaration assessment covers their mathematical
meaning separately.

The import scan covers all 364 tracked production modules that transitively
reach a SignDet module root; no required module is absent from the capture.
Source roles distinguish production from tests, diagnostics, manual examples
and external dependencies. The imported environment contains 14,867 modules.
This checks import coverage, not runtime use or computational performance.

The graph merges known compiler aliases within the selected constants and
identifies 64 public declarations without a path to a production user outside
the companion. Their individual purposes are recorded in
[the disposition table](public-dispositions.md), using the existing assessment.
Twenty-eight have no direct compiled references at all. Every private helper
has a direct compiled reference. Anonymous examples, automation registrations,
external projects and aliases targeting unaudited modules remain outside the
reference model.

The earlier inventory at the parent report remains a retained snapshot. This
capture does not advance phase counters or establish complete core review.
Source bindings, reproduction and final API/manual acceptance remain necessary
before using it as a completed phase attestation.
