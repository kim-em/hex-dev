# Accomplished

- Generalized Mahler separation to arbitrary nonzero integral polynomials via
  the integral radical, and propagated the nonzero/local-simplicity interfaces
  through root identity, NK depth, and the root-free converse.
- Proved local completeness of one-atom refinement under `.nkThenPellet`, even
  when unrelated roots of the ambient polynomial are repeated.
- Made the complete refinement fallback globally reglue survivor lineages and
  require exactly one target-ready atom before emission.
- Added a proved-sound bounded speculative fast pass so successful Newton
  refinement retains logarithmic precision growth before the global fallback.
- Proved the requested-radius contract for fixed-field approximation, including
  dyadic-ball arithmetic, Horner error propagation, coefficient bounds, and
  guard-bit sufficiency; removed the approximation totality `sorry`.
- Updated the roots, polynomial, and number-field SPECs; added a permanent
  repeated-ambient-root conformance case and refreshed affected benchmark
  hashes.
- Incorporated the independent review's findings about survivor-lineage
  splitting and mixed-only completeness.
- Verified the full 9,630-job repository build, `HexConformance`,
  `HexReleaseTests`, and the roots/number-field benchmark smoke gate (43s under
  the 360s cap). Changed files contain no `sorry`, `axiom`, or `native_decide`.

# Current frontier

The approximation-radius and local-refinement-completeness milestone is ready
to publish as one consolidated PR. No PR is currently open for this branch.

# Next step

Publish this milestone, monitor its individual CI jobs, address any review or
CI findings, and merge it before beginning the next implementation stage. Then
resume the remaining obligations in the number-field and tower SPECs.

# Blockers

None.
