# HexMvPoly Phase-6 polish

## Accomplished

- Confirmed both libraries are sorry-, axiom-, and `native_decide`-free and
  rebuilt the computational, Mathlib, conformance, and proof-probe targets.
- Documented every public declaration and every non-obvious private helper in
  the HexMvPoly and HexMvPolyMathlib implementation modules.
- Audited private declarations for reachability and found no dead helpers.
- Reorganized the correspondence bridge's equality-instance sections so its
  transported structures remain coherent without `omit` workarounds.
- Named transported instances, removed redundant simp registrations, and made
  the intentional ambient equality parameters explicit to the Mathlib linter.
- Passed the focused built-in lint suite and Mathlib's namespace lint suite
  with no diagnostics.
- Recorded Phase 5 and Phase 6 completion for both libraries.

## Current frontier

The executable and bridge APIs are fully proven, documented, linter-clean, and
covered by the current committed native performance baseline.

## Next step

Write and build the HexManual chapter and the two released-repo READMEs, verify
their quickstarts, and then record Phase 7 completion.

## Blockers

None.
