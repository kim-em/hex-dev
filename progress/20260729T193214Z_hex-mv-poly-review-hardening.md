# HexMvPoly review hardening

## Accomplished

- Kept generic `ExtTreeMap` traversal and deletion-capable merge machinery in
  the Std-only `HexBasic/ExtTreeMap.lean` upstream-candidate layer; coefficient
  arithmetic and zero elision remain `HexMvPoly` policy.
- Removed a dead coefficient-map helper and limited exposure of reporting
  queries, adding characterization lemmas for the Mathlib correspondence.
- Replaced the apparent randomized Mathlib oracle with honest bridge-import
  executable guards and theorem-transport checks. The independent randomized
  coverage remains the core fixture stream checked by SymPy.
- Hardened the sorted proof-probe proxy with checked canonical construction and
  explicit monomial-order requirements.
- Added a matched construction-only control for the kernel addition probe and
  round-wise construction subtraction to the sweep harness, with unit tests.
- Reworked the transported Mathlib semiring and ring instances so their
  operations remain executable after import.
- Expanded consumer acceptance to the full SOS tactic and example suite.
  Fresh pinned clones passed all 1,545 SOS jobs and all 1,902 CompPoly jobs;
  the setup script's automatic Nix native-library configuration was exercised.
- Passed the full 9,650-job repository build, focused conformance/proof-probe
  and manual build, exact fixture comparison, all 62 sweep-harness tests, all
  11 native benchmark smoke checks, DAG/registry/manifest/Mathlib-free policy
  checks, and the local SymPy-aware oracle path (cleanly skipped because SymPy
  is not installed; release CI requires it).

## Current frontier

The review fixes are ready for a clean commit. The benchmark report and
representation decision still cite the superseded import-only kernel
measurement.

## Next step

Commit this checkpoint, capture a release-quality kernel sweep on the clean
commit with construction subtraction, update the report and representation
decision from that artifact, then run the final independent review and open
the completion PR.

## Blockers

None.
