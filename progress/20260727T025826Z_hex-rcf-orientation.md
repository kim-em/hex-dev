# HexRCF orientation

## Accomplished

- Read `SPEC/Libraries/hex-rcf.md` in full and mapped its reflected language,
  cell-decomposition algorithm, certificate replay boundary, tactic surface,
  conformance requirements, and performance contract.
- Confirmed that `HexRCF` is still planned at `done_through: 0`: there is no
  `HexRCF/` source tree, umbrella, Lake target, or conformance target yet.
- Traced the required downstream APIs in `HexRealRoots`,
  `HexRealRootsMathlib`, `HexPolyZ`, and `HexPolyZMathlib`, including
  `isolate?_isSome`, `aevalIff_squareFreeCore`,
  `RealRootIsolations.isolates`, `SturmChainCert`, and `refineTo`.
- Read the current phase conventions and verified that the tracker lists
  `HexRCF` as deliberately deferred rather than ready for dispatch.

## Current frontier

The dependency foundations are present, including compiled isolation with
kernel-replayable Sturm-chain certificates. All RCF-specific implementation
layers remain: reflected syntax and semantics, cells and bounded endpoint
classification, sign-matrix certificates and checker, soundness assembly,
goal reification, tactic frontend, and conformance fixtures.

## Next step

When `HexRCF` is activated, sanity-check the SPEC's certificate data against
the exact current polynomial gcd/divisibility APIs, then open a narrow Phase 1
scaffolding issue beginning with the reflected language and final-form data
structures.

## Blockers

- `HexRCF` is intentionally marked `status: planned`, so the normal status
  planner skips it.
- The pod `coordination` command was not available on `PATH` in this worktree;
  no claim or dispatch action was needed for this orientation session.
