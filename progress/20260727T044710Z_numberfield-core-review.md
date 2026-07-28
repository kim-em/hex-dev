# HexNumberField core review repair

## Accomplished

- Added positive-degree invariants to checked irreducibility, lazy roots, and
  canonical algebraic numbers, ruling out prime-constant quotient presentations.
- Added the canonical algebraic zero through the fixed isolator, together with
  `Zero`, `Inhabited`, and the diagnostic `panicWith` totalization primitive.
- Added exact generic `DyadicSquare.discContains` geometry to HexRoots and made
  the number-field zero test delegate to it.
- Simplified canonical equality to compare polynomial data and stored squares
  without dependent casts, and corrected the zero-test separation rationale.
- Removed unused core imports, repaired the source-local SPEC index link, and
  added `HexNumberField` to the existing single-job CI library targets.
- Rebuilt `HexNumberField`; compiled guards confirm the `X` certificates,
  canonical isolator path, and semantic zero check. All repository structural
  and source checks passed.

## Current frontier

The core representation now carries the invariants needed for genuine number
fields and has a real canonical fallback value. Three propositional scaffold
obligations certify the executable `X` checks and canonical-isolation branch;
their corresponding compiled guards pass.

## Next step

Update PR #8889, rebase its QAdjoin and approximation descendants onto these
invariant changes, and repair any constructor or instance call sites exposed by
the rebase.

## Blockers

The phase scheduler still waits for HexBerlekampZassenhaus Phase 1 status even
though the dependency APIs exercised by this branch compile successfully.
