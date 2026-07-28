# Tower conformance review repairs

## Accomplished

- Expanded the core profile to cover every advertised tower arithmetic
  operation over genuine one- and two-level fields, including recursive
  inversion, non-rational division, zero totalization, both selected
  conjugates, non-unit defining coefficients, non-unit factor content, and a
  bad first Trager shift.
- Replaced the external oracle's degree-only factor buckets with exact monic
  factor comparison. Lean now emits rational mixed-radix coordinates, scalar,
  multiplicities, relative level degrees, and tower dimension; PARI interprets
  those coordinates through exact compositum generator maps, checks
  reconstruction, and compares the actual irreducible factors.
- Made compositum construction select the declared relative-degree component
  instead of an embedding-blind maximum-degree component.
- Removed the zero- and one-generator flattening bypasses from the external
  profile. Both remaining cases perform a genuine bounded resultant search;
  the dependent-generator case distinguishes absolute degree four from
  relative degree two.
- Made the PARI flattening oracle use the combined collision budget, require a
  linear recovery gcd, and use emitted fixed-embedding boxes to select among
  recoverable conjugate factors.
- Made the split oracle call `nfsplitting` only on irreducible inputs, compose
  their splitting fields explicitly, strip constant content factors, construct
  PARI polynomials through the typed API, and report `PariError` per case.
- Documented that relative-coefficient inputs remain core-only rather than
  silently interpreting them over the rationals.
- Added the tower emitter to the existing single CI build job and regenerated
  the committed fixture.
- Built the complete `HexConformance` target, reproduced the fixture byte for
  byte, passed all nine PARI cases, compiled the Python driver, checked shell
  syntax and the library DAG, and passed `git diff --check`.

## Current frontier

All five blocking findings and the substantive oracle correctness findings
from the conformance review are addressed. End-to-end assertions are still
duplicated in some implementation modules; consolidating every pre-existing
low-level guard is a separate source-layout cleanup, not an oracle soundness
gap.

## Next step

Publish the repaired conformance commit, then apply the focused flattening
re-review's documentation and non-vacuous multiplicativity refinements before
rebasing this branch once more.

## Blockers

None.
