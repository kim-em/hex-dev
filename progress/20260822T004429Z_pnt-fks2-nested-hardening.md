# FKS2 theorem-6.2 nested-log hardening

## Accomplished

- Renamed the runtime predicate to `checkShape` and documented its exact
  structural-only contract, keeping semantic logarithm evidence in the
  package-owned proof companion.
- Added discriminating shift and atanh-numerator failures, plus a structurally
  valid non-source payload demonstrating that shape checking does not imply a
  logarithm window.
- Removed the unused natural-log dependency from the Mathlib-free runtime,
  pinned `sourceRows` and `checkShape` in inventory evidence, and corrected the
  residual PNT classification text.
- Revalidated the focused target, full 9,598-job `HexConformance` target,
  pinned-source inventory, unit tests, static checks, trust surface, and factor
  freshness.

## Current frontier

The one-site nested-log rewrite retains its exact source theorem adapter and
now separates structural source authentication explicitly from the ordinary
semantic proof.

## Next step

Update the existing upstream PR and let its automatic exact-head CI run.

## Blockers

None.
