# Fresh-module proof-probe protocol correction

## Accomplished

- Corrected the Phase-4 proof-probe protocol to require exact invalidation and
  rebuilding of each measured module while imported dependency artefacts stay
  warm.
- Required adjacent reference/candidate builds, rotated pair order, and
  alternating pair orientation, matching the reusable runner implemented for
  #8972 and avoiding measurement of the entire local import closure.

## Current frontier

- The Phase-4 contract now states the executable protocol that the shared
  harness can enforce and that the original #8972 directive requires.

## Next step

- Restack the compiled HexRCF benchmark branch on this correction and use the
  shared pair runner for the HexRCF proof-probe matrix.

## Blockers

- None.
