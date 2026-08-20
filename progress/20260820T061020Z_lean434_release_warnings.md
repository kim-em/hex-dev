# Lean 4.34 release-warning cleanup

## Accomplished

- Reproduced Mathlib PR #42336's full-CI failure as warning-as-error output from the released HexBasic, HexPoly, and HexMvPoly packages.
- Replaced the six deprecated conditional rewrite lemmas with their Lean 4.34 names throughout the three source-of-truth libraries.
- Built `HexBasic`, `HexPoly`, and `HexMvPoly` under Lean 4.34.0-rc1 with Mathlib's exact `--wfail -KCI` policy; all 32 targets passed without warnings.
- Fixed the corresponding two deprecated rewrites in the Mathlib SOS bridge and confirmed its polynomial module builds.

## Current frontier

- The warning-clean Hex changes are ready to commit and send through hex-dev CI.
- The Mathlib bridge edit remains local until the coordinated release pins are available.

## Next step

- Merge the hex-dev cleanup, publish the three split repositories in dependency order, tag patch releases, publish an SOS patch release using those tags, then update and validate the Mathlib draft PR.

## Blockers

- None.
