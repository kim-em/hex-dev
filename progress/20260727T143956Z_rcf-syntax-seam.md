# HexRCF Mathlib-free syntax seam

## Accomplished

- Opened #8982 after auditing the concrete import paths blocking a Mathlib-free
  RCF runtime.
- Added `HexRCF.Syntax` with the unchanged reflected syntax declarations and
  pure polynomial traversals formerly split between `Language` and `Carrier`.
- Left real-valued semantics in `HexRCF.Language`, updated the umbrella and
  SPEC file map, and preserved all existing declaration names.
- Verified the `HexRCF.Syntax` transitive import closure contains no
  `Mathlib.*` module.
- Built `HexRCF.Syntax`, `HexRCF.Language`, `HexRCF.Carrier`, and the complete
  `HexRCF` library; the DAG and diff checks pass.

## Current frontier

The reflected input layer now has a genuine Mathlib-free boundary. The rest of
the compiled decision pipeline still imports proof semantics through the
literal Sturm replay, isolation, sign-matrix, and top-level soundness layers.

## Next step

Split the data, Boolean checks, and literal counts in `HexRCF.SturmReplay` from
its Mathlib-facing validity and soundness theorems, preserving public names and
using the new syntax seam as the start of a staged runtime import closure.

## Blockers

None for this slice. Phase 4 itself remains gated on #8972 and the broader
evidence contract in #8973; this refactor makes no phase claim.
