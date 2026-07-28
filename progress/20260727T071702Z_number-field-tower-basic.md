# HexNumberFieldTower representation scaffold

## Accomplished

- Activated `HexNumberFieldTower` in the library graph, Lake configuration,
  and the existing single-job CI target list; kept its Mathlib companion
  planned until its source exists.
- Moved the immutable tower SPEC into the standard per-library source layout
  and updated the SPEC index link.
- Added the sealed `NumberTower`, top-first level metadata, structural
  mixed-radix dimension invariants, the rational tower, and fixed-width
  `NumberTower.Elem` coordinates.
- Added exact coordinate equality, normalization, rational embedding, and
  compiled rational-carrier checks.
- Built `HexNumberFieldTower` and passed `scripts/check_dag.py`.

## Current frontier

The rational carrier and representation invariants are executable. Tower
arithmetic and the checked level-construction boundary are the next layer.
The completed roots/bounds reviews also require one further conservative
Horner-majorant strengthening before their companion completeness theorem.

## Next step

Publish this scaffold, repair the reviewed disambiguation recurrence on its
originating branch and rebase descendants, then implement recursive
mixed-radix arithmetic.

## Blockers

None.
