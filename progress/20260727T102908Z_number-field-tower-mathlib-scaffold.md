# Number-field tower Mathlib companion scaffold

## Accomplished

- Activated `HexNumberFieldTowerMathlib` in Lake, the library graph, and the
  existing single-job CI target list, and moved its SPEC beside the source.
- Added the full seven-module companion layout covering fixed complex tower
  semantics, arithmetic, relative norms, recursive Trager factorization,
  adjoining, splitting, and primitive-element flattening.
- Defined actual semantic interpretations for tower elements, tower
  polynomials, raw relative polynomials, and relative outer polynomials.
- Added explicit semantic validity predicates for public factorization,
  extension, splitting, and flattening payloads. Arbitrary public records are
  not assumed sound; the contracts apply to checked constructor results.
- Corrected the SPEC's bootstrap order for field packaging and its stale claim
  that both flattening round trips are checked directly.
- Built `HexNumberFieldTowerMathlib`, ran `scripts/check_dag.py`, checked
  library status, scanned for banned axioms and `native_decide`, and passed
  `git diff --check`.

## Current frontier

The tower companion Phase-1 surface is compile-valid with all unfinished work
confined to proof-level `sorry`s. The independent review of its NumberField
Mathlib base completed during this work and identified actionable API and
refinement-contract gaps.

## Next step

Commit the tower scaffold checkpoint, repair the reviewed NumberFieldMathlib
base, update PR #8938, rebase this branch on the corrected base, then launch
the tower scaffold's independent review without waiting before the next stage.

## Blockers

Phase advancement remains gated on the recorded NumberField and Tower Phase-1
dependency milestones. The scaffold itself has no build blocker.
