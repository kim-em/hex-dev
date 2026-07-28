# Number-field Mathlib companion scaffold

## Accomplished

- Added the complete seven-module `HexNumberFieldMathlib` source layout:
  fixed-presentation laws, approximation semantics, exactification, lazy
  arithmetic, algebraic-coefficient polynomials, and root-set correctness.
- Defined actual semantic interpretations for dyadic complex balls,
  algebraic-coefficient polynomials, fixed-field polynomials, and root-set
  membership and multiplicity. All unfinished work is confined to explicit
  proof-level `sorry`s.
- Corrected the companion SPEC so its initial `QAdjoin.toComplex` boundary
  does not presuppose the field structure it is meant to justify, and replaced
  structural lazy-root membership with semantic complex-value membership.
- Exported the complete module chain from `HexNumberFieldMathlib.lean`.
- Built `HexNumberFieldMathlib`, ran `scripts/check_dag.py`, checked library
  status, scanned for banned axioms and `native_decide`, and passed
  `git diff --check`.

## Current frontier

The Phase-1 NumberField Mathlib companion surface is compile-valid and ready
for its checkpoint PR. Its proof obligations remain intentionally visible;
there are no data-level placeholders.

## Next step

Open the NumberField Mathlib scaffold PR, launch its independent review in the
background, and begin the `HexNumberFieldTowerMathlib` companion scaffold
without waiting for that review to finish.

## Blockers

Advancing `HexNumberFieldMathlib.done_through` remains gated on the recorded
Phase-1 dependency milestones. This does not block publishing the scaffold
checkpoint.
