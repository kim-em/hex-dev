# HexResultant reviewed value repair

## Accomplished

- Implemented the reviewed derivative formal-degree correction by multiplying
  the default resultant by the leading-coefficient gap power before the exact
  discriminant quotient.
- Simplified `disc` to one executable definition; the existing derivative
  `@[csimp]` implementation handles compilation directly.
- Added a characteristic-five regression reproducing the review
  counterexample `2X¹⁰ + 3X`, plus cubic and nonmonic discriminants.
- Added a strict reversed odd-degree resultant whose sign factor is `-1`, and
  covered self-resultants and resultant against one.
- Moved inline resultant checks to the resultant definition module and kept
  discriminant checks at their own definition site.
- Rebuilt HexResultant and reran status, DAG, copyright, line-count,
  forbidden-form, and whitespace checks successfully.

## Current frontier

The high-severity review finding is fixed in both contract and implementation.
The Brown recurrence itself was independently confirmed, including signs,
defective drops, final scale, exact divisors, and tight bounds.

## Next step

Force-update the reviewed stacked PR, propagate the repaired base into the
Mathlib and number-field branches, and incorporate the Mathlib scaffold's
direct-specialization proof route.

## Blockers

None.
