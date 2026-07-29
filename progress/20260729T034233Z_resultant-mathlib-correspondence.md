# Resultant–Mathlib correspondence

## Accomplished

- Proved that the terminal value of the ordered Brown–Traub recurrence is the generalized Sylvester coefficient minor.
- Proved the full executable/Mathlib resultant correspondence, including zero, constant, degree-order, and swap cases.
- Derived common-root, root-product, and discriminant correspondence theorems.
- Proved bivariate specialization, including formal-degree drops after evaluation and the default-degree corollary.
- Updated the Resultant and Resultant–Mathlib specifications to describe the completed public API and proof architecture.
- Verified the complete repository with `lake build` (9,573 jobs) and confirmed the Resultant libraries contain no `sorry` or `axiom` declarations.

## Current frontier

The Resultant–Mathlib correspondence milestone is complete and ready to land as one cohesive pull request. There were no open Resultant or NumberField pull requests before this milestone.

## Next step

Open the single Resultant–Mathlib correspondence pull request, monitor its individual GitHub Actions jobs, and merge it before resuming NumberField or tower work.

## Blockers

None.
