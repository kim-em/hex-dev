# Accomplished

- Added iterated unshifted norms for absolute root-candidate eliminants while retaining one-level norms for recursive Trager factorization.
- Added the dependent `Roots` and `Splitting` result types plus identity and composed tower extensions.
- Implemented fixed-embedding candidate isolation, linear-root recovery, and the fuel-bounded factor/adjoin/refactor loop for `split?`.
- Preserved multiplicities from checked factorization and rejected any nonlinear step that does not genuinely increase tower dimension.
- Added compiled zero, constant, quadratic, repeated-quadratic, and two-generator quartic splitting regressions.
- Rebuilt `HexNumberFieldTower.Split` and the full repository successfully with no new proof placeholders.

# Current frontier

Splitting fields are executable through the complete dependent result. The validated-adjoin review has completed with several focused trust-boundary and coverage improvements to carry through the stack before starting flattening.

# Next step

Land this stacked milestone, address the validated-adjoin review on its parent branch, rebase this milestone, then begin primitive-element flattening without waiting for the splitting review.

# Blockers

None.
