# Prime-policy trigger refinement

## Accomplished

- Ran a full 392-instance sweep of the first degree-based prime-probe policy.
  It confirmed the intended 5–25× wins, but also exposed up to 12× regressions
  on sparse and composite cyclotomics where modular probing could not improve
  the first choice enough to repay its cost.
- Replaced the broad degree-50 trigger with three evidence-backed cases:
  coefficient-swollen transforms with at least nine modular factors,
  degree-100 transforms with at least 24 modular factors, and degree-50 uniform
  all-one prime cyclotomics.
- Added a `factorTrace` diagnostic service entry that reports the selected prime
  and lifted modular-factor count for arbitrary corpus requests.
- Re-ran the complete cyclotomic and cyclotomic-product families. Every former
  major regression returned to within about four percent of the established
  baseline, while `Phi_61`, `Phi_151`, `Phi_179`, and `x^105 - 1` retained
  roughly 5.6–25× speedups.
- Removed the superseded full-sweep artifact for the rejected broad trigger.

## Current frontier

The corrected policy is green on its focused diagnostic and on both affected
families. A final clean-revision full sweep is still required before report and
plot refresh.

## Next step

Commit this trigger refinement, run the final 392-instance Hex sweep once, and
compare every eligible row and family with both the current Hex baseline and
the existing same-host Isabelle artifact. If clean, refresh durable reports and
plots, run the full build/conformance checks, obtain an independent second
opinion, then open and merge the PR.

## Blockers

None.
