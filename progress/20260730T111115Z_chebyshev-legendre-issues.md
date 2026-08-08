# Chebyshev and Legendre optimization issues

## Accomplished

- Checked all open issues for overlaps with the six optimization candidates.
- Created GitHub issues #9104–#9109 covering M1 classical lifting,
  degree-aware bounds, modular-kernel optimization, modular irreducibility
  research, adaptive prime costing, and post-M1 relift simplification.
- Included representative baseline measurements, implementation constraints,
  acceptance criteria, and explicit before/after measurement requirements.
- Added the canonical dependency DAG to every issue.

## Current frontier

Issue #9104 is the critical-path root. Modular profiling in #9105 can proceed
in parallel, while #9106–#9109 consume the integrated M1 baseline in stages.

## Next step

Begin #9104, preserving the current adaptive prime-width behavior while
replacing the classical M2 lift/reconstruction with the verified
original-coordinate M1 form.

## Blockers

None.
