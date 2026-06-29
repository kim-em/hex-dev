# Progress — CLD cut architecture review

## Accomplished

Checked the proposed aggregate-cut fix against the BHKS construction for
integer polynomial factorization. The bounded mathematical object is the
aggregate logarithmic derivative `Phi(g) = f * g' / g` for an actual global
factor. The executable's sum of per-local-factor `psiCut` columns is not the
published construction, because the cut is nonlinear under modular wraparound.

## Current frontier

The right verification target is not a lattice whose rows are already cut high
bits. It is a per-row linear CLD lattice with a modulus/period coordinate
allowing the row sum to be recentered modulo `p^a`; rounding/cutting is then
part of the lattice embedding and analysis, with an explicit rounding-error
bound.

## Next step

Refactor the executable specification toward the BHKS one-coefficient lattice:
store full per-local CLD residues, include the period vector, and prove that
true factor supports have a short representative because the aggregate CLD
coefficient satisfies the Mahler/Mignotte bound.

## Blockers

No blocker from the mathematics. The current per-row `psiCut` construction
cannot support the claimed tight bound without changing the lattice
construction.
