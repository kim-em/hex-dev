# Prime-probe downside control

## Accomplished

- Ran a clean-revision full sweep of the narrowed trigger. Paired eligible
  Hex/Isabelle performance improved from a 1.08 median ratio and 111–126 wins to
  1.03 and 117–125, but the sweep also exposed two lost solves at the 10-second
  cutoff: `xpow120_minus1` and `sd5_x_phi45`.
- Extended `factorTrace` with the first-good prime and factor count. This showed
  `sd5_x_phi45` needed the high-width trigger (`r = 28`), while `x^120 - 1`
  suffered because a marginal `r = 39` to `r = 37` change abandoned a much
  better recombination prime.
- Lowered the high-width degree floor to 50, required a probed choice to remove
  at least one quarter of the current modular factors, and reduced the probe
  budget from eight good alternatives to two. All established wins occur in
  those first two alternatives.
- Excluded even `x^n - 1` from speculative high-width probing: its explicit
  difference-of-squares structure makes recursive classical splitting cheap.
- Re-ran cyclotomic, cyclotomic-product, Legendre, and SD-product sentinels.
  `x^120 - 1` is solved near its baseline again; `x^105 - 1`, the prime
  cyclotomics, Legendre `P_30`, and `sd5_x_phi45` retain large speedups. The
  superseded 371-solve artifact was removed.

## Current frontier

The selector now controls all three observed downside modes: false broad
triggers, insignificant prime changes, and excessive probe depth. Focused
families have their baseline solve coverage with no material regression.

## Next step

Commit the final policy, collect the definitive clean-revision 392-instance
artifact, refresh reports and plots, then run full verification and the
requested independent review before opening the PR.

## Blockers

None.
