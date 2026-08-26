# Prime-policy width tuning

## Accomplished

- Audited the remaining public-Hex versus verified-Isabelle losses after the
  merged packed-Hensel work. The largest rows are shared with the classical
  tier, so the remaining gap is in the common factorization core rather than
  hybrid dispatch.
- Added `hex_prime_policy_spike`, which exposes first-good versus adaptive
  prime choice and end-to-end factor traces on representative hard corpus
  inputs.
- Changed bounded adaptive prime selection to retain a probed prime with fewer
  modular factors, rather than discarding every non-singleton improvement.
- Extended probing to degree-50-and-higher transforms while retaining the
  existing high-factor-count/coefficient-swell trigger. Added an early stop for
  a factor-count halving that still leaves at least eight factors.
- Preserved the selector's existing correctness theorems: every returned choice
  still inherits the candidate's primality, good-prime, modular-image, and
  Berlekamp-form properties.
- Targeted timings reduced `x^105 - 1` from about 1.37 s to 53 ms, cyclotomic
  `Phi_179` from about 305 ms to 43 ms, `Phi_61` from about 25 ms to 4.6 ms, and
  Legendre `P_30` from about 177 ms to 31 ms. Conway `(2,38)`, Chebyshev `U_24`,
  and SD5 stayed at their prior timings.

## Current frontier

The tuned selector and diagnostic build successfully. The targeted evidence is
strong, but the full 392-instance corpus has not yet been swept, so aggregate
Hex/Isabelle movement and any less-obvious regressions remain to be measured.

## Next step

Commit the clean implementation baseline, run the full Hex sweep once against
the existing same-host Isabelle artifact, then tune only if the corpus evidence
shows a material regression. Refresh the report/plots, obtain the requested
independent second opinion, open the PR, merge it after CI, and continue from
the new performance frontier.

## Blockers

None.
