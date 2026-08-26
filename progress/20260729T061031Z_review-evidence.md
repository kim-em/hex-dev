# Prime-policy review and evidence consolidation

## Accomplished

- Regenerated all factor-sweep figures with the repository's Matplotlib 3.11.1
  tool version from the clean `567b5aea` public-factor artifact.
- Completed a full `lake build` (9,629 jobs) and an independent pre-merge
  review. The review found no correctness, proof, API, or termination blocker
  and independently reproduced every headline benchmark statistic.
- Added direct executable guards for the even-power-difference recognizer and
  the 25% modular-width retention threshold, documented that probe fuel counts
  good primes, exposed subset-candidate counts in the trace response, and added
  the prime-policy spike to the existing single CI job's executable target set.
- Identified that classical and lattice corpus rows are stale because they use
  the shared selector changed here. External PARI, NTL, FLINT, and Isabelle rows
  remain current and must not be rerun.

## Current frontier

The public-factor artifact is definitive and clean: 373/392 solves, 443.618 us
median, and a 0.996 paired median ratio against verified Isabelle BZ. The
remaining evidence work is limited to the affected Hex classical/lattice
entries and the canonical sweep report that summarizes them.

## Next step

Record clean classical and lattice sweeps, refresh all three reports and plots
from the current per-system artifacts, then re-run final verification and take
the consolidated PR through CI and merge.

## Blockers

None.
