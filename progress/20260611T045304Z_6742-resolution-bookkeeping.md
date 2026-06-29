# #6742 resolution bookkeeping

## Accomplished

- Reviewed the resolution of https://github.com/kim-em/hex/issues/6742
  (interval reducedness checker): implementation #6752 (interval pass with
  deterministic input-size predictor + exact fallback; tally hash-pinned
  7/10/0), SPEC #6755, evidence refresh #6756 (which also re-enabled the
  certified curves on the harsh-cubic comparator figure). Outcome vs gates:
  harsh-cubic checker n=55 7.53x (gate >=5x); crossover realized at n=50
  and n=55; zero indecision; random-bounded non-regression defended by
  interleaved A/B. Harsh-cubic Lean-certified now fits p ~ 2.65 (family
  native ~5.6) and beats native 6.7x at n=55.
- Verified the committed scaling tables regenerate verbatim from
  `python3 scripts/plots/hex-lll-scaling.py --all` (both families).
- Unblocked the two dependents: removed `blocked` from
  https://github.com/kim-em/hex/issues/6743 (margins; noted the directive
  is now purely prophylactic given observed 0 indecision, and that closing
  as not-planned is a legitimate outcome) and
  https://github.com/kim-em/hex/issues/6744 (steered native; noted the
  certifier entry point and the go/no-go budget arithmetic: ~30 ms of the
  ~75 ms n=55 budget goes to final certification, leaving ~45 ms for the
  steered loop).

## Current frontier

#6743 and #6744 are open and claimable. #6744 is the remaining big lever
(native exponent); #6743 is small and optional.

## Next step

Workers claim #6744 (and #6743 if judged worth the hash churn).

## Blockers

None.
