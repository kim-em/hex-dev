# HexRCF balanced null calibration

## Accomplished

- Replaced the odd five-round proof sweep with an enforced six-round contract,
  balancing reference-first and candidate-first builds for every null control.
- Added a second exact same-module null at the degree-50 tactic magnitude so
  the cheap baseline spread is not misused as a noise bound for expensive
  builds.
- Tightened reusable validation to require identical null axiom policies and
  added exact sample-count, parity, metadata-spoofing, magnitude, and manifest
  tests.
- Defined mechanical comparator-floor thresholds: above 50% is raw-only and
  ineligible; above 5% within the eligible range requires both raw and adjusted
  ratios.
- Routed the floor through the same degree-keyed input lookup as the five FLINT
  rungs, rebuilt the bench, and verified all twenty-one registrations.

## Current frontier

- The preregistered artifact shape now has two null controls followed by
  fifteen substantive pairs, with six balanced rounds fixed in code.
- No release-quality samples have been collected under the revised manifest.

## Next step

- Run the full repository checks from the committed state, update draft PR
  #9027, and restack it onto the corrected comparator parent.
- Collect the two null distributions and scientific evidence only on the clean
  named benchmark host.

## Blockers

- Dedicated-host execution is external to this development worktree.
- HexRCF Phase 4 remains dependency-gated on #8972.
