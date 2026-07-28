# Designated shared-host proof evidence

## Accomplished

- Replaced the categorical shared-machine exclusion with an explicit
  designated-shared-host protocol for fresh-module proof evidence.
- Added fail-closed hostname and logical-CPU preregistration. The runner pins
  itself before warmup, timed children inherit that affinity, and every arm
  verifies that the runner affinity has not changed.
- Required at least two representative same-module null controls and six
  balanced rounds for shared-host release evidence; all fresh-module sweeps
  now require an even number of rounds.
- Retained global load, CPU pressure, affinity, physical-core/SMT topology,
  and concurrent Lake/Lean counts around every measured arm. Unrelated
  Lake/Lean process presence is recorded context; saturation still aborts.
- Added regression tests for host identity, affinity pinning, control/sample
  admission, process-presence handling, saturation rejection, and universal
  orientation balance.
- Added normative RealRootsMathlib proof-evidence documentation and exact
  release commands for both RealRootsMathlib and RCF on `chungus2`, CPU 47.

## Current frontier

- The protocol implementation and 45 related Python tests are green on the
  stacked evidence branch.
- The structural RealRootsMathlib probe fixes are separately published on PR
  #8980 so this protocol can rebase cleanly after that milestone merges.

## Next step

- Obtain independent review of the protocol, merge PR #8980 after its own
  corrected review/CI, rebase this branch, and run the six-round RealRoots
  release sweep from a clean checkout.

## Blockers

- None. Current host activity is measured and bounded by the protocol rather
  than treated as a categorical blocker.
