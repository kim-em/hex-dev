# Issue 8625 spike: measurement complete, report written

## Accomplished

Deliverable 1 of #8625 (the gating measurement) is done:

- `bench/HexBench/RecursiveReliftSpike.lean` (`lean_exe
  hex_recursive_relift_spike`, root lakefile, srcDir bench): executable
  unproven prototype of the recursive per-remainder re-lift, in fresh-prime
  and same-prime variants, the latter with a sub-floor scan-size cap
  (full / cap1 / cap2). Shared recombination scan (all arms including the
  today-baseline): smart subset scan + d-1 trailing filter + Mignotte-
  bounded exact division. Per-node accounting (deg, p, r, floorK, kStop,
  rungs, outcome), product/product_ok and degree-signature verification on
  every case. `RELIFT_PROFILE=phases|today|recursive|sameprime` focused
  profile modes.
- `reports/bz-recursive-relift-findings.md`: full findings.

Key numbers (run6, /tmp/relift-spike-run6.log):
- Lift-work model (sum deg^2 k): 4-16x less lift work on split families,
  9x on high_multiplicity, 0 on irreducibles (floor = core floor).
- Naive recursion loses 2.5-3.8x wallclock on split deg16-24 to (a)
  per-node choosePrimeData? (18.9 ms at deg 24 — measured via phases
  profile) and (b) failed sub-floor scan tails (~108 ms at deg-24 k=1;
  d-1 filter ineffective on factorial-content trailing coeffs; bounded
  division only ~20% because the Mignotte abort bound is loose).
- same-prime + cap2 policy: 1.8-2.1x end-to-end WIN on all split families,
  1.6x on high_multiplicity; bounded 1.16-1.27x loss on Phi15/SD3/SD4;
  swell 1.3x loss (cap1 would lose 2x there — cap must be >= 2);
  (x-1)*SD3 1.09x loss.
- Recommendation in report: mechanism viable in same-prime/cap2 form;
  sequence deliverable 2 after #8621 (balanced lift) and re-measure the
  residual wallclock win before committing to the ~5-file proof remodel.

## Current frontier

Report + prototype ready. Second opinion, then PR from branch issue-8625.

## Next step

/second-opinion on the spike + report; address concerns; open PR; comment
the measurement summary on #8625; rebase/CI follow-up.

## Blockers

None.
