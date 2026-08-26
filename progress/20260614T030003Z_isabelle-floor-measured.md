# Isabelle-certified comparator floor: measured, not hardcoded

## Accomplished

Replaced the hardcoded ~18.8 ms Isabelle-certified per-request floor with a
measured committed benchmark (Kim chose "measured benchmark" over a sourced
constant). PR #7018, branch isabelle-floor-measured.

- Registered `runIsabelleCertifiedProcessFloorNormSq` (trivial 2x2
  svp_certified request) in HexLLL/Bench.lean; measured 20.296 ms on carica
  (the real floor — 18.8 was an audit-host underestimate).
- Plot reads the floor from the committed export and subtracts it; rungs at
  or below the floor are dropped (entirely process-bound noise) rather than
  crashing the log axis. Harsh-cubic n=15 (raw 20.2 ~ floor) drops; all else
  survives. Single clean "Isabelle certified (adjusted)" curve, no reference
  line (the earlier raw+line attempt was visually noisy — Kim rejected it).
- Reports updated incl. §Per-call overhead now citing the registered target.
  Scaling fits untouched (raw medians).

## Process notes

- Tried fitting the floor from the ladder (total = floor + C n^p): not robust
  (gave 26/29 ms, family-inconsistent — random-bounded has no floor-dominated
  rung to constrain it). Direct measurement was the right call.
- The measured floor (20.3) > harsh n=15 raw (20.2): n=15 is pure fork, which
  is why de-flooring it is meaningless and it's dropped.

## Current frontier

PR #7018 in review. The comparator-figure work Kim raised this session is
otherwise complete (n=25/35/40/30 elbows + the floor adjustment).

## Next step

Wait for CI / Kim's sign-off, merge.

## Blockers

None.
