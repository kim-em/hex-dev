# Three harsh-cubic figure/ladder directives filed

## Accomplished

Filed the three directives for Kim's harsh-cubic figure concerns:

- https://github.com/kim-em/hex/issues/6757 (HexLLL: recalibrate the
  reducedness dispatch threshold at the small harsh-cubic rungs) — the
  n=25 elbow is the exact/interval dispatch boundary; export medians and
  the dispatchFactor docstring's own calibration claim both suggest the
  switch is one rung conservative. Measurement-gated; productive doc-only
  outcome specified if the routing turns out optimal.
- https://github.com/kim-em/hex/issues/6758 (HexLLL: extend the certified
  harsh-cubic ladder to n = 60 and 65) — aligns the certified rung
  schedule with native/Isabelle; sanity gates (indecision 0 at the new
  rungs, certified < native) rather than perf gates; nonzero indecision
  must be reported on #6743 too. Cross-linked with 6757 (shareable carica
  sweep).
- https://github.com/kim-em/hex/issues/6759 (HexLLL: footnote the
  Isabelle-certified per-request fplll fork on the comparator figures) —
  per Kim's decision: footnote only, rendered in the figures by the plot
  script plus a matching report sentence; no eligibility or table changes.

## Current frontier

In flight: #6743 and #6744 (wt sessions spawned earlier), #6757–#6759
claimable.

## Next step

Optionally fire 6757/6758/6759 via wt when Kim wants them started.

## Blockers

None.
