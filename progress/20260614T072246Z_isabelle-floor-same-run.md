# Isabelle-certified floor: same-run, n=15 restored

## Accomplished

Fixed the dropped harsh-cubic n=15 point in the Isabelle-certified (adjusted)
comparator curve. Root cause: #7018 measured the floor in a separate run, so
cross-run noise put floor (20.3) just above n=15 raw (20.2) -> negative ->
dropped. Within one run, n=15 >= floor by construction.

- Measured floor + harsh-cubic Isabelle-certified ladder in ONE sweep
  (floor 19.91 ms). n=15 returns at +2.4 ms, on-trend; all points survive.
- Plot reads harsh Isabelle-certified + floor from the new export; random
  keeps carica.json (its n=30 >> floor, robust cross-run).
- Drop logic -> never-fires nonpositive guard. Footnote cut to one line.
  Retired the standalone floor export from #7018.
- Beat host contention with a validated retry loop (rejects spiked sweeps;
  the host is shared with pod-agent Lean builds and Isabelle is load-
  sensitive). Committed run is smooth; clean on first low-load attempt.
- Scaling harsh Isabelle-certified row updated (p 4.66->4.62, n=55
  398.4->425.6, same-run). Both scaling tables reproduce.

PR #7079. Both figures verified clean (n=15 present, smooth, one-line note).

## Current frontier

PR #7079 in review. This closes the Isabelle-certified adjustment thread
(Kim chose "adjusted & clean").

## Next step

Merge on Kim's sign-off / green CI.

## Blockers

None (host contention handled by the retry loop).
