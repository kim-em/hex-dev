# Harsh-cubic figure concerns triaged; #6743/#6744 fired off via wt

## Accomplished

- Diagnosed the Lean-certified "elbow" at n=25 on the harsh-cubic
  comparator: it is the input-size dispatch boundary from #6752 — rungs
  n<=25 route to the exact d/nu checker (steep slope), n>=30 to the
  interval pass (~n^3). Export medians (hex-lll-certified-835734e7.json):
  20->25 grows 2.31x, 25->30 grows 1.43x. Extrapolating the interval slope
  back to n=25 (~3.9 ms) vs measured exact (4.89 ms) suggests the
  predictor may be one rung conservative.
- Checked the Isabelle-certified startup question against existing
  doctrine: the report already publishes protocol-overhead-adjusted
  ratios and an eligibility floor; at harsh-cubic n=15 the
  Isabelle-certified measurement (~20.3 ms) is ~93% per-request fplll
  fork (~18.8 ms documented), failing the spirit of the 5% floor.
- Recommended to Kim that all three concerns (predictor calibration,
  certified ladder extension to n=60/65, small-n Isabelle-certified
  eligibility/adjustment) go via issues, since each needs a carica run
  and/or a reporting-policy decision; offered to draft them.
- Spawned worktree agent sessions via `wt 6743 6744`
  (~/worktrees/hex/hex-issue-{6743,6744}, branches issue-{6743,6744}).

## Current frontier

#6743 (margins, prophylactic) and #6744 (steered native) in flight in
parallel sessions. Three new figure/ladder issues awaiting Kim's go-ahead.

## Next step

Draft the three issues if Kim agrees; monitor the spawned sessions.

## Blockers

None.
