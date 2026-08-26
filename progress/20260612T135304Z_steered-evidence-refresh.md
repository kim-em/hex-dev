# Steered evidence refresh: sweeps run, PR up

## Accomplished

- Discovered this session runs ON carica (VS Code remote) — the ssh
  "to carica" was a self-loop, explaining the night's watcher self-matches
  and host contention; later sweeps run directly with a load check first.
- Diagnosed the failed sweep attempts: (1) `| tail -3` swallowed the
  bench's "unregistered benchmark" error — the fpylll comparator targets
  were renamed `runFpylll*` → `runFpLLL*` (in-process fplll-ffi shim at
  the dispatch's requested parameters with transform production);
  (2) a cleanup `pkill -f` matched its own shell.
- Ran both consolidated steered family sweeps at c5a58baf on a quiet
  host: 32/32 + 44/44 rows; dispatched curves monotone on both families
  (harsh-cubic 8.39/11.91/16.61 ms at n=30/35/40 — the #6784 bump is
  gone, matching its paired table).
- Notable data shifts, recorded in the reports: fpLLL series now the
  in-process shim (HC n=55 7.4→3.3 ms; RB n=180 268→334 ms — stronger
  requested parameters + transform production); random-bounded exponent
  spread (0.53) crossed the scaling script's 0.5 gate, so that family
  reports observed ratios instead of C₃ constants now.
- Opened the refresh PR (branch steered-evidence-refresh): exports
  replaced, script repointed, figures regenerated, both report blocks +
  prose recomputed, caveats updated (fpLLL non-comparability across
  revisions). wait-for-ci + squash-merge chained in the background.

## Current frontier

PR in CI. After merge, the committed harsh-cubic figure finally matches
the shipped two-tier dispatch, closing #6784's outstanding obligation.

## Next step

Verify the merge lands and the figure renders monotone; then the LLL
program is fully quiesced.

## Blockers

None.
