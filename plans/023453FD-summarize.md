## Current state

The last closed summarize issue is #2947, closed at 2026-05-10T07:05:22Z. More
than fifty PRs have merged since then, spanning the HexBerlekampZassenhaus
modular and recombination proof surface (small-prime witnesses, prime-chooser
certificates, irreducibility certificate projections, ZMod64 field support,
recombination quarantine, normalization tightening), HexPolyFp Yun and
derivative-split work (square-free quotient proof path, derivative quotient
common-divisor helpers, reachable Yun common-divisor provider, derivative-split
common divisor base), HexMatrix RREF / row-echelon proof work (row-span
transport, nullspace soundness and cancellation, spanContains completeness,
matrix-vector transport, matrix multiplication laws), HexBZ Mathlib bridge work
(BHKS bad-vector hypotheses, BHKS Lprime/W separation, cap separation theorem,
executable cap), HexGramSchmidt prefix span work, and several bench/conformance
refreshes.

The project needs the next Phase 4/5 checkpoint so planners and workers can see
the current frontier without reconstructing it from PR history.

## Deliverables

1. Add a new progress checkpoint summarizing work merged since #2947 / closed at
   2026-05-10T07:05:22Z, grouped by library and proof / benchmark / conformance
   stream.
2. Include quality metrics at the checkpoint: `python3 scripts/status.py`,
   `python3 scripts/check_dag.py`, Lean `sorry` count, Lean `axiom` count, and
   `native_decide` textual hits.
3. Identify the current open frontier and the highest-priority next issues,
   including the still-open human-oversight HexBerlekampZassenhaus
   HO-1 / HO-2 / HO-3 / HO-4 streams (#2564, #2565, #2566, #2567) and #2637,
   their blocking dependency chains, and the HexBZ core capstone chain
   (#3084, #3085, #3086, #3087).

## Context

Read:

- #2947 and its progress checkpoint
- merged PRs since #2947 closed at 2026-05-10T07:05:22Z
- `PLAN.md`
- `PLAN/Conventions.md`
- current open `agent-plan` issues and open PRs
- human-oversight issues #2564, #2565, #2566, #2567, and #2637

This is a summarize issue only. Do not change Lean source, SPEC files, top-level
`PLAN.md`, or top-level `AGENTS.md`.

## Verification

- New checkpoint progress file exists under `progress/`.
- The checkpoint reports the quality metrics listed above.
- The summary names open PRs/issues accurately at the time of the review.
- `git diff --check`

## Out of scope

- Implementing any source change.
- Closing human-oversight issues.
- Creating broad replacement plans for existing open work.
