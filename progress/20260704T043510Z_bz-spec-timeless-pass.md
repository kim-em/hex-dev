# BZ SPEC: timeless pass over the hybrid rewrite

## Accomplished

Kim's correction on SPEC philosophy: the SPEC is a clean-room
re-implementation specification and must not reference the vagaries or
mistakes of the current implementation — migration state belongs in the
issues. Second commit on the #8577 branch applying that:

- Deleted the Implementation note entirely (history + "legacy, scheduled
  for deletion" framing gone; the design speaks for itself).
- Proof obligations recast in the design's tier vocabulary, removing the
  "historical names" translation note: Group A is now
  "exhaustive-recombination correctness (backs factorClassical and
  factorTrial)" with A4/A5 restated (A4 explains how the classical
  some-case and the trial backstop inherit it); Group B is "lattice-tier
  conditional correctness" with B9 stated for factorLattice covering both
  some-exits (recombination-verified and cap certificate). No factorSlow /
  factorFast / factorHybrid / factorWithBound anywhere in the SPEC now.
- Removed implementation-state references: A5's "existing sorry'd
  theorems ... must be discharged", "the current pipeline already does",
  HO-1 / HO-4 milestone labels, `factor_headline` bridge-theorem name,
  `finitePrimeSearchNoneQuadratic` witness def name (kept the 1 + L·X
  family as the mathematical witness), "In the implementation" phrasing
  in the dispatch section (acceptance guard now stated as design).
- Aligned residual fast/slow-path phrasing to tier roles (LiftData note,
  Pitfall 10, precision-schedule termination bullets).

This subsumes most of issue #8584's SPEC deliverables; #8584 rewritten
to the residue (post-convergence consistency grep + refreshing the
#8369/#8370 issue bodies after the renames land).

## Current frontier

PR #8577 carries the full timeless SPEC. Directives #8578-#8583 unchanged
and still sequential; #8584 slimmed.

## Next step

Merge #8577 once CI is green; pod workers start on #8578.

## Blockers

None.
