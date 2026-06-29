# Handoff prompt audit

## Accomplished

Fact-checked the proposed FactorSoundness handoff against the current checkout.
Verified the named executable, recovery, partition-refinement, and soundness
anchors, and inspected the current `toMonicLiftData`/`coreLiftData` definitions,
M1 recovery constructors, and core-coordinate bridge lemmas.

## Current frontier

The handoff is directionally aligned with the code, but it underspecifies the
existing core-coordinate recovery/termination tower and the many hypotheses
required to apply the core-lift partition-refinement theorem from the public
soundness capstone.

## Next step

Revise the handoff prompt with the concrete corrections from this audit before
launching a fresh interactive proof session.

## Blockers

No code blockers were encountered. This session intentionally made no Lean code
changes.
