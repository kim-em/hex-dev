# Issue #9160 follow-up measurement review

## Accomplished

Reviewed the revised PR at `dbd9f33c`, including the production packed
definitions, every new ladder and multiply rung, the merge logic, the generated
C, the attribution report, and the seven raw reduction samples for all 24 rows.
Recomputed the important paired deltas and split representative deltas by ladder
direction. Ran `lake build hexbz_factor_service` successfully.

The large `mirrored - hoistedPivotRow` result is stable and the wrong-baseline,
flat-outer-loop, readback-description, and UInt32-characterization findings are
substantially repaired. The multiply control does contain the intended second
remainder and is usable as a two-divide throughput probe, but not as a causal
share.

## Current frontier

The remaining review concerns are methodological and documentary. Seven
alternating runs leave a 4/3 direction imbalance, so their median does not cancel
order effects; several small deltas visibly depend on direction. Raw samples are
retained only for ladder reductions, while the fixed-order Barrett/UInt-width
variants and stage/readback spans are still independently medianed. The report's
linear one-rung-at-a-time description is also false for the now-branched ladder,
and the array-pivot and flat-row pairs retain small extra differences.

## Next step

Counterbalance an even number of runs and aggregate forward/reverse pairs, retain
raw samples for the prototype variants and stage spans, and rewrite the report to
use explicit baselines and to call the multiply result a throughput ratio rather
than a causal share. Either add paired uncertainty for Barrett or leave that
choice unresolved rather than claiming a 1.5% upper limit.

## Blockers

None.
