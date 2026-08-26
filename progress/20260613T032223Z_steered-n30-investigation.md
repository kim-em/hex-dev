# Steered reducer n=30 robustness investigation

## Accomplished

Investigated the random-bounded n=30 steered-certification failure that
forces the elbow in the Lean-steered comparator curve. Fresh evidence via
SteeredProbe.lean (untracked scratch at repo root; build by adding a
`scratch_steered_probe` lean_exe to lakefile.lean):

1. **Real and reproducible.** The steered output at random-bounded
   n=30/seed=8 fails `lllReducedCheck (3/4) (11/20)` with exactly one
   Lovász violation at adjacent pair i=27, achieved ratio 0.722 vs the
   required 0.75. Size-reduction is perfect.
2. **Mechanism = missed swap from float drift, not fuel.** fuel×2 and
   fuel×4 still fail; the loop terminates "thinking it's done." The
   default refresh period=16 lets the float bb/mu drift enough that the
   float Lovász test at the (27,28) pair wrongly passes. The final sweep
   only size-reduces (no swaps), so the missed swap survives to output.
3. **Isolated.** Across rungs 15..65 and seeds 1..12, baseline fails ONLY
   at n=30/seed=8.
4. **Two robust fixes, both eliminate every failure across that space:**
   - δsteer = (δ+3)/4 = 0.9375 (double the current (δ+1)/2 margin):
     ~1.05× steered-loop cost — essentially free. PREFERRED: principled,
     in the spirit of the existing "steer stricter for margin" design.
   - period=8 (halve refresh interval): robust but ~1.3× (the refresh
     dot-products are bignum).
5. **Uniformity payoff.** With the fix, steered loop at n=30 = 2.55 ms
   (+~0.5 ms cert ≈ 3 ms) vs exact dispatched 14.27 ms — a ~4-5× win.
   So a robust n=30 routes to steered, removing the elbow; and the
   narrow-operand steerDimThreshold=40 (calibrated under the broken
   behavior) can likely drop toward 30, potentially UNIFYING with
   steerWideDimThreshold=30 and collapsing the two-tier wide/narrow
   operand case-split — the case-split reduction Kim wants.

## Current frontier

Investigation complete; directive proposed to Kim (fix δsteer →
robustness, then re-measure the narrow steered crossover and simplify the
dispatch toward a single threshold). Not yet filed.

## Next step

On Kim's go: file the directive and fire via wt.

## Blockers

None.
