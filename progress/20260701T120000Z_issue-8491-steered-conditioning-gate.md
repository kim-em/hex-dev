# Issue #8491: steered LLL never certifies on structured bench families

## Accomplished

Diagnosed and fixed the root cause of `Hex.lllSteered` wasting a full steered
reduction + failed certification on the four structured Phase-4 bench families
(ajtai / q-ary / ntru / knapsack) before falling back to exact.

**Diagnosis (scratch probe, since the structured families live on the unmerged
`feat/hexlll-perf-restore-extend` branch — copied their generators locally):**

- Which condition fails: on every structured rung the steered candidate fails
  BOTH size-reduction (`|μ| ≤ 11/20`) AND Lovász — it is genuinely not
  `(δ, 11/20)`-reduced, `ind=true size=false lovasz=false`.
- The discriminator is NOT entry magnitude (harsh-cubic has `2^264` entries yet
  certifies) and NOT the positive-`bb` spread (random-bounded's is 45-61 bits,
  overlapping the structured families' 51-57). It is the **count of
  non-positive float `bb[i]`** from `SteeredState.init`: a genuine `‖b*_i‖² > 0`,
  so a `Float64` value `≤ 0` is a definitive catastrophic-cancellation signature.
  - structured: 13-36 non-positive of 32-40 rows (ajtai 18, q-ary 13-19,
    ntru 13, knapsack 29-36).
  - random-bounded (30..180, all seeds 1-12) and harsh-cubic (25..80): **0**
    non-positive on every rung.

**Fix (`HexLLL/Steered.lean`):** `SteeredState.wellConditioned` reads off the
sign of every `init.bb[i]` in `O(n)`. `lllSteered` now builds `init` once,
consults `wellConditioned`, and skips the doomed steered loop straight to
`lllNative` when the float GSO is degenerate. Factored `steeredReduce` into
`steeredReduceFrom` (loop + final sweep from a prebuilt state) so the gate reuses
the same `init` — no second float pass on the well-conditioned path. Added a
`skipped` outcome to `SteeredTally` distinguishing "conditioning-skipped" from
"attempted then fell back".

**Verified end-to-end** (routing via the same internal calls `lllSteered` makes):
all four structured families → SKIPPED (native, no wasted steer); all
well-conditioned families → CERTIFIED (unchanged).

Proofs: `steeredReduceFrom_memLattice_iff` added; the three `lllSteered_*`
soundness theorems in `HexLLLMathlib/Reducer.lean` gained one nested `split` for
the new skip branch. `HexLLL`, `HexLLLMathlib`, `HexLLLBenchSupport` all build.

## Current frontier

Fix complete and verified locally. SPEC updated with the conditioning-gate
paragraph.

## Next step

Second opinion, then PR.

## Blockers

None. Note: the structured bench families / comparator SVGs / perf-doc framing
live on `feat/hexlll-perf-restore-extend`; when that branch merges the four
families will route via the new SKIPPED path (their comparator "Lean steered"
curve becomes an honest copy of `lllNative`, not a failed-attempt artifact).
