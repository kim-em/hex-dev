# #6758 landed; sanity check passed; LLL performance program complete

## Accomplished

Sanity-checked the #6758 landing (merge b061493e, PR #6775):

- Export hex-lll-certified-harsh-extended-1e6679ff.json: all 11 rungs
  present; 15-55 hashes bit-identical to the prior committed export.
- New rungs sit on the fitted curve: p~2.65-2.79 extrapolation predicts
  44.8 / 55.5 ms at n=60/65 vs measured 45.38 / 56.10 ms (within 1.5%).
- Sanity gates: certified vs native 0.1189 at n=60 (8.4x) and 0.0903 at
  n=65 (11.1x); tally extended 7->9 interval-dispatched with indecision 0
  (enforced by the verify suite; tally target not part of the ladder
  export). Ratio table extended, harsh-cubic figure regenerated, scaling
  fit window kept at 40-55 per the directive, and both scaling tables
  reproduce verbatim from committed exports.
- Minor caveat noted: implied candidate-production deltas (full minus
  checker-only medians) are noisy at top rungs (4.2 ms @55, ~1.1 ms @65);
  independent medians, not a paired measurement - checker share is 91-98%
  there.

All eight directives of the LLL performance program are now resolved:
#6741, #6742, #6743, #6744, #6757, #6758, #6759 (+ the originating
analysis). Headline vs the session's starting point: random-bounded
certified 4.4x -> 3.5x fpLLL and native 16.9x -> 7.1x (steered);
harsh-cubic exponent broken on both paths (certified p~2.79, steered
p~2.95, from ~5.6), certified now 11.1x faster than exact native at n=65.

## Current frontier

Program complete. No open LLL directives.

## Next step

None pending; future candidates recorded in issue comments (e.g. steered
RB slope watch item at n>>180).

## Blockers

None.
