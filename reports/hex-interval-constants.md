# Bounded π and exp(1) point certificates

`Hex.Interval.Constants`, imported by `HexInterval`, supplies two versioned
Mathlib-free sources: `Source.piMachinV1` and `Source.expOneTaylorV1`.
`generate limits source bits order` computes an exact rational approximation,
projects its two bounds outward through checked singleton division, and checks
the final width against `2^(-bits)`. `enclose` chooses order `bits + 4` and
rounding grid `bits + 2`; it never increases the caller's limits.
`check limits source bits certificate` authenticates the requested subject and
precision, preflights the literal data, recomputes its center, remainder and
endpoints, and returns a checked finite interval. Failures are explicit.

## Formulas and ownership

For π, write

- `S_n(1/q) = sum(i<n) (-1)^i / ((2*i+1)*q^(2*i+1))`;
- `R_n(1/q) = q² / (q^(2*n+1)*(q²-1))`.

The center is `16*S_n(1/5) - 4*S_n(1/239)` and its symmetric radius is
`16*R_n(1/5) + 4*R_n(1/239)`. This is the geometric remainder, not the
smaller alternating next-term remainder.

For exp(1), the center is `sum(i<n) 1/i!` and the symmetric radius is
`(n+1)/(n!*n)`, with `n > 0`. An integer recurrence retains the partial-sum
numerator over `n!`; it does not repeatedly recompute factorials.

A `Certificate` contains the source identity, width bits, order, rational
center/radius, and both closed dyadic cuts. Core theorems authenticate the
accepted source, precision, positive order, exact approximation, ordered cuts,
requested dyadic width and exact interval view, and identify the retained
arctangent power. Real containment and effective progress for the full
schedule belong to [#10342](https://github.com/kim-em/hex-dev/issues/10342).
The runtime has no Mathlib import, callback assumption, proof placeholder,
external planner or new trusted primitive. Unchecked formula and projection
helpers are exposed for companion proofs; only `generate`, `enclose` and
`check` are resource boundaries.

## Resources

The public limits separately cap order, conservative integer-bit, work,
allocation and replay charges, and the existing endpoint / precision /
rational-quotient resources. The four series charges are predetermined functions
of order and requested precision, not counters of realized work. The polynomial bit bound accounts
for even unreduced accumulation of every arctangent fraction. Gcd reduction
can only shrink that bound. Cubic bit-work and quadratic cumulative-bit
allocation charges per primitive cover classical integer arithmetic and
normalization. These intentionally conservative logical charges do not
predict wall time or heap bytes. Computed rational witnesses are additionally
checked against the bit charge, and reversed cuts are rejected explicitly.
`limitsFor bits` supplies a generous request-scaled schedule; it is not a
sanitizer. Untrusted requests require independently chosen caller caps.
Finite tests do not replace the companion's effective-progress proof.

## Conformance

`ConstantsConformance` uses ordinary public imports and tests both generators
and checkers at 0, 1, 8, 32, 128, 256 and 1000 width bits. It also covers first
terms, insufficient approximation order, zero/billion-sized requests, every
independent resource cap, changed subject/precision, forged sums/remainders,
and changed/reversed/oversized cuts.

The compiled `hexinterval_emit_constants` emits original inputs, complete exact
witnesses, cuts and successful replay. `scripts/oracle/interval_constants.py`
recomputes the formulas with Python `Fraction`, direct powers and factorials.
It verifies exact outward grid cuts and actual final width. Its independent
π enclosure uses `π = 4*(atan(1/2)+atan(1/3))` with alternating next-term bounds;
its e enclosure uses a longer factorial sum and a one-sided tail.
All 14 fixtures pass. Oracle mutation tests reject altered results and malformed
schemas. The existing CI oracle runner regenerates and diffs the committed
[fixtures](../conformance-fixtures/HexInterval/constants.jsonl).

## Compiled acceptance evidence

The four fixed lean-bench registrations are 1000-bit acceptance/hash anchors,
not Phase-4 complexity registrations or absolute-budget gates. Inputs pass
through `IO.Ref`; checker inputs are generated before timing. Both operations
return and hash precision, order, the rational witness and both cuts; each
registration fixes the source identity. This prevents timing a constant load
or accepting a result with missing witness work.

| Source | Producer median | Checker median |
| --- | ---: | ---: |
| π, Machin v1 | 93.419 ms | 93.084 ms |
| exp(1), Taylor v1 | 2.716 ms | 2.703 ms |

Each median has five completed samples. All hashes match the independently
checked fixture values. Measurements use one automatically selected logical
CPU on the shared host; every completed sample is retained. These absolute
values describe that host. The [raw export](bench-results/interval-constants/ordered/acceptance.json),
[console output](bench-results/interval-constants/ordered/acceptance.log), and
[context](bench-results/interval-constants/ordered/context.json) retain individual
samples, CPU, host/load, exact command, source hashes and executable digest.
The context names the exact source commit with both witness-size and ordered-cut
checks enabled; generated output artifacts account for the export's dirty label.

The [initial samples](bench-results/interval-constants/acceptance.json) and
[their context](bench-results/interval-constants/context.json) are also retained.
They predate those two checks. Their context records a commit and
[reconstruction patch](bench-results/interval-constants/measured-source.patch)
for the exact initial measured source hash, removing only an erased theorem
from that commit. These are separate acceptance runs, not a paired performance
comparison; no improvement claim is inferred from their timings.

## Remaining obligations

[#10334](https://github.com/kim-em/hex-dev/issues/10334) remains open for
formal core resource/rounding contracts, applicable
whole-library phase gates, and Phase-4 complexity/comparator/attribution evidence.
In particular, core theorems still need to connect accepted literal cuts to
`center - radius` and `center + radius` through the executed checked quotient;
the exposed ordered view alone does not establish outward containment.
The fixed acceptance anchors do not discharge those performance requirements.
The companion separately owns real soundness, effective convergence and
ordinary-kernel reconstruction measurements; conformance and compiled replay
do not establish those analytic proofs. No whole-library phase counter is
advanced by these provider measurements.
