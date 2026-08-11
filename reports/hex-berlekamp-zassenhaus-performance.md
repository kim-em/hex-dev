# HexBerlekampZassenhaus Performance Report

This report describes the supported public integer-polynomial factorization
entry point. Standalone classical and lattice entries remain development
diagnostics, not alternative public implementations.

## Current measurement

The current Hex record measures clean source revision
`58c873ca` with
`leanprover/lean4:v4.33.0-rc1`.

Hex was measured on 2026-08-10 and the external systems on 2026-08-01 on
`chungus2`, an AMD EPYC 9455 Linux x86-64 host. The harness and service were
pinned to verified-idle CPU 1 for Hex and CPU 0 for the external record. New
measurements must use `scripts/bench/idle_core.py`, because other work shares
the host, and must record the selected core alongside the artifact. The CPU
0/70 control in [hexbz-support-traversal.md](hexbz-support-traversal.md) checks
that an idle core is interchangeable with CPU 0 on this host. The committed
392-row corpus has SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
Services were persistent and warmed. Each call had a ten-second cutoff; rows
below one second used the median of five calls, and slower rows used one call.
The external record attempted every row. The Hex record stops a monotonic
family after three consecutive timeouts; this skipped only `hoeij_F630`, whose
recorded timeout is unchanged by the shortcut.

The current artifacts are:

- `reports/bench-results/hexbz-factor-sweep-58c873ca-hex-chungus2-cpu1.json`
  for Hex, SHA-256
  `3c96905dae847e634de7e20934a9074e582ce7d545294471adebf945b6c1efe9`;
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  for FLINT, NTL, PARI, and both Isabelle implementations, SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`.

The second artifact contains an older same-run Hex row too, but the clean Lean
4.33 Hex record supersedes it. The plotting and freshness tools select the
newest valid record independently for each system.

The prior PARI comparator artifact used PARI/GP 2.17.3; the current Nix closure
provided 2.17.2. No cross-record PARI change is attributed to Hex. All current
ratios and curves use the fresh same-protocol 2.17.2 measurement above.

## Cross-system result

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 383 | 9 | 273.175 us | 6.693 ms | 3.972 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

Every answering system agreed with the committed factor-degree oracle or with
the other systems on rows without one.

For paired comparisons, both measurements must exceed ten times their own
protocol overhead. On 189 eligible common rows, Hex divided by verified
Isabelle BZ has median `0.506x`, p10-p90 `0.316x-1.525x`, and a 153-36 win
split. Hex therefore has a substantial aggregate lead over verified Isabelle
BZ, though individual rows still go both ways.

The optimized unverified libraries remain substantially faster. Median Hex
ratios are `6.493x` against FLINT, `6.316x` against PARI, and `3.020x`
against NTL on 80, 86, and 142 eligible pairs respectively.

## Effect of the divisibility obstruction

Between constructing a recombination candidate and dividing by it, the search
now reduces both modulo a fixed word-sized prime and rejects the candidate when
the finite-field remainder is nonzero. The filter can only reject; exact
integer division is still the only accepting test.

Across the probed corpus, 4,204 of the 4,302 candidates reaching the filter
were rejected, and all 98 that passed were genuine divisors. `xpow120_minus1`
moves to 0.306x, `cyclo_phi275` to 0.234x, and `cyclo_phi1031` changes from a
ten-second timeout to 4.176 s; the aggregate of `xpow48/105/120` is 0.361x and
the whole corpus is 0.704x. The median over rows above one millisecond is
0.994x against a measured noise floor of 0.8%. The cost side is `wilkinson` at
1.022x, where the unforced sweep peels one linear factor at a time and the
filter rejects none of its candidates.

Those ratios are measured against `main` with this branch merged out, built and
swept in the same session with four fully interleaved repeats per side, not
against an earlier committed record: `main` moves under a branch, and against a
stale record rows this change cannot touch move more than rows it can.
[hexbz-modular-obstruction.md](hexbz-modular-obstruction.md) is the measurement
record, and it also states what the change does not fix.

## Effect of the support-traversal change

The head-forced recombination leaf now runs its metadata-only filters before
it materializes anything, and the lift modulus and per-factor degree and
trailing coefficient are precomputed once per subset-cardinality level. The
Swinnerton-Dyer family moves from 0.684x to 0.850x against the preceding
record, and at that revision its median against verified Isabelle BZ improved
from `2.799x` to `2.116x`. The quadratic-norm certificate has since taken the
current median to `0.611x`, as tabulated below. No other family moved more than
3% in the support-traversal comparison.
[hexbz-support-traversal.md](hexbz-support-traversal.md) is the measurement
record.

## Effect of the earlier proposal-path optimization

The proposal path now has two general rules:

1. search support sizes one through three once, then repeatedly peel support
   sizes one or two from the exact quotient while reusing the same Hensel
   lift;
2. build a selected-coordinate proposal lattice only after peeling has made
   exact progress. With no peel, go directly to the exact full-CLD fallback.

These rules contain no family or benchmark names. They retain repeated cheap
progress on Wilkinson inputs and avoid speculative lattice work on inputs such
as `sd6` where the cheap search found nothing.

The current record solves `hoeij_F190` in 3.287 seconds after peeling a
degree-10 factor and partitioning the degree-180 residual into two degree-90
pieces. It solves `sd6` in 27.044 milliseconds after the no-progress proposal
skips its futile selected-coordinate lattice. Under the declared repetition
policy F190 uses one timed call, while `sd6` is the median of five.

Current representative Wilkinson timings are 3.480 ms at degree 24, 9.431 ms
at degree 40, and 21.266 ms at degree 56. These values and the hard-row values
are coverage snapshots, not a new optimization A/B.

## Relative to verified Isabelle BZ

| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |
|---|---:|---:|---:|
| Chebyshev | 7 | 0.388x | 7 |
| Conway | 70 | 0.453x | 51 |
| Cyclotomic | 23 | 0.462x | 19 |
| Cyclotomic products | 18 | 0.601x | 16 |
| Laguerre | 11 | 0.601x | 11 |
| Legendre | 12 | 0.503x | 11 |
| Random products | 23 | 0.452x | 22 |
| Swinnerton-Dyer products | 7 | 0.651x | 5 |
| Swinnerton-Dyer | 6 | 0.611x | 6 |
| Wilkinson | 12 | 1.106x | 5 |

There is no common answered Hoeij-Zimmermann row with verified Isabelle BZ.
The certificate turns Swinnerton-Dyer from the largest family-level gap into a
lead on all six eligible pairs. Wilkinson is now the only family in this table
whose median remains slower than verified Isabelle BZ.

## Remaining long tail

The nine Hex timeouts are three Swinnerton-Dyer products:
`sd5_x_sd5shift1`, `sd6_x_phi105`, and `sd6_x_sd6shift1` -- and six
Hoeij-Zimmermann rows: `hoeij_F192`, `hoeij_F256`, `hoeij_F351`,
`hoeij_F630`, `hoeij_P7`, and `hoeij_S9`.

The remaining open recombination work is deliberately measurement-gated.
Issues #9151 and #9152 propose reusing the lift modulus, support data, and target
image at their mathematical lifetimes; #9153 then asks whether the retained
other-prime degree-reachability bitsets reject enough leaves to pay for a
production filter. Their motivating profiles predate the quadratic-norm
certificate, so the current rows that actually reach recombination must be
remeasured before any of the three changes production.

## Where the mid-tail time goes

[`hexbz-cactus-elbow.md`](hexbz-cactus-elbow.md) preserves the phase-attributed
record of the former solved-rank 125-140 crossover. The quadratic-norm
certificate removes it: on the current 160-row combined mixture Hex solves 151
rows against Isabelle BZ's 141, and the worst cumulative Hex/Isabelle ratio
over ranks 125-140 is `0.689x` at rank 133, below the `0.85x` acceptance bound
at every rank in that window. The cumulative times from which that ratio is
computed are reproduced by `python3 scripts/bench/cactus_rank_table.py --lo
125 --hi 140`; full
before/after attribution is in
[`hexbz-quadratic-norm-certificate.md`](hexbz-quadratic-norm-certificate.md).
