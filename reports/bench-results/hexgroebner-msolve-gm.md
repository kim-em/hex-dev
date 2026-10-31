# Matched msolve diagnostics with native rows and pair pruning

Hex source fingerprint `9f64edec57c7` and msolve both complete all 16 inputs of
the frozen diagnostic suite within the same ten-second/16 GiB per-child limits.
All 32 paired reduced bases agree at every coefficient and exponent. The
[earlier portable observation](hexgroebner-msolve.md) completed 14 inputs in Hex
and 16 in msolve. The two observations are separately matched comparator
sweeps; they are not adjacent before/after timing arms.

The [summary](hexgroebner-msolve-gm-9f64edec57c7.json) and
[complete evidence archive](hexgroebner-msolve-gm-9f64edec57c7.tar.gz) retain
all 64 scheduled samples, complete outputs, output comparisons, verification
script, input suite and conversions, exact timer, driver source, manifests,
compiler/binary identities, GPL comparator notice and host context. The suite
SHA256 remains `59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
No completed sample is removed because of host activity.

The host is `chungus2`, AMD EPYC 9455. Measurements use one computational
thread pinned to automatically leased logical CPU 70. A is Hex and B is msolve;
each input runs adjacent AB then BA. Whole-process time includes startup,
parsing and complete reduced-basis output; Hex internal candidate nanoseconds
are also retained. Each child has the same 64 MiB output-file cap. Certification,
independent native checking and Lean kernel checking are excluded. Small cases
include substantial process-startup cost.

msolve remains version 0.11.0 at
`3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with GCC 16.2,
`-O3 -march=native`, GMP and FLINT 3.6.0, with all 71 upstream tests passing.
The invocation `-g 2 -t 1 -l 2` selects an exact sparse reduced grevlex basis;
FGLM and root solving are excluded. Hex uses Lean `v4.35.0-rc3`, default
generated C, the existing wide-word arithmetic and bounded scalar C row updates.
It enables Gebauer–Möller installation and proper-LCM chain pruning. The driver
uses explicit broad cumulative allowances, including 10^11 work units, rather
than relying on the default allowance. Those operational work units differ
from milliseconds and are not comparator timing budgets.

Both programs use ordinary polynomial rings over primes 32,003 and
2,147,483,647, grevlex and the written variable precedence. Input identities,
public GamBa source hashes and the fixed dense-quadratic seed remain unchanged.
The following numbers are geometric means of the two within-block
**Hex/msolve whole-process wall-time ratios**. Values above one are losses for
Hex, and all cases are retained.

| Input | p = 32,003 | p = 2,147,483,647 |
| --- | ---: | ---: |
| cyclic-5 | 2.20 | 2.30 |
| cyclic-6 | 4.57 | 4.71 |
| kat6 (six variables) | 2.32 | 2.47 |
| eco-10 | 44.71 | 44.97 |
| noon-4 | 2.09 | 2.24 |
| Reimer-5 | 16.41 | 16.79 |
| MinRank(2,2,3,2) | 1.83 | 2.01 |
| dense quadratic, 5 variables | 2.24 | 2.31 |

Eco-10 takes 3.64–3.66 seconds in Hex and 80–83 ms in msolve. Reimer-5 takes
260–265 ms versus 14–18 ms. Peak whole-process RSS is at most 93,944 KiB for
Hex and 19,300 KiB for msolve; this includes runtime/setup storage and is not
the API's packed-payload counter.

For eco-10 at the smaller prime, Hex records 203 final basis polynomials,
38 F4 rounds and 242 matrix calls. The call structure and these counters imply
203 separate final-tail matrix calls, besides the input call and 38 rounds.
The final interreduction path shares its reducer index but repeats symbolic
closure and matrix construction for each tail. This identifies reusable
preprocessing and independent multi-target reduction as concrete algorithmic
work to investigate; it does not quantify their isolated share of wall time.

This diagnostic suite covers six public families plus dense quadratics. It
is not the SPEC's hard, family-balanced and held-out acceptance suite; it lacks
the other required comparators, field adapters and parallel sweeps. Hex loses
to msolve on every input here. There is no fastest-open-source milestone or
measured language-impossibility barrier. Complete basis certificates and F4
soundness/termination remain required independently of candidate speed.
