# Canonical roots of a 40-bit quadratic

The quadratic `1099511627776 X² + 1099513724929` has roots
`±(1048577/1048576)i`. Its canonical root construction exhausted an 8 GiB
cgroup because the integer-root shortcut in factorization allocated
`List.range (|constant coefficient| + 1)` before filtering for divisors.
Here that requested over a trillion list entries. Isolation and squarefree
normalization were inexpensive; comparison was never invoked.

`quadraticIntegerRootFactors?` now obtains at most two candidates from the
quadratic formula, using Newton integer square root on the discriminant.
Negative and nonsquare discriminants yield no integer candidates. Exact
polynomial evaluation rejects rounded nonintegral quotients, and the existing
exact-division splitter validates each proposed linear factor. A declined
shortcut proceeds through the existing general factorization route. The
companion product, irreducibility, primitivity, and distinct-factor proofs
continue to follow that splitter; candidate distinctness is a two-element
list proof. Canonical representative selection and structural equality are
unchanged.

## Stage measurements

The compiled `hexnumberfield_quadratic` executable takes its stage and height
at runtime and consumes the result. Height `h` constructs
`(2^h + 1)² + 2^(2h) X²`. Each stage ran in its own user systemd service with
`MemoryMax=8G`, `MemorySwapMax=0`, `CPUQuota=100%`, and a 120-second wall cap,
pinned to one automatically selected allowed CPU on the shared host. The
baseline is `92d42a806`, using Lean `v4.34.0-rc2`.

All 32 completed stage samples, their selected CPU and host load, and both
RSS and cgroup accounting are retained in
[the measurement data](bench-results/hex-number-field-quadratic.json).
These are localization samples, not estimates of small timing differences.

| Height | Baseline factorization | Baseline canonical roots | Fixed canonical roots |
|---|---|---|---|
| 5 | 0.03 s, 66 MiB RSS | 0.04 s, 67 MiB RSS | 0.04 s, 67 MiB RSS |
| 10 | 0.04 s, 100 MiB RSS | 0.06 s, 122 MiB RSS | 0.04 s, 67 MiB RSS |
| 15 | killed at 8 GiB | killed at 8 GiB | 0.04 s, 66 MiB RSS |
| 20 | killed at 8 GiB | killed at 8 GiB | 0.04 s, 67 MiB RSS |

Squarefree normalization and isolation completed at every height, using
roughly 67 MiB RSS and 0.03–0.07 seconds. After the fix, factorization also
used roughly 67 MiB RSS and 0.03 seconds at every height. RSS includes shared
mapped pages; cgroup peak charges shared pages differently, so the two
memory measurements should not be interchanged.

The combined direct/arithmetic construction regression completed in 0.06 s
at 68,200 KiB RSS under a **1 GiB process-tree cap**, no swap, one CPU, and a
30-second wall cap. The existing Ubuntu CI job applies those generous bounds
to the compiled regression separately from elaboration. These are operational
catastrophic-regression limits, not portable performance promises.

## Reproduction and correctness checks

Build with `lake build hexnumberfield_quadratic`. For each `stage` in
`squarefree`, `factor`, `isolate`, `canonical`, `arithmetic`, and `regression`,
use a capped invocation such as:

```sh
quadratic_cpu=$(python3 -c 'import os; c=sorted(os.sched_getaffinity(0)); print(c[os.getpid() % len(c)])')
systemd-run --user --wait --pipe --collect \
  -p MemoryMax=1G -p MemorySwapMax=0 -p CPUQuota=100% -p RuntimeMaxSec=30 \
  taskset -c "$quadratic_cpu" "$PWD/.lake/build/bin/hexnumberfield_quadratic" "$stage" 20
```

The `regression` stage and complex conformance suite compare both canonical
roots structurally with `±((1 + ofRat (1/1048576)) * I)` and retain the exact
minimal polynomial. The real-algebraic fixture emitter serializes both roots
and the arithmetic construction. Its FLINT qqbar oracle independently selects
the exact roots from their polynomial and isolating discs, then checks real
coordinate zero and imaginary coordinates `±1048577/1048576`. Oracle rejection
tests cover missing, duplicated, reversed, and wrongly signed results.

The factorization fixtures also exercise a negative discriminant, a positive
nonsquare discriminant, large integer roots, mixed integer/rational roots,
and two nonintegral rational roots; existing cases cover repeated roots,
zero constant coefficients, content, and signs.

## Nearby allocation and repeated-work audit

The exhaustive trial fallback still uses the generic `positiveDivisors`
range in `Lattice.lean`. More seriously, `boundedCoefficientVectors` constructs
all `(2B+1)^(d+1)` coefficient vectors for candidate degree `d` before
`trialDivisionPeelAux` can test its first polynomial. Exhaustiveness requires
the search space, but does not require retaining that whole space in memory.
Streaming these searches is separate work with corresponding trial-division
proof changes. `ZPoly.factorTrial` reaches them directly: on the issue's
negative-discriminant quadratic, the shortcut declines and the divisor-range
allocation remains. `ZPoly.factorize` can also reach this backstop when modular
planning or checked recovery fails. This fix removes the allocation from the
quadratic shortcut used by ordinary canonical construction; it does not make
the explicit trial API or its backstop resource-efficient.

`ZPoly.algebraicRoots?` also exactifies roots individually. Each `exact?`
factors the same enclosing polynomial again, and `exactFactor?` isolates a
factor before `ofNormalized?` invokes canonical isolation for that factor
again. This is repeated work, rather than another coefficient-sized allocation;
sharing factorization and canonical isolation across a root family merits a
separate optimization. The nearby modular linear-split diagnostic also scans
a list of residues, but its supported prime list is capped below 501, so it
does not have the unbounded coefficient-height problem.
