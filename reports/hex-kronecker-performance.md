# HexKronecker performance

## Scope and method

The `expression-checker` and `term-list-products` families cover atoms
`1, 2, 3, 4, 6, 8` and degrees `2, 4, 8, 16`. Each of the three arms accepts
18 points and records six preflight declines. The tree family compares a
power of a sum with its expanded integer support, converted to an expression
tree. The product family checks a rectangular `1 × 2` by `2 × 1` product,
using both `plain` and `signedPacked` with the same polynomial inputs.

Measurements use lean-bench's six-trial schedule on the shared host, pinned
to one automatically leased CPU. All completed samples are retained in
[the raw export](data/hex-kronecker/bench-runtime.json). Environment, result hashes,
RSS, inner repeats, and every individual duration are included. The
[run log](data/hex-kronecker/bench-runtime.log) records the selected CPU; the
operation profiles below record source SHA-256 hashes. The earlier
[interrupted run](data/hex-kronecker/bench-interrupted.log) is retained as
partial evidence; it is not treated as a complete baseline.

## Cost claim

All three parametric registrations select **mode 2: one-sided upper bound**.
The parameter is a grid index. The model evaluates that point's actual
reported packed bit bound `N`, expression-node or support count `T`, and
explicit square-and-multiply count `M`. It charges `O(T * budgetBits + M * N²)`.
The support model also charges exponent-list traversal. Thus it accounts for
the integer work and does not claim complexity merely in the polynomial
operation count or atom count.

Mode 1 has no single tight family-specific scaling law here: the grid varies
support, coefficient sizes, exponent codes, and the balance of the integer
multiplication operands together. The common dense-box bound may exceed the
actual operand size. GMP also selects size-dependent
[multiplication algorithms](https://gmplib.org/manual/Multiplication-Algorithms).
The published [basecase bound](https://gmplib.org/manual/Basecase-Multiplication)
is quadratic for equal-length operands and covers the multiplication phase
observed in the profiles. Faster GMP algorithms remain below this bound.
Primitive recursors avoid unnecessary kernel recursion bookkeeping; proved
compiler rewrites supply executable recursive equations. Preflight retains
roots and the exceptional descendants below zero products or zero powers.
`Expr.analyze_bits` proves that this gives exactly the full subtree maximum.
Difference lists collect these bounds in linear time. The additional linear
cap term covers materializing the saturation threshold,
copying/subtraction, and single-limb division on this registered family.
The proved small-operand fast paths preserve exact saturation and avoid those
cap operations inside most bound calculations.

The harness currently reports a two-sided verdict. Its `inconclusive` result
with a negative normalized slope is the expected faster-than-bound outcome
for these mode-2 registrations, and is recorded as **within declared upper
bound (observed faster)**. It is not a two-sided complexity match.

| Registration | Raw verdict | Normalized slope | Upper-bound assessment |
| --- | --- | ---: | --- |
| `runTree` | inconclusive | -6.498 | within bound, observed faster |
| `runPlain` | inconclusive | -5.622 | within bound, observed faster |
| `runPacked` | inconclusive | -8.618 | within bound, observed faster |

## Complete grid

`N` is the structural signed packed-bit bound; signed packing includes its
outer products. The [metadata](data/hex-kronecker/grid.jsonl) also records
`D`, digit width, inner size, outer slot width, operation count, and result
hash for each point. Times below are medians in milliseconds.

| Atoms | Degree | Tree N | Tree ms | Plain N | Plain ms | Signed N | Signed ms |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 8 | 0.113 | 15 | 0.114 | 122 | 0.116 |
| 1 | 4 | 14 | 0.112 | 25 | 0.113 | 202 | 0.115 |
| 1 | 8 | 26 | 0.113 | 45 | 0.113 | 362 | 0.117 |
| 1 | 16 | 50 | 0.113 | 85 | 0.114 | 682 | 0.118 |
| 2 | 2 | 44 | 0.115 | 54 | 0.114 | 434 | 0.117 |
| 2 | 4 | 174 | 0.118 | 150 | 0.115 | 1202 | 0.118 |
| 2 | 8 | 890 | 0.126 | 486 | 0.117 | 3890 | 0.122 |
| 2 | 16 | 5490 | 0.154 | 1734 | 0.119 | 13874 | 0.125 |
| 3 | 2 | 161 | 0.120 | 189 | 0.117 | 1514 | 0.120 |
| 3 | 4 | 1124 | 0.140 | 875 | 0.120 | 7002 | 0.125 |
| 3 | 8 | 10934 | 0.261 | 5103 | 0.126 | 40826 | 0.140 |
| 3 | 16 | 137563 | 7.551 | 34391 | 0.203 | 275130 | 0.335 |
| 4 | 2 | 566 | 0.133 | 647 | 0.122 | 5178 | 0.128 |
| 4 | 4 | 6874 | 0.227 | 4999 | 0.131 | 39994 | 0.146 |
| 4 | 8 | 124658 | 5.552 | 52487 | 0.281 | 419898 | 0.568 |
| 4 | 16 | decline | — | decline | — | decline | — |
| 6 | 2 | 5831 | 0.208 | 6560 | 0.144 | 52482 | 0.165 |
| 6 | 4 | 203124 | 6.734 | 140624 | 0.812 | 1124994 | 1.778 |
| 6 | 8 | decline | — | decline | — | decline | — |
| 6 | 16 | decline | — | decline | — | decline | — |
| 8 | 2 | 59048 | 0.799 | 65609 | 0.397 | 524874 | 0.784 |
| 8 | 4 | decline | — | decline | — | decline | — |
| 8 | 8 | decline | — | decline | — | decline | — |
| 8 | 16 | decline | — | decline | — | decline | — |

Every accepted result hash is `0x1`. The signed arm is slower at every
registered median, so these data establish no crossover: `plain` remains
the default. Declines are separate fixed workloads, outside the complexity
regressions. Their inputs are read from `IO.Ref`s so the compiler cannot
precompute the preflight results. Tree declines measure the six declined grid
points together; product declines measure the six points in both modes.

| Decline workload | Points | Median ms | Result hash |
| --- | ---: | ---: | --- |
| Tree | 6 | 4.190 | `0xb` (true) |
| Products | 12 | 1.912 | `0xb` (true) |

## Operation profiles and provenance

One operation-only profile per computational arm uses grid index 15
(four atoms, degree eight). `perf` timestamps are filtered against lean-bench's
`kernel` regions, excluding preparation and result hashing. All in-region
samples, sidecars, source SHA-256 hashes, and profiling-only benchmark rows
are retained. These samples are attribution evidence, not scientific timing
samples. Unresolved system samples remain in the denominator. Profile JSON
is stored losslessly with gzip compression; the recorded hashes describe the
measured sources, not the archive format.

| Arm | Operation samples | Leading resolved leaf |
| --- | ---: | --- |
| [tree](data/hex-kronecker/runtime-profiles/profile-tree.json.gz) | 281 | `__gmpn_addmul_1_x86_64` (50.9%) |
| [plain](data/hex-kronecker/runtime-profiles/profile-plain.json.gz) | 239 | `__gmpn_copyi_x86_64` (23.0%) |
| [packed](data/hex-kronecker/runtime-profiles/profile-packed.json.gz) | 221 | `__gmpn_addmul_1_x86_64` (26.7%) |

The tree profile is dominated by GMP multiply/add-multiply operations. Product
profiles include power construction, copying, and multiplication, covered by
the two terms of the declared bound. Baseline profiles are retained alongside
the optimized profiles and explain the saturation optimization: repeated
operations on the large cap dominated the earlier implementation.

## Retained computational runs

Each export contains all completed trials for its source state. The linked
profile manifest records full SHA-256 hashes; the table abbreviates the
`Expr.lean`, `Size.lean`, and benchmark-driver hashes to twelve digits.
Comparative conclusions use the latest complete family table above.

| Export | Lean | Expr / Size SHA-256 prefixes | Driver SHA-256 prefix | Source manifest | Change |
| --- | --- | --- | --- | --- | --- |
| [bench-optimized.json](data/hex-kronecker/bench-optimized.json) | 4.34.0-rc2 | `a540414cc86b` / `f47eadccea6e` | `bc480ecd5d66` | [hashes](data/hex-kronecker/profile-tree-optimized.json.gz) | Small-operand exact saturation |
| [bench-direct.json](data/hex-kronecker/bench-direct.json) | 4.34.0-rc2 | `7ee6f4ac5e86` / `757c2e036384` | `bc480ecd5d66` | [hashes](data/hex-kronecker/direct-profiles/profile-tree.json.gz) | Primitive recursors |
| [bench-final.json](data/hex-kronecker/bench-final.json) | 4.34.0-rc2 | `7ee6f4ac5e86` / `eaea75e641d0` | `bc480ecd5d66` | [hashes](data/hex-kronecker/final-profiles/profile-tree.json.gz) | Exact subtree pruning |
| [bench-integrated.json](data/hex-kronecker/bench-integrated.json) | 4.34.0 | `7ee6f4ac5e86` / `eaea75e641d0` | `bc480ecd5d66` | [hashes](data/hex-kronecker/integrated-profiles/profile-tree.json.gz) | Lean 4.34.0 |
| [bench-runtime.json](data/hex-kronecker/bench-runtime.json) | 4.34.0 | `7ee6f4ac5e86` / `eaea75e641d0` | `48c991960c1f` | [hashes](data/hex-kronecker/runtime-profiles/profile-tree.json.gz) | Runtime decline inputs |
