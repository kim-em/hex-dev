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
[the raw export](data/hex-kronecker/bench-integrated.json). Environment, result hashes,
RSS, inner repeats, and every individual duration are included. The
[run log](data/hex-kronecker/bench-integrated.log) records the selected CPU; the
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
| `runTree` | inconclusive | -6.493 | within bound, observed faster |
| `runPlain` | inconclusive | -5.617 | within bound, observed faster |
| `runPacked` | inconclusive | -8.601 | within bound, observed faster |

## Complete grid

`N` is the structural signed packed-bit bound; signed packing includes its
outer products. The [metadata](data/hex-kronecker/grid.jsonl) also records
`D`, digit width, inner size, outer slot width, operation count, and result
hash for each point. Times below are medians in milliseconds.

| Atoms | Degree | Tree N | Tree ms | Plain N | Plain ms | Signed N | Signed ms |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 8 | 0.114 | 15 | 0.114 | 122 | 0.116 |
| 1 | 4 | 14 | 0.114 | 25 | 0.115 | 202 | 0.115 |
| 1 | 8 | 26 | 0.114 | 45 | 0.115 | 362 | 0.117 |
| 1 | 16 | 50 | 0.120 | 85 | 0.116 | 682 | 0.118 |
| 2 | 2 | 44 | 0.116 | 54 | 0.116 | 434 | 0.118 |
| 2 | 4 | 174 | 0.119 | 150 | 0.118 | 1202 | 0.120 |
| 2 | 8 | 890 | 0.127 | 486 | 0.119 | 3890 | 0.122 |
| 2 | 16 | 5490 | 0.157 | 1734 | 0.121 | 13874 | 0.127 |
| 3 | 2 | 161 | 0.122 | 189 | 0.119 | 1514 | 0.121 |
| 3 | 4 | 1124 | 0.141 | 875 | 0.122 | 7002 | 0.126 |
| 3 | 8 | 10934 | 0.265 | 5103 | 0.129 | 40826 | 0.141 |
| 3 | 16 | 137563 | 7.682 | 34391 | 0.206 | 275130 | 0.336 |
| 4 | 2 | 566 | 0.135 | 647 | 0.124 | 5178 | 0.128 |
| 4 | 4 | 6874 | 0.230 | 4999 | 0.134 | 39994 | 0.147 |
| 4 | 8 | 124658 | 5.628 | 52487 | 0.285 | 419898 | 0.580 |
| 4 | 16 | decline | — | decline | — | decline | — |
| 6 | 2 | 5831 | 0.209 | 6560 | 0.148 | 52482 | 0.166 |
| 6 | 4 | 203124 | 6.829 | 140624 | 0.825 | 1124994 | 1.849 |
| 6 | 8 | decline | — | decline | — | decline | — |
| 6 | 16 | decline | — | decline | — | decline | — |
| 8 | 2 | 59048 | 0.825 | 65609 | 0.406 | 524874 | 0.823 |
| 8 | 4 | decline | — | decline | — | decline | — |
| 8 | 8 | decline | — | decline | — | decline | — |
| 8 | 16 | decline | — | decline | — | decline | — |

Every accepted result hash is `0x1`. The signed arm is slower at every
registered median, so these data establish no crossover: `plain` remains
the default. Declines are separate fixed protocol anchors, not complexity
evidence. Their constant Boolean result can be folded by the compiler;
the conformance checks and guarded proof probes verify the actual preflight
behavior, including rejection before packing.

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
| [tree](data/hex-kronecker/integrated-profiles/profile-tree.json.gz) | 289 | `__gmpn_addmul_1_x86_64` (43.6%) |
| [plain](data/hex-kronecker/integrated-profiles/profile-plain.json.gz) | 237 | `__gmpn_copyi_x86_64` (23.2%) |
| [packed](data/hex-kronecker/integrated-profiles/profile-packed.json.gz) | 218 | `__gmpn_addmul_1_x86_64` (32.6%) |

The tree profile is dominated by GMP multiply/add-multiply operations. Product
profiles include power construction, copying, and multiplication, covered by
the two terms of the declared bound. Baseline profiles are retained alongside
the optimized profiles and explain the saturation optimization: repeated
operations on the large cap dominated the earlier implementation.
