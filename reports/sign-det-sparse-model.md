# Repeated-query sign-determination costs

The registrations in `bench/HexSignDet/Bench.lean` use mode 1 (two-sided
parametric), with six fixed trial-major repetitions at
`s = 64,128,256,512,1024,2048`. The head is `X²−1`, the interval is the whole
line and every query is `X`. This family exercises many unrealized conditions:
only the all-negative and all-positive words occur, each once. It does not
cover maximal realized support, increasing head/query degree, growing
coefficient or witness bits, extension depth or nested coefficient evidence.

Every singleton leaf has the three fixed columns. At an internal node the two
child supports each have size two, so the Cartesian candidate has four
columns and exactly two positive counts. The first independent rows are the
constant row and an odd row; recursively each retained nonconstant row has
one nonzero exponent. Each parent moment consequently has at most two
nonzero exponents. The actual certificate inventory checks these bounds.
All polynomial arithmetic operands and rational/integer matrix entries have
bounded sizes in this family. Positional indices grow with `s`, but the
registered range fits ordinary machine-word natural numbers.

A node on a query sublist of length `k` scans or copies `Θ(k)` query,
exponent and sign slots. `QueryReduction.checkFrom` and the factor builder
walk corresponding lists together; they do not repeatedly index a linked
list. Candidate matrices have at most four rows and columns, and their
entries evaluate sign words of length `k`. Matrix solving/rank work has
bounded dimensions. Initial preprocessing, child slices and moment
construction also cost `O(k)` here. The balanced tree has `2s−1` nodes and
`log₂s+1` levels, each with query-arity sum `s`. Its arity volume is exactly
`s(log₂s+1)`. Thus production and full tree replay have family-specific
`Θ(s log s)` cost; `runProduce`, `runDirect` and `runTree` register
`s(log₂s+1)`.

The query kernels contribute an additional linear term: there are three
moment slots at each leaf and four at every internal node, giving `7s−4`
slots. This term can dominate at finite sizes even though the slot-processing
term is asymptotically larger. The harness verdict and eventual profile must
be reported without turning this family into evidence for all BKR costs.

The graph fixture retains one actual node per arity on the left branch and
uses two references to the preceding node at every internal entry. For this
family, both child query blocks are literally equal. The graph checker
validates both references and all operand bindings, so construction of the
fixture alone is not taken as evidence. The graph has `log₂s+1` entries,
`2log₂s` edges and total arity `2s−1`. It checks each local node once and
reuses accepted child values and proofs. `runGraph` therefore registers the
family-specific model `s`. Input preparation and full certificate hashing
are outside the timed operation; the timed production result hash includes
the two complete retained sign words and counts and costs `O(s)`.

`inspect` checks both producer modes against the known complete table and
validates tree and graph replay. It records actual dimensions, moment slots,
arity volumes, exponent sums and stored remainder-coefficient sizes. These
observations are structural validation, not performance measurements or
proofs of root semantics. The measurement runner retains the source hashes,
binary hash, host/CPU context, commands and all raw LeanBench samples. It
requires the exact six-trial schedule and checks every result hash against
the known complete table or successful replay. Missing, duplicate or failed
samples invalidate the measurement; their logs remain retained. Inconclusive
complexity verdicts remain recorded and make the runner exit unsuccessfully,
without discarding their samples or automatically repeating the run. The runner
selects a CPU by an automatic nonblocking lease; it performs no quiet-core
preflight and does not reject samples based on host activity. An inconclusive
measurement permits at most one unchanged rerun, retaining both runs.

## Retained measurements

The [raw exports and provenance](data/sign-det-sparse/2327cca21/metadata.json)
record source `2327cca216bf94d8b54d7f2ad561ab04d361366f`, a clean worktree,
LeanBench `8a37daf1074c3bdbd0da479b55538bad4a0022db`, and shared host
`chungus2`, CPU 50. All 144 timed samples completed, matched the known
output hashes, and passed the exact schedule check. No samples were removed
and no rerun was used. The four mode-1 verdicts are **consistent with
declared complexity**.

| Registration | Declared model | Median at s=64 | Median at s=2048 | Normalized slope |
| --- | --- | ---: | ---: | ---: |
| `runProduce` | `s * (Nat.log2 s + 1)` | 13.251 ms | 508.593 ms | -0.093729 |
| `runDirect` | `s * (Nat.log2 s + 1)` | 14.290 ms | 547.933 ms | -0.092278 |
| `runTree` | `s * (Nat.log2 s + 1)` | 7.580 ms | 291.376 ms | -0.093734 |
| `runGraph` | `s` | 0.812 ms | 20.035 ms | -0.023883 |

The slight negative normalized slopes for tree operations are consistent
with the independently identified linear query-kernel term remaining
substantial over this range; the profile below finds substantial query checking
and construction work. These are
separate complexity schedules, not adjacent AB/BA comparisons; the table
does not establish a comparative speedup. Timings are host-specific.

Exports retain whole-child peak RSS, which includes preparation and is not
operation allocation. `alloc_bytes` is unavailable (`null`), so the allocation
gate remains open. Stored remainder bits are not peak intermediate witness
bits, and graph node/edge counts are not serialized certificate bytes.
Additional input axes, paired solver/reduction comparisons,
and fresh-module proof checking remain required. The complete performance
contract remains [the library specification](../HexSignDet/SPEC/hex-sign-det.md);
this family does not establish full Phase-4 completion.

## Sparse-support profile

The [profile summary](data/sign-det-sparse/profile-b8166e5f1/sparse-support.summary.json)
and [manifest](data/sign-det-sparse/profile-b8166e5f1/sparse-support.manifest.json)
retain the commands, tool revisions, binary hash, diagnostics and local raw
artifact hashes. Source `b8166e5f1` adds the runner and observations without
changing the measured binary. The case is `runProduce`, `s=2048`, on shared
host `chungus2`, automatically leased CPU 72, at 999 Hz with a five-second
target. Only the benchmark thread's timed regions are included; fixture
preparation and process startup are excluded. Raw profiles remain local.

Leaf self-time is 37.36% allocation/free, 21.34% GMP, 28.02% Lean runtime,
5.81% Lean own code, and 7.47% other. The classifier accounts for 92.53%;
0.64% of leaves have unresolved symbols. This is allocation **time**, not
allocated-byte evidence.

| Inclusive function | Share |
| --- | ---: |
| `SignDet.buildPrepared` | 95.45% |
| `SignDet.Replay.check` | 56.74% |
| `SignDet.buildTreeFrom` | 38.91% |
| `SignDet.checkMoment` | 35.00% |
| `TarskiCertificate.check` | 27.93% |
| `SignDet.momentMatrix` | 17.83% |
| `Sturm.certifyPrepared` | 14.56% |
| `SignDet.solveSystem` | 6.56% |
| `Sturm.orderSign` | 0.66% |

Inclusive percentages overlap and must not be summed. Production includes
its final literal replay, which accounts for more than half of the samples;
`runTree` independently measures that operation. Query construction and
checking consume substantial time even for the fixed quadratic head.
Moment-matrix entries still scan long sign/exponent words despite the maximum
matrix dimension being four. Rational scalar normalization, allocation and
GMP operations dominate leaf time; the rational coefficient sign callback
itself is cheap here. These findings call for separate query, product and
matrix phase registrations, as the SPEC requires, and do not cover expensive
extension-coefficient sign work.

Filter diagnostics: **4.534347 s** total timed duration,
**4,526 retained samples**, calibration residual
**0.851 ms** (limit 5 ms), no off-thread samples in the selected windows,
and **passed** confidence and boundary-shift sensitivity checks. No profile
rerun was used.
