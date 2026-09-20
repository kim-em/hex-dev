# HexRank performance

HexRank remains at `done_through: 3`. Registration checks are not scientific
performance verdicts. The outstanding compiled evidence is owned by
[#10352](https://github.com/kim-em/hex-dev/issues/10352).

## Bench targets

Build and inspect from the repository root:

```sh
lake build hexrank_bench
lake exe hexrank_bench list
lake exe hexrank_bench verify
```

The executable is Mathlib-free. Existing CI ownership selects `hexrank_bench`
for `HexRank`; no additional workflow, job or matrix is needed.

| Public surface | Evidence track and measured path |
| --- | --- |
| `rowReduceWith`, `rowReduceFF` | Compiled first pass: `runRowReduce*` on integer families and `run{RatPoly,Mv}Rank*` on polynomial families. |
| `rankWith`, `rankProfileWith`, `rank`, `rankProfile` | Compiled projections of that same first pass, not independent algorithms. The targets return the computed rank. |
| `rankCertWith`, `rankCert`, `rankCertOf` | Compiled certificate production: `runRankCert*` and `run{RatPoly,Mv}Cert*`; includes the first pass and the second pass on the augmented pivot block. Separate attribution of `rankCertOf` remains to be established by profiling. |
| `checkRank` | Compiled checker: `runCheckRank*` and `run{RatPoly,Mv}Check*`; certificates are prepared outside timing. |
| `certifyRankWith`, `certifyRank` | Compiled certificate production followed by checking. An end-to-end registration remains necessary. |
| `rankWitness`, polynomial quotient witness production | Native certificate construction used by the companion's tactics. The fresh-module probes include this work, but do not establish a separate compiled performance verdict. Compiled coverage remains to be audited. |
| `checkRankList`, `checkRankListPacked`, `checkRankPoly` in kernel replay; tactic elaboration and proof construction | Proof track in HexRankMathlib. Reuse the companion's fresh-module evidence; no Mathlib import into this executable. |
| Soundness, completeness, rank correspondence, profile theorems | Mathematical API, not executable timing targets. The existing companion bridge is unchanged. |

The integer registrations currently declare `n * n` for fixed low rank and
`hadamardBound n` for dense and variable-rank deficient inputs. Their existing
schedules end at 64 or 128. Neither the full scientific range nor the strongest
applicable mode has yet been established. In particular, the dense generator
is a product of unit triangular matrices: factor entries are bounded by 5,
while product entries are bounded by `25n`, not 8. Its leading principal
minors are all 1. Deficient generators contain identity pivot blocks. A
generic worst-case Hadamard bound alone does not justify mode 2 on these
structured families under the ordered-mode rule.

Polynomial names have the form
`Hex.RankBench.run{RatPoly,Mv}{Deficient,}{Rank,Cert,Check}{4,8,12}`.
`Rank` times `rowReduceWith`'s first pass, `Cert` times `rankCertWith`, and
`Check` times `checkRank`. Existing names are preserved. Inputs retain the
original generators: `smallEntry` uses the documented 64-bit LCG; rational
coefficients use salts 13 and 17, multivariate coefficients use 19 and 23.
Deficient inputs use the products and index offsets in the driver. Expected
ranks are `n` and `n / 2`, respectively.

A per-child `IO.Ref` cache stores the actual matrix and its certificate.
`warmupFirstIter := true` prepares and validates them before timed calls.
Preparation checks both the expected rank and `checkRank`; a mismatch throws
an error. Timed calls read this cache. The checker does not reconstruct its
certificate; the producer targets do recompute their respective operation.
The cache lookup is included in timing. Fixed registrations check the expected
hash of the rank or `true`, in addition to repeat agreement.

## Verdicts

No Phase-4 scientific verdict is claimed. Polynomial support is intended for
mode 3: dimensions alone do not give a tight wall-time model for polynomial
minor support and coefficient growth. The thirty-second `maxSecondsPerCall` is
an operational child timeout, **not** an operation-specific performance
budget. SymPy-derived budgets and measurements against them remain required.

[Registration artifacts](bench-results/hex-rank-10352/) contain the original
29-case list/verify and the 54-case polynomial coverage list/verify.
[Metadata](bench-results/hex-rank-10352/metadata.json) records the base revision,
source hash, toolchain, host, CPU, affinity and load. Commands were the three
commands above (the executable was invoked directly after building).
These checks validate wiring and prepared polynomial ranks, not scaling.

The retained [baseline diagnostic](bench-results/hex-rank-10352/baseline-poly-cert8.txt)
was `hexrank_bench run Hex.RankBench.runRatPolyCert8 --repeats 2` on the
base-revision driver, with default affinity. It is not a scientific comparison
or a budget source. Generated C at that revision places `ratPolyMatrix` and
`rankCertWith` inside `runRatPolyCertAt`; the corresponding checker also
constructs its certificate inside the callable despite its former prep comment.
The runtime cache makes the intended preparation boundary explicit.

The retained [timing-boundary check](bench-results/hex-rank-10352/poly-timing-boundary.json)
ran `runRatPolyCheck8`, `runMvCheck12`, and `runMvCert12` with five repeats
under automatic CPU placement and the original six-second child cap. The
rational checker completed all repeats; the multivariate checker completed
three and hit the cap twice; certificate production hit the cap in every
repeat. The cap includes preparation and the untimed warmup, so this is a
registration-budget failure, not a polynomial complexity verdict. The child
cap is thirty seconds to accommodate preparation plus timed production at 12;
no operation-specific scientific budget has been relaxed. All completed
samples and killed children remain in the artifact.

The [30-second-cap check](bench-results/hex-rank-10352/poly-timing-boundary-30s.json)
completed all five repeats of each case with matching expected hashes:

| Case | Median per call |
| --- | ---: |
| `runRatPolyCheck8` | 8.618 ms |
| `runMvCheck12` | 450.116 ms |
| `runMvCert12` | 6.895 s |

Its [command record](bench-results/hex-rank-10352/poly-timing-boundary-30s-command.json)
contains automatic CPU placement and the driver source hash. These establish
that the fixed cases run through the intended timing boundary; they do not
establish the missing comparator-derived budgets or an asymptotic verdict.

## Comparator ratios

Not measured. All three SPEC comparators remain informational and need
persistent-subprocess registrations: FLINT `fmpz_mat.rank`, FLINT
`fmpq_mat.rank`, and SymPy `DomainMatrix.rank` on exact polynomial domains.
Full shared-input curves, output agreement, protocol overhead, eligible
ranges, versions, and polynomial operation budgets remain required. The
conformance oracle is a correctness reference, not performance evidence.

## Profile

No compiled timed-region profile is claimed. Representative profiles of all
four manifest families and attribution to separately measured operations
remain required. Scientific runs must use automatic CPU placement, the fixed
trial-major schedule, and retain every completed sample.

Kernel/proof evidence has a different measurement contract. The existing
[carrier proof report](hex-rank-carriers-performance.md) and the companion's
`bench/HexRankMathlib/ProofProbe` inputs remain the owners of tactic and kernel
construction/replay measurements. Their times are not compiled rank verdicts.

## Concerns

- [#10352](https://github.com/kim-em/hex-dev/issues/10352): complete the integer generator/model audit, scientific schedules, remaining public-operation coverage, comparator curves and polynomial budgets, timed-region profiles and attribution before claiming Phase 4.
