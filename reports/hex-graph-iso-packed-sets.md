# HexGraphIso packed vertex sets: before and after

`canonicalize` runs nauty's search tree node for node, so the hex/nauty
wallclock ratio is a per-node constant factor and the only asymptotic
question about the implementation is whether that factor grows with the
vertex count. Before this change it did: the search kept every vertex set
as a `Nat` bitset, unboxed and one machine word below 64 vertices and a
heap-allocated GMP bignum above, so every set operation on a larger graph
paid an allocation and a bignum call. The search now keeps vertex sets as
`Nauty.VSet`, an array of 63-bit limbs (`Array Nat` with every limb below
`2^63`, so each limb stays an unboxed scalar and `&&&`, `|||`, `^^^`,
`>>>` and `testBit` on it never leave the fast path), the same shape as
nauty's `setword` arrays. Every set operation costs `⌈n/63⌉` word
operations, and the `Nat` bitset survives only as the kernel-facing
specification the checker consumes.

Two instruments record the effect, both repeatable from the repository:

- `scripts/bench/graphiso_perf_side_by_side.sh` records one `perf`
  profile of `hexgraphiso_cactus`, which runs `canonicalize` and the
  nauty comparator on the same corpus in one process, and attributes
  the samples to the compiled search, the corpus instance builders, the
  bignum library and allocator, the Lean runtime, and nauty's own C.
- `scripts/bench/graphiso_pernode_fit.py` reads a recorded cactus sweep,
  divides each instance's wallclock by its visited-node count, fits
  `cost per node ~ n^e` per family for hex and for nauty, and prints the
  exponents with the hex/nauty ratio `X` below and above 64 vertices.
  `--check 0.2` is the required CI check that fails when a family with
  at least five sizes has a hex exponent more than `0.2` above nauty's.

## Profile

Whole cactus corpus, `chungus2` (AMD EPYC 9455), 2026-09-05, one
`perf record` at 2 kHz per binary. "Before" is the `main` binary at
`efa5e0c49`, "after" is this branch. Shares are of all samples in the
process, so hex and nauty are measured under identical conditions.

| category | before | after |
|---|---|---|
| hex-search (`Hex.GraphIso.Nauty.*`, including `VSet` and `Bits`) | 6.6% | 14.6% |
| hex-instances (corpus builders: `Families`, `Random`, `Graph.ofRel`) | 28.7% | 56.3% |
| hex-other (other compiled Lean) | 3.5% | 5.3% |
| GMP+allocator (`__gmp*`, `lean_nat_big_*`, `malloc`/`free`, mimalloc) | 52.7% | 8.4% |
| Lean-runtime | 6.9% | 13.6% |
| nauty-C | 0.7% | 1.4% |

The bignum and allocator share falls from over half of the run to under a
tenth, and no `lean_nat_big_*` symbol remains in the top twenty. What is
left above the search itself is the corpus: `Families.choose`, evaluated
inside the lazy adjacency functions the driver hands to `canonicalize`,
is the single largest symbol in both profiles (27% before, 53% after)
and is instance construction, not search. The remaining GMP samples are
the `Nat` row conversion at the boundary with the kernel-facing checker,
which is outside the search loop.

The instance-builder share is a separate finding: the corpus's Kneser
and Johnson graphs computed their binomial coefficients by the Pascal
recurrence inside the lazy adjacency functions, which made
`Families.choose` the largest symbol in both profiles. With the
multiplicative formula the same binary profiles as follows.

| category | after, multiplicative binomials |
|---|---|
| hex-search | 29.2% |
| hex-instances | 7.0% |
| hex-other | 13.1% |
| GMP+allocator | 17.6% |
| Lean-runtime | 29.1% |
| nauty-C | 3.2% |

The search is now the largest compiled category, and what remains of the
bignum share is the `Nat` row conversion at the checker boundary plus the
allocator traffic of the limb arrays themselves.

## Per-node cost

Fits of `cost per node ~ n^e` from the two sweeps, before
(`hexgraphiso-cactus-04f38e84f6e2-chungus2.jsonl`, the last sweep on
`main`) and after (`hexgraphiso-cactus-17852d9b9995-chungus2.jsonl`).
`diff` is the hex exponent minus nauty's; the CI margin is `0.2`.

| family | sizes | hex n^e before | hex n^e after | nauty n^e | diff before | diff after |
|---|---|---|---|---|---|---|
| circulant-12 | 17 | 2.15 | 1.74 | 1.84 | 0.32 | -0.10 |
| circulant-1248 | 12 | 2.41 | 1.79 | 1.87 | 0.56 | -0.08 |
| grid | 10 | 2.23 | 1.69 | 1.88 | 0.35 | -0.19 |
| hypercube | 5 | 1.69 | 1.36 | 1.41 | 0.29 | -0.05 |
| johnson | 10 | 1.66 | 0.99 | 1.05 | 0.61 | -0.06 |
| kneser | 10 | 2.02 | 1.33 | 1.32 | 0.70 | 0.01 |
| latin | 3 | 2.69 | 1.82 | 1.92 | 0.76 | -0.10 |
| paley | 13 | 2.51 | 1.74 | 1.83 | 0.72 | -0.10 |
| random | 18 | 2.57 | 1.88 | 1.91 | 0.68 | -0.03 |

Before the change every family with at least five sizes failed the
margin; after it every family passes, and the hex exponent is at or
below nauty's on all nine. The hex/nauty ratio `X` (geometric mean of
per-instance wallclock ratios):

| slice | X before | X after |
|---|---|---|
| n ≤ 64 | 5.67 | 7.72 |
| n > 64 | 18.57 | 7.12 |

`X` is now flat in `n`, which is what "same algorithm, constant per-node
factor" predicts. The two slices moved in opposite directions. Above 64
vertices the packed sets remove the bignum path and the corpus
canonicalizes 2.6 times faster (geometric mean over instances; Kneser
22-2 goes from 209 ms to 39 ms, Paley 229 from 29 ms to 6.8 ms). Below
64 vertices a `Nat` bitset was a single unboxed scalar and every set
operation was one machine instruction, whereas a one-limb `VSet` is a
heap-allocated array whose operations allocate their result, and the
small instances run 0.74 times as fast as before (0.65 to 0.89 across
the slice; grid 5×5 goes from 0.066 ms to 0.084 ms). That is the price
of one representation for every size, and it is the honest reading of
the per-size table in the manual's Performance section. Whole-corpus
`canonicalize` time falls from 0.87 s to 0.24 s.

The `checked_ns` column is absent from both sweeps: the certificate tier
collapsed onto the fast surface before this change, so the comparison is
of `canonicalize` alone. The tactic tier is unaffected: the kernel-facing
checker keeps `Nat` rows, converted from the packed rows at the boundary
by `VSet.toNat` with the correspondence proofs in `NodeLit.lean`.
