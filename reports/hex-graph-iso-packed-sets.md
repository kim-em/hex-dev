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
nauty's `setword` arrays. Every set operation is a loop over the
`⌈n/63⌉` limbs (the binary operations allocate one result array, which
nauty's in-place C does not), and the `Nat` bitset survives only as the
kernel-facing specification the checker consumes.

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

The instance-builder share is a separate finding, and it was
asymmetric: `canonicalize` received the corpus's lazy adjacency
functions and evaluated them inside its timed region, whereas nauty
received adjacency strings built before its timer started, and the
Kneser and Johnson generators computed their binomial coefficients by
the Pascal recurrence on every adjacency query. The driver now
materializes each instance's adjacency once and hands both columns a
cheap lookup, and `Families.choose` is multiplicative; the binary then
profiles as follows, with the search the largest compiled category.

| category | after, adjacency materialized |
|---|---|
| hex-search | 29.4% |
| hex-instances | 7.5% |
| hex-other | 12.5% |
| GMP+allocator | 18.0% |
| Lean-runtime | 29.1% |
| nauty-C | 2.9% |

What remains of the bignum share is the `Nat` row conversion at the
checker boundary plus the allocator traffic of the limb arrays
themselves; the instance share is the one-time construction at startup,
outside every timed region.

## Per-node cost

Fits of `cost per node ~ n^e` from the two sweeps, before
(`hexgraphiso-cactus-d78dade3633a-chungus2.jsonl`, the last sweep on
`main`) and after (`hexgraphiso-cactus-ac1dfad4a453-chungus2.jsonl`).
`diff` is the hex exponent minus nauty's; the CI margin is `0.2`.

| family | sizes | hex n^e before | hex n^e after | nauty n^e | diff before | diff after |
|---|---|---|---|---|---|---|
| circulant-12 | 17 | 2.14 | 1.75 | 1.83 | 0.32 | -0.08 |
| circulant-1248 | 12 | 2.41 | 1.80 | 1.88 | 0.54 | -0.08 |
| grid | 10 | 2.23 | 1.69 | 1.87 | 0.38 | -0.18 |
| hypercube | 5 | 1.70 | 1.36 | 1.41 | 0.29 | -0.05 |
| johnson | 10 | 1.67 | 1.00 | 1.05 | 0.62 | -0.06 |
| kneser | 10 | 2.02 | 1.32 | 1.33 | 0.69 | -0.00 |
| latin | 3 | 2.68 | 1.83 | 1.92 | 0.78 | -0.09 |
| paley | 13 | 2.51 | 1.73 | 1.84 | 0.69 | -0.10 |
| random | 18 | 2.57 | 1.88 | 1.91 | 0.68 | -0.03 |

Before the change every family with at least five sizes failed the
margin; after it every family passes, and the hex exponent is at or
below nauty's on all nine. The hex/nauty ratio `X` (geometric mean of
per-instance wallclock ratios):

| slice | X before | X after |
|---|---|---|
| n ≤ 64 | 5.75 | 7.67 |
| n > 64 | 18.85 | 7.08 |

`X` is now flat in `n`, which is what "same algorithm, constant per-node
factor" predicts. The two slices moved in opposite directions. Above 64
vertices the packed sets remove the bignum path and the corpus
canonicalizes 2.6 times faster (geometric mean over instances; Kneser
22-2 goes from 211 ms to 38 ms, Paley 229 from 29 ms to 6.7 ms).
The materialized adjacency moves neither slice measurably: the sweep
recorded with the lazy generators still inside the timed region gave
the same exponents and `X` of 7.7 and 7.1. Up to
63 vertices a `Nat` bitset was a single unboxed scalar and every set
operation was one machine instruction, whereas a one-limb `VSet` is a
heap-allocated array whose binary operations allocate their result, and
the small instances run 0.74 times as fast as before (0.66 to 0.91
across the slice; grid 5×5 goes from 0.066 ms to 0.084 ms). That is the price
of one representation for every size, and it is the honest reading of
the per-size table in the manual's Performance section. Whole-corpus
`canonicalize` time falls from 0.87 s to 0.24 s.

The `checked_ns` column is absent from both sweeps: the certificate tier
collapsed onto the fast surface before this change, so the comparison is
of `canonicalize` alone. The tactic tier is unchanged within noise (curve
shift 1.03x): the kernel-facing checker keeps `Nat` rows, converted from
the packed rows at the boundary by `VSet.toNat` with the correspondence
proofs in `NodeLit.lean`, and its packed-state clone in `NodePacked.lean`
is proven equal to that list tower.
