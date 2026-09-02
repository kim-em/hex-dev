# hex-graph-iso: word-packed rows and masks — survey and design

Design for https://github.com/kim-em/hex-dev/issues/9894. Measurement
first; every number below is from this machine (chungus2), compiled
binaries, same-process A/B.

## Proof-surface survey

Theorems whose statements or proofs touch the Nat-bitset operations,
by file (op counts are textual mentions, a proxy for entanglement):

| file | lines | theorems | heaviest ops |
|---|---|---|---|
| CellPerm.lean | 1039 | 37 | elem 61, testBit 11, insert 5, worksetOf 6 |
| CellPermLoop.lean | 1565 | 57 | insert 12, popCount 12, `&&&` 12, testBit 8 |
| Equivariance.lean | 1500 | 84 | image 40, insert 13, worksetOf 11, `&&&` 11 |
| Image.lean | 682 | 30 | testBit 102, image 70, insert 34, `<<<` 15 |
| Refine.lean | 548 | 0 | executable only |
| Bits.lean | 433 | 16 | wave-1 csimp layer |

~224 theorems bind to the Nat representation, but through two narrow
necks: the op-lemma library (Image.lean) and direct
`testBit`/`insert` reasoning about `refine`'s helpers. `Refine.lean`
itself is proof-free; everything proved about refinement unfolds its
helpers from the CellPerm/Equivariance side. `Search.lean` (the
run driver) is conformance-pinned but proof-free.

Consequence: a representation change *at the type level* (rows or
masks stop being `Nat` in the definitions the proofs unfold) re-founds
all four proof files — months, and it would also move the kernel
surface the kdecide ladder pins. Rejected. The representation must be
a runtime-only fact.

## Representation microbenchmark

Per-op cost, deterministic ~half-density masks, same-process A/B, two
passes (stable within noise); `s1` is today's code (Nat `&&&` plus the
wave-1 byte-chunked `popCount`), `s2` walks both operands in 64-bit
chunks without materializing the intersection, `s3` is two 63-bit
small-Nat limbs stored structure-of-arrays (the quoted cost INCLUDES
the four `Array Nat` reads):

| shape | bits | s1 Nat | s2 fused64 | s3 two-limb |
|---|---|---|---|---|
| `popCount (a &&& b)` | 61 | 22ns | 124ns | 25ns |
| `popCount (a &&& b)` | 96 | 438ns | 322ns | **32ns** |
| `popCount (a &&& b)` | 126 | 750ns | 328ns | **32ns** |
| 16-position insert fold | 61 | 575ns | — | 578ns |
| 16-position insert fold | 96 | 3175ns | — | **635ns** |

Two-limb small-Nat limbs win 13-23x on the splitter's flagship op past
the 63-bit small-scalar boundary and 5x on workset construction, at
parity below it. Chunk-walking (`s2`) is not competitive: each chunk
extraction is a GMP shift. `Array UInt64` was not benched because the
Lean runtime boxes `UInt64` array elements (heap object per element);
`Array Nat` of small values is already a tagged-pointer read, which is
why the SoA limb arrays are the right container. `ByteArray` rows were
not benched: reads are per-byte function calls, and the limb layout
strictly dominates for the n ≤ 126 corpus.

Limb generalization: 63-bit limbs, low limb first. For n ≤ 126 both
limbs are small Nats and every op is tag-checked arithmetic with zero
GMP. For n > 126 the high limb becomes a big Nat again and the ops
degrade gracefully (correct, and still cheaper than today because the
low 63 bits stay small); a k-limb flat strided `Array Nat` is the
natural extension if the corpus ever grows past 126 vertices, and
nothing in this design blocks it.

## The seam: csimp on `refine`, nothing else moves

`@[csimp] refine = refineFast`, where `refineFast` converts `ctx.g`
to limb SoA once per call (`ofRowsL`, two `Array.map`s) and runs a
limb twin of the splitter loop. Every caller — the search driver, the
trace-driven translator, and the trusted replay's `checkNode` — picks
up the fast implementation at compile time; the kernel, the kdecide
ladder, and all 224 theorems continue to see the unchanged `refine`.
Per-call conversion is O(n) against the splitter's O(n·cells) work
and measures as noise.

The twin (~140 lines, an afternoon to reproduce from this
section) mirrors `refine`'s helpers with three substitutions: `countsOfL`
(the `popCount (workset &&& row)` map over limb pairs), `worksetOfL`
(limb insert fold), and `splitCellLoopL`/`refineTrivialL` (limb
`elem` on the captured splitter row). `active`, `ptn`, positions, and
codes are untouched (position sets over n bits share the same
representation question, but `active`'s ops run per split, not per
vertex — tier 2, only if a later profile indicts them). The twin also
let-binds the counts list that the original recomputes textually
eight times; the compiler already CSEs those (verified in the
generated C: one `countsOf` call site), so this is cosmetic, and the
zeta-reduced terms are definitionally equal for the proof.

Empirical faithfulness of the twin before any proof: with the csimp
equality `sorry`d, the full fixture stream is byte-identical
(6,000+ cases through `canonicalize`, whose every refinement now runs
the limb path).

## In-situ measurement: the spike does not clear the bar

With the `sorry`d csimp active (fixture stream byte-identical, so the
twin is faithful), quiet machine, same worktree and compiler:

| runColored | limbs csimp ON | OFF (baseline) |
|---|---|---|
| n = 96 (dense pseudo-random) | 863 us | 890 us (**-3%**) |
| n = 64 | 185.4 us | 185.6 us (flat) |
| profile instances (n <= 64) | flat to +4-14% | — |

The microbenchmark's 13-23x on the isolated op is real but does not
surface: the splitter's `popCount (workset &&& row)` is a small
fraction of `runColored` even at n = 96, and the wave-1 ~15% GMP
share is *distributed* across every big-Nat set in the search —
`active`, the orbit and fixed-point sets, `nextElem`'s shifted sets,
`testcanlab`'s row compares, `breakout` — not concentrated where the
csimp seam can reach it. The small-n instances additionally pay the
per-call `ofRowsL` conversion.

## Verdict: PARKED

Per the measurement discipline (measure before proving), the
~600-line `refine = refineFast` proof is not worth paying for a 3%
ceiling. The refine-level csimp seam is parked with this record.
What would change the verdict:

- a corpus shift toward n substantially above 96 (limb count grows,
  the op share grows superlinearly), or
- a decision to move the WHOLE search state (active/orbits/rows) to
  the limb representation, which is the full type migration priced
  above at re-founding four proof files — only conceivable as its own
  campaign with the ~15% aggregate GMP share as the honest ceiling,
- in which case the `refineFast` twin described above and the
  microbenchmark table are the starting points.

The two-limb representation itself remains validated and available:
issue https://github.com/kim-em/hex-dev/issues/9898 (permset/rowOf
transport on the checked path) can reuse wave 1's limb kernels in
Image.lean, which is where the limb approach has already paid.

## Negative results recorded

- The refine-level limb csimp: -3% at n=96, flat at n=64, small
  regression below (per-call conversion) — parked, see above.
- `countsOf`'s eightfold textual recomputation is already CSE'd by
  the compiler; hoisting is worth nothing at runtime.
- 64-bit chunk walking of big Nats (s2) is dominated by two-limb SoA
  everywhere and by the status quo below 63 bits.
- The 63-bit small-Nat boundary tax at exactly n = 64 (one GMP limb)
  is minor at the op level; the measured n=56 -> 64 cactus ratio jump
  in the committed sweep is therefore mostly allocator and List
  machinery, not GMP arithmetic — relevant to issue 9896.
