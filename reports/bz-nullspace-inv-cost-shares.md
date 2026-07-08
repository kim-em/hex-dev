# Berlekamp-Zassenhaus: nullspace and `ZMod64.inv` cost shares (#8647)

This report records the measurement gating
https://github.com/kim-em/hex-dev/issues/8647 ("bench(modarith): measure
nullspace and ZMod64.inv cost shares"), the consolidated reassessment deferred
from the closing comments of
https://github.com/kim-em/hex-dev/issues/8634 (packed nullspace/row-reduction
kernel) and https://github.com/kim-em/hex-dev/issues/8635 (`ZMod64.inv` in word
arithmetic). It reports the remaining cost shares, on current `main`, of the two
generic paths those issues named, and decides which remain material.

## Headline

1. **The generic `Matrix.nullspace` / row-reduction under
   `Berlekamp.fixedSpaceKernel` is now the single largest algorithmic share of
   the `RELIFT_PROFILE=prime` profile: ~15-22%** (folded-stack inclusive ~21%,
   compiled-symbol self-time ~19%), a large relative increase over the earlier
   deg-24 **~8%** baseline. It **grew**: the `ZMod64` arithmetic speedups of
   #8633/#8638 shrank the multiply/add cost and the rest of the denominator, but
   left the *generic boxed* linear-algebra machinery untouched. (The 8% baseline
   was deg-24-only and this figure is an all-degree aggregate, so treat it as
   evidence of a large relative rise, not an exact ratio.) **Material** — a
   targeted implementation issue is filed
   (https://github.com/kim-em/hex-dev/issues/8669).

2. **`ZMod64.inv` (via `HexArith.Int.extGcd`, GMP `lean_hex_mpz_gcdext`) is
   ~3%** (self 3.0%, inclusive 3.2%), and GMP-internal work is negligible
   (`__gmpz_cfdiv_r_2exp` 0.04%). On the small primes BZ actually uses
   (`p = 29` here), the extended-GCD round-trip is cheap. **Not currently
   material in this workload** — recorded and closed, no implementation issue.

3. **The `#8639` gate is both unmet and irrelevant to these two shares.**
   #8639 (Barrett-context / lazy-reduction convolution kernels) is still open;
   its multiply half landed **dormant** with no measured improvement
   (https://github.com/kim-em/hex-dev/pull/8644: the finite-field poly
   workloads are reduction-bound, not multiply-bound). More to the point,
   **neither measured subtree is a call to the #8639 multiply/convolution
   kernels**: row-reduction uses generic per-element `ZMod64` field ops (it does
   multiply, but through the contextless `ZMod64.mul`, not the packed/Barrett
   matrix-multiply surface), and `ZMod64.inv` is `extGcd`. #8639's kernels
   specialize `FpPoly` multiply and `ZMod64` matrix *multiply*; its own text
   notes Barrett "does not help the contextless `ZMod64.mul`". So the
   closing-comment expectation that the generic nullspace would "inherit the
   Barrett/lazy-reduction work of #8639" does not hold, and the measurement is
   valid on current `main` with no need to wait. A future #8639 could still
   shrink the total-profile *denominator* through other `FpPoly` work in the
   same run, but that would make the nullspace share *larger*, not less
   material.

## Instruments

* **`RELIFT_PROFILE=prime` under `perf` — decisive.** This is the instrument
  that isolates both shares: the profile runs `choosePrimeData?` across the
  split degree families (deg 8/12/16/20/24 plus Phi15 and SD4) and a marginal
  `isGoodPrime` at the selected prime. Both shares live in that path -- the
  Berlekamp factorization inside `choosePrimeData?` calls `fixedSpaceKernel`
  (the nullspace) and drives the `c = 0..p-1` constant sweep of
  `DensePoly.gcd` (the divisions whose leading-coefficient inverse is
  `ZMod64.inv`). Two 60k-sample frame-pointer captures (folded, inclusive) plus
  one 60k-sample flat self-time capture; the two arms agree within ~1 point and
  reproduce.
* **`hexpolyfp_bench` — context only.** It measures the `FpPoly` layer
  (`gcd`/`divMod`/`modByMonic`/Frobenius), which is upstream of neither share:
  the nullspace sits in the matrix layer and `inv` in the scalar layer. It
  corroborates that the `FpPoly` reduction cost (`modByMonic` long division) is
  a *separate* concern, tracked in https://github.com/kim-em/hex-dev/issues/8642,
  not part of the two shares this issue measures. (`runGcdChecksum`: deg 256
  gcd 64.3 us/call on this host.)
* **BZ factor sweep with the #8640 before/after cactus overlay — inapplicable.**
  The overlay diffs a sweep recorded on `main` against one on a change branch.
  With #8639 unlanded there is no "after" branch to diff, so the overlay has
  nothing to compare; a single current-`main` sweep would just reproduce the
  committed baseline. The `perf` attribution above is the appropriate instrument
  for a per-component share on a single tree.

## Method

Reproduction (host `chungus2`, `lean=4.32.0-rc1`, commit `d0d94fc`):

```
lake build hex_recursive_relift_spike
# flat self-time
perf record -F 4000 --call-graph dwarf -o prime.data -- \
  bash -c 'for i in $(seq 12); do RELIFT_PROFILE=prime .lake/build/bin/hex_recursive_relift_spike >/dev/null; done'
perf report -i prime.data --stdio --no-children     # bucket symbols by category
# folded inclusive share (frame-pointer stacks)
perf record -F 4000 --call-graph fp -o prime_fp.data -- bash -c '...'
perf script -i prime_fp.data --comm hex_recursive_r  # count samples whose stack contains the symbol
```

The flat self-time is bucketed by compiled-symbol name; the inclusive share is
the fraction of samples whose call stack passes through the subtree's entry
symbol (`fixedSpaceKernel`/`nullspaceMatrix`/`rowReduce`/pivot for the linear
algebra; `lean_hex_mpz_gcdext`/`ZMod64_inv` for the inverse). The manual symbol
buckets are approximate (Lean's generated names, inlining, and trampolines make
per-symbol attribution imprecise), so the inclusive subtree counts are the
primary materiality number and the self-time table is a cross-check. Frame-
pointer stacks average only ~4.4 frames, so subtree membership can miss deep
leaf samples whose ancestor frame was not unwound: treat the inclusive figures
as approximate and likely undercounting, not exact inclusive time. The two
independent fp captures are the reproducibility anchor.

## Numbers

Self-time, `perf report --no-children`, symbols bucketed by category
(60k samples, `RELIFT_PROFILE=prime`, all degrees):

| category | self-time |
|---|---|
| generic nullspace + row-reduction (`nullspaceMatrix`, `rowReduce`, `pivotIndex`, `findPivot`, `eliminateColumn`, `freeCols`, `Matrix.ofFn`/`identity`/`col`) | **19.3%** |
| `lean_apply_1/2` closure trampolines (generic typeclass dispatch) | 26.3% |
| allocator / refcount (`mi_malloc`/`mi_free`, `lean_dec_ref`, `del_core`) | 22.3% |
| `Array.ofFn`/`List.ofFn`/`foldl` higher-order machinery | 11.4% |
| `DensePoly` mod-p ops (`divMod`, Euclid gcd, `subtractScaledShift`) | 7.8% |
| `ZMod64` scalar arithmetic (`add`/`sub`/`mul`/`ofNat`) | 6.3% |
| **`ZMod64.inv` / `extGcd`** (`lean_hex_mpz_gcdext`, `ZMod64.inv`, `instDiv`) | **3.0%** |
| `berlekampMatrix` build | 0.8% |
| other | 2.4% |

The materiality call rests on the **15-22% inclusive** figure, not on the
surrounding buckets. The trampoline / allocator / higher-order buckets
(~60% combined) are generic machinery *driven by* the algorithms above them and
are **shared** between the nullspace and the `DensePoly.gcd` constant sweep, so
they are not additional nullspace-attributable time; they are supporting
evidence that the profile is dominated by boxed/generic overhead, part of which
a monomorphic nullspace kernel removes and part of which belongs to the mod-p
gcd sweep.

Inclusive (folded frame-pointer stacks, two independent captures):

| subtree | capture A | capture B |
|---|---|---|
| `fixedSpaceKernel` / `Matrix.nullspace` | 15.5% | 14.4% |
| linear algebra (nullspace + `rowReduce` + pivots) | 21.7% | 20.9% |
| `ZMod64.inv` / `extGcd` | 3.2% | 3.1% |

`choosePrimeData?` wallclock on this tree (us/call, was 18666 for deg-24 in the
recursive-relift report, pre-#8633): deg 8 358; deg 12 1068; deg 16 2707;
deg 20 5529; deg 24 10792; Phi15 159; SD4 2888; `isGoodPrime@selected` deg-24
216. The profile is time-dominated by deg 20/24, whose matrices are largest, so
the aggregate nullspace share above is at the high end for deg-24 specifically
(the report's ~8% baseline was the deg-24 profile).

## Why the nullspace share grew

The cost is not the field arithmetic. `ZMod64.mul`/`add` are ~6% combined and
already word-fast after #8633 (dead per-multiply bignum allocation removed) and
#8638 (`p < 2^31`, division-free `add`/`sub`/`mul`). What remains is the
*generic boxed* linear-algebra representation:

* `Matrix R n m` carries **boxed `ZMod64`** elements dispatched through the
  `Lean.Grind.Ring R` typeclass, so every element read/write and every
  arithmetic op crosses a `lean_apply_1/2` closure boundary (26% of the
  profile) rather than inlining a `UInt64` op;
* the matrix and each nullspace basis vector are built with
  `Array.ofFn`-of-`Array.ofFn` (11% higher-order machinery) and the whole
  thing allocates and refcounts boxed cells (22% allocator);
* free-column extraction runs through `List`-based `freeColsList` /
  `filterTR_loop`.

The packed-`Array UInt64` kernel of #8634 was already tried and regressed,
because it converted to and from the boxed `Matrix` at its boundary and paid the
same per-multiply bignum allocation that #8633 later removed at the source. Post
#8633 the arithmetic is fixed but the boxed-representation overhead is now the
dominant residue, and it is what a *boundary-free* monomorphic row-reduction
attacks -- one that stays in unboxed `Array UInt64` end to end (matrix build ->
echelon -> nullspace basis -> witness polynomials), with a correspondence
theorem to the generic `nullspace` (plus deterministic output checks) so the
public factorization result is unchanged. That is the direction of
https://github.com/kim-em/hex-dev/issues/8669.

The distinction from #8634 is a hard acceptance criterion, stated negatively:
**no boxed `Matrix R n m` conversion anywhere on the hot path**, before or after
row-reduction. The packed `Array UInt64` representation must flow from the
Berlekamp matrix construction through echelon form, nullspace basis, and witness
polynomial extraction without a pack/unpack boundary. #8634 regressed precisely
because it materialized the boxed `Matrix` at its edges; a re-file of that shape
would regress the same way. The lever is boundary-free monomorphization, not
"packed nullspace."

## Decision

* **Nullspace/row-reduction (~15-22%): material.** Filed
  https://github.com/kim-em/hex-dev/issues/8669.
* **`ZMod64.inv`/`extGcd` (~3%): not currently material in this workload.**
  Recorded here; no issue. The word-arithmetic inverse of #8635 would save a
  fraction of 3% on the small primes BZ uses, below the bar for the proof/FFI
  work it needs.
