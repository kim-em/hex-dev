# hex-matrix (foundation, no dependencies)

Dense matrices over a coefficient type `R`.

**Contents:**
- `Matrix R n m`, an encapsulated dense matrix type. Consumers go through
  its API — `ofFn`, `ofRows`, `castRows`, `getRow`, `rows`, and entry access
  `M[(i, j)]` (the normal form for entries) — so the backing representation
  stays private and can change.
- Matrix-vector multiplication, matrix-matrix multiplication
- Dot product, norm squared (for `R = Int` and `R = Rat`)
- Row operations (swap, scale, add multiple of one row to another) and the
  corresponding column operations
- Rectangular leading-diagonal construction `diagMatrix`
- Submatrix / leading-submatrix slicing and the Gram matrix
- Generic over the coefficient type `R`

**Backing representation (required): flat row-major `Vector R (n * m)`.**
The opaque one-field structure wraps a single contiguous buffer holding the
`n * m` entries in row-major order: entry `(i, j)` lives at flat index
`i * m + j`, and row `i` occupies the contiguous span
`data[i*m .. i*m + m)`. The layout-order decision (row-major `n * m` versus
column-major `m * n`) was settled by the two deciding workloads:

- *Elementary row operations dominate the elimination stack.* `rowSwap`,
  `rowScale`, `rowAdd`, `modifyRow`, and the `mapRowsIdx`-based column
  scatters each touch the `m` entries of one row, and the elimination
  consumers (`hex-row-reduce`, `hex-bareiss`, `hex-lll`) issue `O(n²)` such
  calls per run; `getRow` is the most-used accessor family-wide. Row-major
  makes every one of these a contiguous span of the single buffer, updated
  in place when the buffer is uniquely referenced. Column-major would
  stride them all.
- *`mulImpl`'s transpose step survives.* Under row-major the columns of the
  right operand are non-contiguous (stride `m`), which is exactly why
  `mulImpl` transposes once up front; the step is retained unchanged, a
  one-time `O(m·k)` pass amortized against the `O(n·m·k)` product.
  Column-major would let the right operand skip that transpose, but at the
  cost of striding the far more numerous row-op workload — the wrong trade.
- *Strassen block strides fall out naturally.* A quadrant sub-block of the
  row-major buffer is an offset-and-stride window (row offset `r0`, column
  offset `c0`, row stride `m`; entry `(i, j)` of the view at
  `backing[(r0 + i) * m + (c0 + j)]`), the view type the copy-free Strassen
  schedule needs (see "Avoiding sub-block copies").

**Entry vs row access.** `M[(i, j)]` is the O(1) entry accessor and the normal
form for single entries — one flat read at `i * m + j`. Row access `M[i]` is
deliberately `noncomputable`: it exists only so proofs may speak of whole rows,
while compiled code reads rows through the computable `getRow` (one contiguous
copy of the row span) and entries through `M[(i, j)]`. Any compiled definition
that reaches for `M[i]` fails to compile, so the flat backing never silently
pays a per-entry row-materialization cost. `rows` materializes all rows and is
the (O(n·m)) observation the row-level lemma layer is stated against, not a
compiled hot-path accessor.

This is the dense base of the matrix family. The row-reduction stack
(`hex-row-reduce`), the Leibniz determinant theory (`hex-determinant`), and the
executable Bareiss algorithm (`hex-bareiss`) build on it.

**Elementary operations.** `rowSwap`, `rowScale`, `rowAdd`, `rowMoveUp`, and the
column analogues `colAdd` / `colAddRight` are pure data transforms on the dense
representation. Their algebraic identities (involutivity of `rowSwap`,
multiplicative behaviour `rowSwap_mul` / `rowScale_mul` / `rowAdd_mul`, and the
inverse-preservation lemmas) live here and are reused by row reduction and by
the determinant row-operation laws. They update the matrix in place when it is
uniquely referenced: each uses its argument linearly and writes the affected
row spans of the single flat buffer through `Vector.set` / `Vector.swap`
loops (`writeRow` and the `swap` column loop), which reuse the backing store
rather than copying it.

**Indexed row/column mutation.** `modifyRow` updates one row span in place;
`setCol` and the per-entry `modifyCol` update one column entry per row through
flat per-entry folds over the single buffer. The column *analogues* of the
elementary operations (`colAdd`, `colAddRight`, `colSwap`) run the same flat
per-entry column engine: each reads the source column(s) once into a borrowed
`O(n)` vector, then writes the destination column entries in place through
`modifyCol` (`colAdd`/`colAddRight`) or two `setCol` passes (`colSwap`) — one
single-entry flat-buffer write per row, reusing the backing store when the
matrix is uniquely referenced, with no row materialization. This replaced the
former `mapRows` form, which materialized every row and reflattened, and the
former `ofFn`-rebuild form of `setCol`, which read and reallocated every entry
to change one column.

**Key properties:**
- identity matrices act as left and right multiplicative identities
- row-vector multiplication associates with matrix multiplication, and its
  action on `diagMatrix` is characterized entrywise
- `transpose` is involutive
- `gramMatrix M = M * Mᵀ`
- elementary-operation multiplicative and inverse-preservation lemmas
- `smul_mul : (c • A) * B = c • (A * B)`, with `row_smul` underneath it

The executable operations remain in `Elementary.lean`; the reusable algebraic
surface is grouped in `ElementaryAlgebra.lean`. It includes multiplication
transport for row and column operations, the explicit inverse-preservation
lemmas used by certificate-producing elimination, and
`transpose_colAdd`. `Matrix` and `DensePoly` structural Boolean equality are
lawful whenever entry equality is lawful, so certificate checkers may use
matrix `BEq` without a separate soundness assumption.

The determinant of a row operation (`det_rowSwap`, `det_rowScale`,
`det_rowAdd`) is stated in `hex-determinant`, where `det` is defined.

## Strassen-Winograd multiplication

The naive product `mul` does `n^3` coefficient multiplications for an
`n × n` product. Strassen's algorithm (V. Strassen, "Gaussian elimination is
not optimal", Numerische Mathematik 13, 1969) computes a 2×2 block product
with **seven** recursive block multiplications instead of eight, which gives
`Θ(n^{log₂ 7}) = Θ(n^{2.807…})`. Winograd's schedule for the same seven
products uses **fifteen** block additions and subtractions against Strassen's
eighteen. Fifteen is optimal for a seven-multiplication 2×2 scheme without a
change of basis (Probert's lower bound). An alternative-basis scheme reaches
twelve (Karstadt and Schwartz, "Matrix multiplication, a little faster", 2017),
which `hex-matrix` does not use. `hex-matrix` specifies the Winograd schedule
under the name `mulStrassen`.

The matrix coefficients used across the project are `Int`, `Rat`, `ZMod64`,
and the `Fp` finite-field types. All are exact, so the Strassen identity holds
exactly and there is no numerical-stability cost: the only question is the
crossover size below which the naive product is faster. For exact integer and
rational coefficients a coefficient multiplication (a multi-limb GMP multiply)
costs much more than a coefficient addition, so the crossover is lower than the
floating-point figures quoted in the numerical-analysis literature.

### Coefficient-ring requirement

`mul` runs for any `R` with `[Mul R] [Add R] [OfNat R 0]`. Winograd's schedule
subtracts blocks, so the executable `mulStrassen` needs subtraction on `R`,
stated as the extra operation `[Sub R]`. The *correctness proof* needs more than
the bare operations: it uses additive associativity and commutativity,
distributivity, and the identity `a - b = a + (-b)`. Those laws come from the
project's ring class `Lean.Grind.Ring R` (the class `mul_assoc`, `identity_mul`,
and the other laws in `HexMatrix/MatrixAlgebra.lean` are already stated over).
So the split is: `mulStrassen` is *defined* over `[Mul R] [Add R] [Sub R]
[OfNat R 0]`, and `mulStrassen_eq_mul` is *proved* over `[Lean.Grind.Ring R]`,
which supplies both the operations and the laws.

A `@[csimp]` replacement must preserve the declaration's type, so Strassen
**cannot** be registered as a type-preserving `@[csimp]` replacement of the
generic `mul`: `mul` has no `[Sub R]`. This is a correction to the issue's
literal wording "just use it by default in matrix multiplication at runtime".
The generic-semiring `*` on `Matrix R n n` keeps the naive `mul` as its
universal, type-correct fallback. Every coefficient type the project actually
multiplies (`Int`, `Rat`, `ZMod64`, `Fp`) is a ring, so `mulStrassen` is
available to every ring-typed caller.

Making Strassen "the default at runtime" therefore has a concrete, stated
mechanism, not an implicit one:

1. `mulStrassen` remains the ring-level reference entry point and the theorem
   `mulStrassen_eq_mul` continues to state its equality to naive `mul`.
   Compiled calls are transferred to the storage-scheduled
   `mulStrassenImpl` by the proved function equality
   `@[csimp] mulStrassen_eq_impl : @mulStrassen = @mulStrassenImpl`, mirroring
   `mul` / `mulImpl` / `mul_eq_mulImpl`, never `@[implemented_by]`.
2. Ring-typed callers with genuine matrix-matrix products opt in by calling
   `mulStrassen` at their own call sites. A survey of the tree found no such
   caller: the dense consumers (`hex-determinant`, `hex-bareiss`,
   `hex-row-reduce`, `hex-lll`, and the `hex-berlekamp` nullspace) are
   elimination-based — row operations, not products; the Gram matrices are
   built entrywise as dot products and exploit a symmetry a materialized
   product would forfeit; and the LLL same-lattice certificate checks product
   equality through packed dot products cheaper than any materialized product.
   So no caller switch exists to perform, and `mulStrassen` is the entry point
   a future product-shaped caller (for example matrix powering) adopts
   directly.
3. Widening `mul` itself to require `[Sub R]`, or redirecting the
   `Mul (Matrix R n n)` instance once the coefficient algebra is known to be a
   ring, are possible later API changes. Both are out of scope here and
   neither is needed today, since no executable caller multiplies through the
   instance.

### The Winograd schedule

Partition each square operand into 2×2 blocks
`A = [[A₁₁, A₁₂], [A₂₁, A₂₂]]` and `B = [[B₁₁, B₁₂], [B₂₁, B₂₂]]`, with the
product `C = [[C₁₁, C₁₂], [C₂₁, C₂₂]]`. The memory-efficient Winograd schedule
(B. Boyer, J.-G. Dumas, C. Pernet, W. Zhou, "Memory efficient scheduling of
Strassen-Winograd matrix multiplication algorithm", ISSAC 2009) is:

    S₁ = A₂₁ + A₂₂    T₁ = B₁₂ − B₁₁
    S₂ = S₁ − A₁₁     T₂ = B₂₂ − T₁
    S₃ = A₁₁ − A₂₁    T₃ = B₂₂ − B₁₂
    S₄ = A₁₂ − S₂     T₄ = T₂ − B₂₁

    P₁ = A₁₁ · B₁₁    P₅ = S₁ · T₁
    P₂ = A₁₂ · B₂₁    P₆ = S₂ · T₂
    P₃ = S₄ · B₂₂     P₇ = S₃ · T₃
    P₄ = A₂₂ · T₄

    U₁ = P₁ + P₂      U₅ = U₄ + P₃
    U₂ = P₁ + P₆      U₆ = U₃ − P₄
    U₃ = U₂ + P₇      U₇ = U₃ + P₅
    U₄ = U₂ + P₅

    C₁₁ = U₁   C₁₂ = U₅   C₂₁ = U₆   C₂₂ = U₇

That is four operand sums `S₁…S₄`, four operand sums `T₁…T₄`, seven recursive
products `P₁…P₇`, and seven result sums `U₁…U₇`, for seven multiplications and
fifteen additions per level. The schedule is a hypothesis the implementation
must **prove**, not trust: the correctness obligation below states it as an
equality against `mul`.

### Recursion, base case, and the customizable backend

`mulStrassen` recurses on the runtime dimensions. When any of `n`, `m`, `k` is at
most 1 or below the `cutoff`, it materializes the current blocks and calls a
**base kernel**. Otherwise it splits and recurses. The `at most 1` part of the
base condition does not depend on the config, so a `cutoff` of 0 or 1 cannot make
the recursion split a `1×1` block forever, and an empty axis drops straight to
the base kernel. The cutoff and the base kernel live in a data-only configuration
record:

    structure StrassenConfig (R : Type u) where
      cutoff  : Nat
      baseMul : {n m k : Nat} → Matrix R n m → Matrix R m k → Matrix R n k

The structure carries no algebraic instances: `baseMul` is a bare function type,
and `Matrix R n m` needs none. The instances appear only where `mul` does, on the
validity predicate. A configuration is **valid** when its base kernel agrees with
`mul`:

    def StrassenConfig.Valid [Mul R] [Add R] [OfNat R 0]
        (cfg : StrassenConfig R) : Prop :=
      ∀ {n m k} (X : Matrix R n m) (Y : Matrix R m k), cfg.baseMul X Y = mul X Y

Keeping the proof out of the data record (rather than a `baseMul_eq` field) lets
`StrassenConfig` stay a plain value and states the correctness theorem under an
explicit `cfg.Valid` hypothesis. The **default** configuration `strassenDefault`
uses the naive `mulImpl` as its base kernel and a benchmarked `cutoff` (see
Benchmarks); `strassenDefault_valid : strassenDefault.Valid` is proved from
`mul_eq_mulImpl`. This is the config the runtime uses. The pluggable `baseMul`
is the "not used by default" backend the issue asks for: a caller supplies a
hand-tuned small-matrix kernel (for example a fixed 3×3 or 4×4 scheme) without
touching the recursion, and proves `cfg.Valid` for it.

**Even dimensions are required to split; odd dimensions are padded.** The
balanced 2×2 schedule needs the two column-blocks of `A` (and the two
row-blocks of `B`) to have matching shapes, so `S₁ = A₂₁ + A₂₂` and the other
operand sums type-check. That forces the split of each of `n`, `m`, `k` to be
exactly in half, which needs each of them to be even. An earlier draft claimed a
`⌊n/2⌋` / `⌈n/2⌉` split makes unequal quadrants work; that is wrong, because
`A₂₁ + A₂₂` would then add an `(n−h)×h` block to an `(n−h)×(m−h)` block.

The recommended handling is **pad each odd dimension up to even at each level**:
where `n`, `m`, or `k` is odd, border that axis with one zero row or column,
split the now-even dimension in half, and recurse on the rectangular even
half-blocks (the products `Pᵢ` are themselves rectangular sub-multiplications).
The border entries are zero, so the true `n × k` product is the top-left block
of the padded product, which is what makes the padding provably correct. The
overhead is at most one extra row or column per axis per level, a bounded
constant factor. The simplest-to-prove alternative is one static pad of each
axis to a power of two at the top; it can nearly double a dimension, so it is
the fallback if per-level padding proves awkward to formalize first. Dynamic
peeling (handle the odd fringe with rank-updates rather than a zero border) has
the lowest overhead and is the option to adopt if benchmarks justify the extra
proof work. The recursion fires only when all of `n`, `m`, `k` are at least 2 (and
at least the cutoff), so each dimension it splits is padded to even and halved to
something strictly smaller. Well-founded recursion on `n + m + k` then discharges
termination, and the config cannot defeat it because the `at most 1` base
condition is config-independent.

### Avoiding sub-block copies

The four quadrants of `A` and `B` are **views** (`Submatrix`, named in the
`Subarray`/`Substring` style), not freshly materialized matrices: a `Submatrix`
is a backing matrix together with a row offset, a column offset, the two block
dimensions (type indices), and the real-data extent (`rhi`/`chi`, one past the
last real row/column in backing coordinates). Reading a quadrant entry adds the
offset and indexes the shared backing store when the position holds real data
(`r0 + i < rhi ∧ c0 + j < chi`) and returns `0` in the zero-pad fringe otherwise.
The recursive splitting therefore never materializes or copies a quadrant buffer (only O(1) view records)
— `Submatrix.toBlocks₁₁ … toBlocks₂₂` are pure offset/extent arithmetic. Because
the backing dims never change through the recursion, `r0 + i < rhi` is the exact
real-vs-pad test at every nesting depth, so widening a view to even dimensions
(`Submatrix.pad`) before a split is likewise a copy-free reshape. The internal
recursion `mulStrassenView` is stated over this view type, not over `Matrix`.
Only when a block drops below the cutoff does the recursion **materialize** that
small view into a `Matrix` (`Submatrix.toMatrix`) and hand it to `cfg.baseMul`,
which is why the public `baseMul` keeps the clean
`Matrix R n m → Matrix R m k → Matrix R n k` type: views inside the recursion,
a materialized `Matrix` at each leaf.

The `Sᵢ` and `Tᵢ` operand sums are genuinely new values, so the *logical*
schedule names fifteen sums. The *storage* schedule is separate:
`mulStrassenImpl` implements the Boyer-Dumas-Pernet-Zhou two-buffer schedule
at square, even recursion nodes. It reuses two auxiliary `(n/2)²` matrices
`X` and `Y`, writes each recursive product directly into one of the four
output quadrants, and accumulates the `Uᵢ` values there without a
`fromBlocks` copy. Rectangular top-level inputs and odd square recursion nodes
retain `mulStrassenView` as the shape-safe fallback; reaching an odd node
reverts that node's entire subtree, so a dimension such as 1000 uses the
schedule for `1000 → 500 → 250` and the reference below 125.

Writes use `Region`, a backing-free rectangle descriptor containing offsets
and bounds proofs but no matrix. One owned output `Matrix` is threaded through
every write and recursive call; quadrant descriptors therefore cannot create
four aliases of its backing. Each update operates directly on the owned
region. Row-start arithmetic is hoisted outside the column loop; overwrite
and accumulation both read the needed entries and then thread the consumed
array through one `lean_array_fset`, without a copy-out/copy-back row. The
generated C can therefore reuse the array when uniquely referenced. The
writer's proof has a stronger
frame property: it returns exactly the reference
result in its destination and preserves every disjoint region. This proves the
complete BDPZ accumulation order without introducing ring assumptions into
the equality transfer.

The **flat row-major backing** (see "Backing representation" above) is what
makes such views cheap: stride-and-cache locality across a whole block, cheap
bulk materialization of a leaf block for the base kernel, and a block view
that is pure offset-and-stride arithmetic into one shared buffer
(`backing[(r0 + i) * m + (c0 + j)]`). `Hex.Matrix` is deliberately an opaque
one-field structure (design principle 10) precisely so that representation
switch stayed invisible to consumers when it landed. The recursion runs over
the `Submatrix` view type (backing matrix plus row/column offsets plus block
dimensions plus real-data extent). The reference recursion still exposes the
logical `Sᵢ`/`Tᵢ`/`Uᵢ`, product, assembly, and crop allocations; the compiled
square/even path replaces that node-local storage with `X`, `Y`, and the
already-owned output, while leaf materialization remains for `cfg.baseMul`.
Correctness reduces to the
same three lemmas: a view-to-matrix abstraction lemma (`toMatrix` of a quadrant
view equals `toBlocks` of the materialized parent, and `toMatrix` of a widened
view equals `Matrix.pad` of the materialized source) carries the view recursion
`mulStrassenView` down to the `mul`-level Winograd/block/padding decomposition,
so the recursion and the correctness proof are identical to the `Matrix`-level
form the migration first shipped.

### Correctness

The public reference stays `mul` (naive, kernel-reducible, `noncomputable`). The
obligation is

    theorem mulStrassen_eq_mul [Lean.Grind.Ring R]
        (cfg : StrassenConfig R) (h : cfg.Valid)
        (M : Matrix R n m) (N : Matrix R m k) :
        mulStrassen cfg M N = mul M N

for every valid configuration, so a correct base kernel and any cutoff give the
naive answer. The `[Lean.Grind.Ring R]` instance carries the algebraic laws the
proof uses. Following "push sorries earlier" (design principle notes), decompose
it into named lemmas:

- a **padding** lemma: bordering an operand with a zero row or column and taking
  the top-left block of the product returns the unpadded product;
- a **block-decomposition** lemma: `mul` of a matrix with each of `n`, `m`, `k`
  even equals the assembly of the four quadrant products, which reduces to
  splitting a length-`m` dot product into its first-half and second-half parts;
- the **Winograd identity**: the seven-product, fifteen-addition schedule above
  equals the 2×2 block product `[[A₁₁B₁₁ + A₁₂B₂₁, …], …]`, proved entrywise
  through `getElem` and the ring laws on `R`.

No `native_decide` and no `axiom` (project policy). Termination is well-founded
on `n + m + k`. It strictly decreases at each recursive call because the
recursion fires only when all three dimensions are at least 2, and a dimension of
at least 2 padded to even and halved is strictly smaller. The base condition
stops at any dimension of at most 1 regardless of the config, so `cutoff = 0` is
still terminating.

### Benchmarks

The crossover `cutoff` is a **measured** constant, not a guessed one (design
principle 9: conformance and benchmarking establish behaviour first). The bench
target
`bench/HexMatrix/Bench.lean` gains a Strassen driver alongside the existing
`runSquareMulChecksum`, sweeping the dimension `n` and the cutoff `τ` on the same
deterministic integer fixtures, and the shipped `strassenDefault.cutoff` is set
where `mulStrassen` first beats `mul` on `Int` coefficients with GMP arithmetic.
The literature expectation for exact integer coefficients is a crossover of
order tens of rows, well below the floating-point figures, but the SPEC requires
the number to be re-measured on this project's coefficient types rather than
assumed. The Strassen driver declares the cost model `n^{log₂ 7}` to the bench
harness (the naive driver declares `n * n * n`), so regression tracking uses the
sub-cubic exponent. The driver stays Mathlib-free and under the wallclock cap
(`SPEC/benchmarking.md` and `SPEC/CI.md`), and it extends the existing single
bench job rather than adding a new one (`SPEC/CI.md`).

The benchmark deliverable is not just numbers: it includes a committed scaling
figure at `reports/figures/hex-matrix-mul-scaling.svg`, generated by
`scripts/plots/hex-matrix-mul-scaling.py` in the same idiom as
`scripts/plots/hex-lll-scaling.py`. The figure is a log-log plot of per-call
wall time against the dimension `n`, with two series, naive `mul` and the
default-config `mulStrassen`, each annotated with its fitted power-law slope over
an explicitly chosen asymptotic window (for example `n ≥ 4·cutoff` and spanning
at least a decade, matching the window the speedup table below fits over). The
diagnostic target is a naive slope near `3.0` and a Strassen slope near
`log₂ 7 ≈ 2.81`, with the crossover where the two lines meet marked. The fitted
Strassen exponent is only a diagnostic, not an acceptance condition: near the
cutoff the Strassen curve is in a crossover transient, and on the row-of-rows
backing the locality overhead and the limited benched sizes bend the fit above
`2.81`. The exponent approaches `log₂ 7` only once the sizes are large enough or
the `Submatrix` view recursion lands on the flat backing (see the representation
note below). The point the figure must make is the visibly
shallower Strassen slope: Strassen lowers the asymptotic order, not merely the
constant factor. A speedup table
that fits both exponents by ordinary least squares over the asymptotic window,
as `hex-lll-scaling.py` does, accompanies the figure.

The measured crossover is representation-dependent, so the bench records which
backing it ran on. The flat row-major switch itself was measured as a
before/after overlay on this same multiply bench: **neutral on the multiply
surface** (naive `1.00–1.02×`, default-config `mulStrassen` `0.98–1.00×`
across `64…1024`; identical checksums) with a small Bareiss elimination cost
(`1–4%`, shrinking with `n`). The multiply hot paths were already
row-contiguous under row-of-rows, so parity is the expected reading; what the
flat backing changes for Strassen is not these curves but the cost model of
the *recursion's internals* — quadrant materialization and leaf handling —
which is why the crossover gets re-measured when the `Submatrix`-view
recursion (see "Avoiding sub-block copies") replaces materialized quadrants,
not before. That re-measurement is recorded with the shipped
`strassenDefault.cutoff` in `HexMatrix/Strassen.lean`.

### A demonstration non-default config

The pluggable base kernel is only credible if at least one non-default config is
built and shown to pay off, so the SPEC requires one demonstration config. The
base kernel `baseMul` is polymorphic over the dimensions `{n m k}` because the
recursion reaches the base case at a range of shapes (any block with a dimension
below the cutoff, including rectangular ones), not at one fixed size. A
size-specialized kernel is therefore written as a single function that dispatches
on the runtime dimensions and falls back to the naive kernel off its fast path.

The demonstration config targets the Barrett-reduced prime-field residues
(`ZMod64` / `Fp`) as a standalone kernel for future product-shaped callers. The
current tree has no production matrix-matrix consumer to route through it:
Berlekamp nullspace and the other dense consumers use elimination or individual
dot products, as recorded in the caller survey above. The default base kernel
reduces modulo `p` after every multiply-add. The demonstration kernel instead
accumulates each dot product in a wide accumulator and reduces less often. It
must use the **periodic-reduction** form, reducing the accumulator modulo `p`
every fixed number of terms chosen to preclude overflow, not a single reduction
at the end over a 128-bit accumulator. The reason is that
`Valid` quantifies over all `n`, `m`, `k`, and at a base-case leaf only one
dimension is guaranteed below the cutoff: the inner dimension `m` (the dot-product
length) can be arbitrarily large, so a fixed-width accumulator with one final
reduction is not provably correct for every `m`, while periodic reduction is.
`BarrettCtx` keeps `p < 2^32`, so each single product fits in 64 bits and a
bounded run of them fits in the wide accumulator between reductions.

This is the standard delayed-reduction trick for modular matrix multiplication,
and it is `Valid` because reduction modulo `p` is a ring homomorphism, so the
periodically-reduced sum has the same residue as reducing at each step. The proof
is more than one lemma: it needs an accumulator invariant (the running sum modulo
`p`), the per-window no-overflow bound, the final-reduction step, and the equality
to the `ZMod64` / `Fp` dot product the naive kernel computes. The verified
two-word layer in `HexArith/Barrett/Accumulator.lean` supplies the add, reduce,
and fold lemmas; `HexBerlekamp/DelayedKernel.lean` bridges the fold to the
`ZMod64` dot product and the polymorphic matrix base kernel.

Two honesty constraints on this config. First, a base kernel fires only below
the cutoff, so it moves the constant factor and the crossover, never the
asymptotic slope. Its evidence is a separate comparison plot of default-base
against delayed-reduction-base `mulStrassen` on the prime field, not a third
slope on the scaling figure above. Second, it earns its place only if it
measurably beats the default naive base kernel on that type (design principle 9).
If the measured win does not materialize, the demonstration reverts to a trivial
alternate config that still exercises the plug-in path, and the delayed-reduction
kernel becomes follow-up work. A GF(2) four-Russians base kernel would be the
strongest showcase, but the project has no bit-packed GF(2) matrix
representation, so it is out of scope here.

The shipped `strassenBarrett` uses a 4096-term window. The accumulator proof
shows that the high word grows by at most one per product, so every unreduced
window fits below `2^128`; reducing a window and the final partial window
preserves the running residue for arbitrary inner dimension. The committed
measurement compares `mulImpl` directly with the periodic leaf and compares
full `mulStrassen` both as shipped and at matched cutoffs, at `p = 5`, `65537`,
and `2^31 - 1`. Across the square and rectangular cases the leaf is
`2.93`–`16.84×` faster and full Strassen is `13.32`–`15.30×` faster; the
matched-cutoff controls are `5.68`–`15.80×`. Leaf contractions of length
`12289` and `20481` cross three and five windows. A sweep against 256-term and
effectively single-flush alternatives measures the selected window's periodic
cost at `3.9`–`5.4%` against the single-flush loop. The result clears the 5%
demonstration gate without changing `strassenDefault`.

### Conformance

`conformance/HexMatrix/Conformance.lean` gains `#guard` checks that
`mulStrassen cfg A B = mul A B` on committed fixtures spanning even, odd, and
prime dimensions, the empty and 1×1 matrices, and a dimension straddling the
cutoff, with both `strassenDefault` and a non-default custom base kernel. The 1×1
and empty fixtures also exercise the config-independent base condition that keeps
the recursion terminating. Because correctness is a theorem, this differential
check is a cross-check that the compiled `mulStrassen` agrees with the reference
`mul` on concrete inputs. It runs through `#guard`, the compiled-evaluator path,
not kernel `decide`: `mulStrassen` is defined by well-founded recursion and does
not reduce cheaply in the kernel, so it stays off the `decide` cross-check path
that design principle 11 discusses. Oracle: none; the surface is structural-layer
exact arithmetic, as for the existing multiplication guards.

`Matrix.castRows` transports the row dimension along an equality without
changing the backing buffer. `Matrix.getElem_castRows` and
`Matrix.getElem_castRows_nested` expose its pair and nested entry behaviour;
`Matrix.getElem_pair_eq_get` relates constant-time pair access to the explicit
row-vector projection. These representation lemmas support downstream
dimension-dependent projections without making the backing field public.

`conformance/HexBerlekamp/Conformance.lean` adds the coefficient-specific
cross-checks for `strassenBarrett`: near-upper-bound residues exercise high-word
carries; inner dimensions `4095`, `4096`, and `4097` straddle the implementation
dispatch and exact flush; `12289` covers three flushes plus a partial tail; and
empty contraction/output axes cover the generic rectangular signature.

### New public names

`Matrix.StrassenConfig`, `Matrix.StrassenConfig.Valid`, `Matrix.strassenDefault`,
`Matrix.strassenDefault_valid`, `Matrix.mulStrassen`, and the correctness theorem
`Matrix.mulStrassen_eq_mul`, with the padding, block-decomposition, and
Winograd-identity lemmas it decomposes into. Names stay short verb-noun forms
with qualifiers in the `Hex.Matrix` namespace. Prior art for a verified Strassen
is CoqEAL's refinement-based implementation (`SPEC/prior-art.md`); `hex-matrix`
instead proves the executable schedule equal to the naive reference directly and
swaps it in with `@[csimp]`.

The row-transport additions are `Matrix.castRows`,
`Matrix.getElem_castRows`, `Matrix.getElem_castRows_nested`, and
`Matrix.getElem_pair_eq_get`.

## External comparators

The dense base surfaces (matrix multiplication, row operations, transposition,
slicing) have **no** external comparator named. They declare absence with the
**structural-layer** reason per
[the benchmarking spec's "Comparator naming" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#comparator-naming):
those surfaces are GMP-backed `Int` arithmetic on `Vector` / `Array`
primitives. The determinant comparator (FLINT `fmpz_mat_det`) covers the
determinant surface and lives in `hex-bareiss`.

The Strassen bench driver declares the same **structural-layer** absence: it
measures the multiplication surface already covered above, and its baseline is
the internal naive `mul`, not an external tool. Its deliverable is the measured
crossover cutoff and the speedup at the largest benched dimension, recorded in
the headline report.

Structured metadata in the project's
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml)
under `HexMatrix.phase4`.
