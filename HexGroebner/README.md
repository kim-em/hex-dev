# HexGroebner

Mathlib-free finite-field F4 under [the governing contract](../SPEC/Libraries/hex-groebner.md).

`Hex.Groebner.computeWith` performs deterministic prime-field F4 candidate
production. Its explicit context fixes the prime field, variable count and
lawful lex, grlex or grevlex order. Raw terms are validated, repeated monomials
combined, zero coefficients removed and supports sorted. Critical pairs use
explicit total-degree or sugar-degree batching and are held in a persistent leftist heap; product and resolved-dependency chain criteria
discard unneeded pairs. Symbolic preprocessing closes a selected batch under a
basis-specific divisibility trie and constructs one joint Macaulay matrix.
The chain test visits indexed LCM divisors; final tail reductions share one
immutable reducer index.
Symbolic support membership uses a bitmap of stable arena identifiers. It grows
as reducer products are interned and preserves first-occurrence queue order.
The workspace retains the bitmap across preparations and checkpoints. Growth
counts against the parent work and packed-byte limits once; the next preparation
clears only the previously visited identifiers and charges that clearing work.
Cache hits and separate-tail normal forms reuse the paid-for bitmap payload.
Deterministic, sampled and certificate-producing loops move the workspace out
of the old round state before running the next computation. Column sorting
consumes the visited queue; the sorted columns also identify bits to clear.
Externally retained checkpoints and shared raw buffers preserve their snapshots
through ordinary copy-on-write.
With `nativeMonomials := true`, a bounded operation validates and queues slices
of at most 4096 packed identifiers. Shared and borrowed buffers retain their
contents; disabling native monomial operations selects the portable definition.
The [support-queue measurements](../reports/bench-results/hexgroebner-support.md)
separate primitive timings, complete F4 candidate timings and independent checks.
Joint matrix elimination stably orders targets by decreasing leading-column
index, then increasing support size, retaining input order for equal keys.
This starts with smaller leading monomials in the decreasing monomial column
map. Sorting work is
charged before the sort. Independent normal forms retain their input order;
traced production moves each target's derivation root with its polynomial.
Known reducer pivots retain their contracts with either scheduling strategy.
F4 checkpoints retain a `ReducerCache` of multiplied reducers from the same
append-only monomial arena. Stable IDs survive exponent-width changes.
Monomial hash buckets and collision links use packed `UInt32` buffers. Hashes
only filter candidates; exact exponent comparison decides equality. Index
growth, rebuilding work and peak packed payload are charged before allocation.
A bounded owned native operation can complete lookup or insertion within the
current width and index capacity, for up to 2047 variables and 4096 additional
work units. Unsupported shapes, widening, index growth and tight allowances
return the unchanged table; portable continuation starts after the native frame
returns. Multiplied polynomial supports use slices of at most 64 identifiers,
reduced to `max(1, floor(4096/(3*arity+4)))` as arity grows, leaving room
for extra collision-chain headers. A one-term slice retains the scalar loop
to reuse its workspace; this starts at arity 682.
A native batch can complete product lookups and same-width, same-capacity
insertions within 4096 total charged work units, returning stable identifiers
and the complete final workspace and table work. Errors, widening, index growth
and unsupported geometry defer the unchanged table to scalar operations.
Every slice uses the remaining parent allowances. Conformance compares the
complete slice loop with the original scalar failure prefixes.
`productsWith_spec` proves the pure wrapper equal to its scalar model;
conformance checks the C provider's result and exact admission decisions.
Explicit borrowed-support aliases use controlled copies that preserve the linear
mark, including when the table is shared. Other arena sharing retains Lean's
nonlinearity diagnostics. The private exponent plan uses the conservative
4096-coordinate scratch bound; successful insertion bytes are at most 5460,
since `terms*(3*arity+1) ≤ 4096` and each coordinate uses at most four bytes.
The complete private plan remains below 32 KiB.
Shared and aliased buffers retain their original contents. Field/order metadata is checked before
reuse, and the complete base payload identifies the basis polynomial. A cache
hit checks the complete base polynomial, comparing at most 4096 bytes per native
call; basis changes cannot silently reuse a different row. Sugar and certificate
derivations are rebuilt from the current basis. The private cache retains at most
16384 entries, charges eight logical key bytes per insertion and all comparison
work to the parent allowance, and shares already charged polynomial buffers.
When key storage would not fit, multiplication continues without caching that
product. Every hit also validates all product exponents against the current
arena, with at most 4096 coordinate comparisons per native call; incompatible
identifier meanings in public raw calls over arenas produced by the interning
API therefore cannot return a stale row.
The portable route checks the same exact identities. Full caches permit
replacement of an existing key, charging each insertion cumulatively.
The [cache measurements](../reports/bench-results/hexgroebner-arena-cache.md)
retain full-system results, small-case regressions and fixed-benchmark variability.
Final minimal-leading-monomial selection and tail reduction produce canonical
monic, sorted, reduced output. Empty/all-zero input produces an empty basis;
the unit ideal produces `[1]`, including zero-variable inputs. Ordinary
characteristic-two polynomials receive no implicit field equations.

`computeWith` success is an **unchecked candidate**, carrying the field/order
identity, canonical interchange polynomials and explicit random state.
Deterministic execution consumes no random samples. `basisWith` computes and
independently certifies a basis; `certifyWith` constructs and checks a certificate
for explicit candidate data. Their canonical natural-residue inputs are
distinct from `computeWith` raw interchange arrays. `checkBasis` independently
replays a complete certificate. `Certificate.BasisVerification.verifyWith`
checks a supplied witness under cumulative replay limits and returns a sealed
`CheckedBasis` on acceptance.

`PrimeField.ofZMod64` reuses actual primality and bounds evidence. Every prime
`2 ≤ p < 2^31` is supported. A context can also carry a proof from
`Hex.Nat.isPrimeTrial_isPrime`; no unchecked primality flag is accepted.
`Polynomial.toMvPoly` and `ofMvPoly` preserve the fixed-arity interchange terms.

```lean
def field : Hex.Groebner.PrimeField :=
  ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

def candidate : Hex.Groebner.ComputeResult :=
  Hex.Groebner.computeWith ⟨field, 2, .grevlex⟩ {} #[
    #[⟨#[2, 0], 1⟩, ⟨#[0, 1], 6⟩],
    #[⟨#[1, 1], 1⟩, ⟨#[0, 0], 6⟩]]
```

The same system can be computed with complete independent certification:

```lean
def checked : Hex.Groebner.BasisResult ⟨field, 2, .grevlex⟩
    #[[([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]] none :=
  Hex.Groebner.basisWith ⟨field, 2, .grevlex⟩ {}
    #[[([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]]
```

A successful receipt's `value` supplies the checked basis for `normalFormWith`
and `memberWith`. `HexGroebnerTheory.basisWith_sound` proves that its polynomials
are the reduced Gröbner basis of these exact generators. The downstream
[`PolynomialExample`](../HexGroebnerTheory/PolynomialExample.lean) states
`x ∉ (x² − y, xy − 1)` directly with Mathlib polynomials over `ZMod 7` and proves
it by ordinary kernel replay of a generated certificate.

This example needs the additional basis polynomial `y² - x`; checking only
ideal-membership identities for the two original generators would miss that
S-pair obligation. Candidate production alone supplies no Lean ideal theorem.

`resumeWith` accepts a sealed state and larger absolute cumulative allowances.
Its immutable identity retains the generators, field, order and seed. Input
normalization, each F4 round and final interreduction are atomic basis/pair
checkpoints. On exhaustion, no partially processed batch loses unresolved pairs;
temporary interned monomials and charged work survive. Retrying a stage charges
its repeated work. Invalid input, internal invariant failures, representation
exhaustion and consumed allowances remain distinct. `Limits.packedBytes` bounds monomial arenas plus
cumulative packed polynomial/matrix allocation, eight bytes per reducer-cache
insertion, and decoded interchange scalar
payload; it excludes headers and allocator capacity. Pair attempts, rounds,
basis size, cumulative matrix rows/entries, monomials and variables have
separate bounds.
Batch size has a minimum of one. Nested hashing, widening, sorting, polynomial
arithmetic and matrix work share the remaining parent allowance. These are
operational counters, not predictions of elapsed time. `Statistics.matrixTargets`
counts target rows in calls that reach the elimination kernel; `matrixReductions` counts
completed pivot applications, and `matrixZeroRows` counts rows found zero. These
include failed-call prefixes and repeated work after an atomic-stage retry.
Zero rows include inputs that were already empty. F4 symbolic reducers have
distinct leading columns, so successful F4 calls count zero rows only among
targets. The conformance corpus checks matrix-counter agreement between
successful uninterrupted traced and unchecked computations with the same
strategy. Exhaustion and resumption can produce different prefixes and repeated
work. These counts describe algebraic work rather than elapsed time or the
probability of a sampling miss.

`Sampled.computeWith context limits generators random config` selects seeded
candidate production with random combinations in pair rounds. Input normalization
and final interreduction retain deterministic F4. `Sampling.Config` fixes block
size (1–4096) and a positive total-zero stopping count; the count does not reset
after a new pivot. Full-field coefficients use `Hex.Rand` rejection draws. No
uniformity, independence or rank-preservation probability is asserted for this
pseudorandom generator. Block sugar labels bound all contributing rows.

The optional `minimumTargets` argument selects deterministic elimination for
pair matrices below that target count, after the same pair selection and symbolic
preprocessing. Its default is zero. The sealed continuation and candidate retain
the policy; deterministic batches consume parent allowances without drawing random
words. `hexgroebner_sample --min-targets N` exposes the same option. This does
not turn sampled candidates into checked bases. Final certification remains
independent. The cutoff can improve small-matrix costs, but is not a universal
performance choice across fields and systems.

When a minimum target count is requested, a smaller pair matrix uses atomic
deterministic elimination within its preparation slice. The `matrixSteps`
quantum applies to sampled matrices. A deterministic batch can contain many
reducers even when its target count is small; exhaustion retries selection,
preprocessing and elimination, charging repeated work. A changed resumed
batch-size cap can change the cutoff decision. Pending sampled matrices retain
their selected rows and advanced random state.

`Sampled.Result.candidate` carries an unchecked `Sampled.Candidate`, ordinary work
statistics and separate sampling counts. The candidate retains the initial random
state, sampling controls and monomial-arena counts alongside the advanced state.
Independent complete-basis certification
remains necessary. The current route exposes candidate production and separate
`certifyWith` validation; a checked retry/fallback driver remains to be implemented.
The conformance corpus includes deliberate rank misses that certification rejects.
The [sampling measurements](../reports/bench-results/hexgroebner-sampling.md)
retain the negative and inconclusive development campaigns. Sampling remains
slower overall than deterministic F4 on that suite and is explicitly opt-in.

A sealed `Sampled.State` fixes context, inputs, scheduling and sampling controls.
It preserves the selected pair batch, column map, advanced random state, accepted
coefficient and partial combination/scan/gather on exhaustion. Resumption charges
only new matrix work; atomic output decoding or basis-update retries charge their
repeated work. `Sampled.resumeWith` also accepts a scheduling quantum: its
`suspended` result retains unfinished work without claiming budget exhaustion.
Each call performs at most one million outer slices, each with at most 64 matrix
phases. The optional matrix quantum is clamped to 1–64 phases. Library callers
continue `.suspended` states when they want completion; the CLI does this
automatically. Native combination, scan and gather calls inspect at most 4096 entries.
Combination bounds omit untouched columns and extend when reducers introduce a
later column. Inversion reserves its multiplication cost and the gather column-sweep charge
before charging work, so phase resumption does not repeat an inverse prefix.
Gather normalization is charged incrementally as output entries are appended.

Sampling charges random words, combination updates, validation, initialization,
elimination, output and subsequent F4 work to the parent allowances. The row
allowance and matrix row/target counters include original inputs and generated
combinations. `Sampled.Statistics.inputTargets` and `combinations` separate these
classes. A generated row is counted when submitted to elimination; a pending
combination retains its consumed words if the row allowance is exhausted.
`Sampling.next_spec` and `advance_spec` prove agreement with scalar phases;
compiled native/scalar and sanitizer checks cover actual foreign execution.

`Limits.densePivots` optionally prepares checked dense pivot buffers for
untraced deterministic M31 matrices (`p = 2147483647`). It defaults to `false`;
the driver accepts `--dense-pivots true|false`. Other fields, certificate
production and sampled computation retain their existing sparse kernels.
Admission requires 128–4096 nonzero entries, at most 65536 matrix columns,
a non-contiguous span at least three-quarter full, and sufficient parent work
and packed-byte allowances. Fully contiguous pivots use the existing sparse
kernel's contiguous SIMD path. Matrices without any admitted cache also keep
that path.

Each cache retains its immutable sparse source. The typed cache proves exact
coefficient equality, source-array correspondence and whether any dense buffer
is active. Preparation reserves its entire bounded cost before traversing the
row. Dense updates preserve zero gaps, every intermediate cursor and the first
malformed-target prefix; partial pending reductions use locally bounded dense packets or sparse updates. A call
advances at most 4096 logical updates and 8192 dense cells. Cache preparation
and payload count against the same parent allowances as elimination. The
continuation and whole-eliminator correspondence proofs include these charges.
Bulk elimination retains its ordinary frame eligibility. Its validated monic
rows determine exact preparation charges without materializing unused caches;
the same parent-budget refusal rules and fixed work quantum still apply.
The low-level `MatrixLimits.densePivots` also charges requested preparation in
reference and traced calls, preserving the exact shared counter contract; those
routes discard caches. Scalar row updates remain scalar, while explicitly
requested preparation uses its bounded native provider. The polynomial
certificate producer does not enable that low-level policy.
This option does not establish a full-system speedup or the performance milestone.

`Limits.binaryPivots` optionally uses private bit-packed pivots and an accumulator
in untraced ordinary F2 matrix frames. It defaults to `false`; the deterministic
driver accepts `--binary-pivots true|false` and records the requested policy.
This preserves ordinary polynomial semantics, including distinct monomials
`x` and `x²`. Other fields retain their existing route. Admission permits at
most 16384 columns, 16384 reducers and 1024 targets, with bounds of `2^32`
reference work and `2^28` packing/scalar/word visits. The private bitmap stores
at most the lesser of the row and column counts in pivot rows, plus one
accumulator. Each pivot also stores its length, final column and sugar in a
private 16-byte metadata record, avoiding repeated object traversal during word
updates. Frames with at least 64 columns, four known reducers and 64 targets
first project every target through the known reducers in column order, then
eliminate by target pivots in their original order. Private target bitmaps and
last-column/sugar records preserve the reference scan extent and labels. Four
consecutive dense known pivots use a reusable 16-row XOR table. Its triangular
head-pattern map selects exactly the reference pivots; cancelled tails still
retain every selected row's work, end column and sugar. A sparse pivot interrupts
the group and uses its ordinary update. Their
initialization, copies and reduction visits are included in the physical bound.
Each group replaces at most four full-width known-row updates by one table
update. Admission deducts that exact worst-case saving while retaining table
construction and mask-selection charges. An early lower bound rejects frames
whose prefix alone exceeds the cap; the complete check follows known-pivot
installation and precedes target elimination. The physical cap remains `2^28`.
The bitmap and metadata payload fits the remaining packed-byte allowance
alongside the complete sparse-reference charges. Those logical counters remain
identical; the private buffers never escape the call. Sparse wide pivots toggle
their explicit entries, while denser pivots use exact word XOR. Word scans and
gathers decode the same byte layout on every host.

A byte-allowance refusal can discard a partially or fully processed native frame
before the reference continuation succeeds. Speculation is bounded per frame;
multiple matrix calls can incur it. The reservation is conservative: reference workspace charges coexist with the
private accumulator allowance, and empty or sparse-only pivots still reserve
bitmap rows. The certificate producer leaves this low-level policy disabled.
This policy has no fastest-open-source claim.

The packed-payload allowance is not a process-memory limit: it excludes
hash tables, tree nodes, object headers and allocator capacity. Structural
monomial, pair-attempt, basis and variable bounds also limit metadata growth.
Accounting for live heap overhead remains an outstanding memory-control
requirement of the SPEC.

Monomial identifiers index an append-only packed arena, with cached degree,
semantic hash and support mask. Hash buckets use full exponent equality checks.
Exponent storage widens from 8 to 16 to 32 bits before overflow, preserving
identifiers and hashes. Larger exponents produce representation exhaustion.
Divisibility masks only reject candidates; trie paths inspect exact exponents.
Immutable reducer indices also retain a validated packed tree when small enough.
The validated format admits at most 16384 nodes and 16383 edges. Lookup preserves
sparse-row preference, higher-degree tie breaking and LIFO traversal ties.
Lean assigns explicit priorities once; native lookup selects the least admitted
priority without implementing the F4 preference policy. Checked descendant
priority bounds skip non-improving subtrees; a divisor attaining the root bound
ends the search because no remaining leaf can improve its priority.
Its fixed 16384-entry stack and 32768-unit query quantum cover every complete
walk of at most 32767 node/edge visits. Unsupported formats decline before
traversal; larger indices retain ordinary traversal under the parent allowance.
Validation separately inspects at most 32767 node/edge records.
Encoding and validation charge the parent work and packed-byte allowances;
insufficient preparation allowances and larger trees retain ordinary traversal.
Queries use the current arena and exponent width, so stable IDs remain valid
after arena extension or widening. The portable packed model and the original
node traversal independently check results and exact exhaustion prefixes.
The native harness includes maximum-stack read-only guard-page probes.
Polynomials use separate packed stable-identifier and coefficient buffers.
Coefficients occupy one byte below modulus 256, two below 65536, and four for
larger supported primes. Interchange decoding occurs outside the hot loops.
Packed scalar reads retain their byte-based kernel definition and compile through
a proved rewrite to one complete range check and unboxed indices. Reducer lookup
accumulates work locally and commits its exact charged prefix once, including
exhaustion. [Matched observations](../reports/bench-results/hexgroebner-access.md)
retain the incremental gains, variability and unresolved cyclic-case result.

Cached 64-bit metadata uses `Packed.read64`. Its byte-based kernel definition
is preserved while a proved compiler rewrite selects checked unboxed reads.
The equality covers all byte arrays and offsets, with an explicit platform
address bound; it needs no custom native binding. The
[metadata measurements](../reports/bench-results/hexgroebner-metadata.md) retain
full-system and registered lean-bench comparisons, including slower variants.

For arities 1 through 4096, `MonomialTable.combineOwned` uses bounded native
packed preparation and full-coordinate collision comparisons. LCM, product and
exact quotient share one owned reusable buffer for u32 coordinates and cached
metadata. `Limits.nativeMonomials := false` retains the coordinate-array route;
zero and larger arities use it automatically. Both routes preserve stable IDs,
exact overflow rejection and successful work counters. Both backends reserve the same workspace payload after the first monomial,
including when the physical buffer has not yet been allocated or was consumed
by a failed operation. Byte and monomial-count exhaustion are explicit distinct
errors. The single-monomial operation copies shared workspaces and reuses
uniquely owned buffers. A successful lookup batch allocates a fresh final
workspace and result slice. Native primitives have transparent portable bodies,
check geometry before access and preserve borrowed source bytes under aliasing.
The `*Arrays` benchmarks compare complete candidates on these two routes.

Monomial ordering and divisibility use read-only native coordinate comparisons
for arities through 4096 and u8/u16/u32 exponent storage. Cached degree and mask
filters run first. Arbitrary-precision indices are checked before narrowing;
complete row spans are checked before native reads. Larger arities and
unsupported shapes retain the portable coordinate loops. The primitives have
transparent portable bodies and preserve borrowed buffers.

`eliminateWith` accepts a fixed column count, canonical sparse reducer rows and
target rows. Columns must follow decreasing monomial order. Reducers with free
leading columns install directly; other rows scan their active interval,
extending it when a pivot introduces a later term. Empty rows bypass the dense
accumulator. Target rows reduce against reducers and earlier target pivots.
Outputs are monic echelon rows in the original column order. `fromTarget`
identifies added row-space dimension. The retained reducer rows span the input
reducer space. Pivot metadata retains the normalization scalar and propagated
sugar, allowing ordinary remainders to preserve their original coefficients.
Untraced native elimination first tries a complete matrix frame on the 64-bit
ABI, with at most 4096 columns, 1024 known reducers, 64 targets and a conservative
`2^20` work quantum. Unsupported shapes continue outside the native frame.
Cancellation is observed between these bounded calls; the whole-matrix quantum
is coarser than a scan or gather chunk. Native scan and row-extraction calls
within this frame or the ordinary route process at most 4096 transitions or
columns. A scan transition visits a column, updates one sparse entry, or completes
one reduction; a long row resumes with its work already reserved. Row extraction
normalizes nonzero entries and clears the accumulator. Both operations retain
charged prefixes on exhaustion, including the ordering of trace-node and byte
failures. `eliminateWith (... native := false)` and `Limits.nativeRows := false`
select the scalar Lean reference. Both routes produce identical pivots,
provenance, sugar and resource counters. The transparent portable definitions
also support ordinary-kernel replay independently of the C implementation.
Owned accumulator/output buffers use copy-on-write when aliased; input pivot
buffers remain borrowed.

The ordinary matrix loop also uses native validation for rows of at most 65,537
entries and at most 2^32−1 ambient columns on 64-bit hosts, with input counters
below 2^62. Calls decline before charges outside that geometry. Native zeroed
buffer allocation admits at most one MiB per call; larger buffers use the
portable allocator. Both bindings borrow inputs and return fresh owned results.
`Matrix.validateWith_spec` and `Matrix.zerosWith_spec` equate their Lean models
to the original operations, including exact first errors and charge prefixes.
The C implementations are audited and compared independently. Disabling native
rows also disables these validation/allocation calls. The existing column-map
builder separately uses the 4096-byte append-zero provider in chunks.

The five Groebner native objects use the host `cc` by default. To choose a
specific compiler, run `lake -R -KhexGroebnerCC=/absolute/path/to/clang build HexGroebner`.
The compiler path string and flags are part of the object build traces; compiler
contents and PATH resolution are not. Prefer absolute immutable paths, and clean
native objects and any enabled artifact cache after upgrading a compiler in place.
Set `TMPDIR` to a writable directory when the build environment restricts `/tmp`. Other
libraries and Lean-generated C retain their own compiler choices. Lake retains
this setting across later plain builds; use `-R` when changing it.
`lake -R build` restores defaults and
resets other `-K` settings too. The freeze tool's `--native-cc` option makes
compiler commands absolute before detached builds while preserving symlink invocation
names. It records compiler identities and any `--compiler-input` files supplied.
[Compiler observations](../reports/bench-results/hexgroebner-compiler.md) keep
Groebner-only and broader compiler changes separate, with no overall speed claim.

The native scan dispatches once per bounded call to specialized one-, two- or
four-byte scalar loops. In characteristic two, validated subtraction uses exact
XOR. Other scalar products use uint128 Barrett reduction when
available and exact word remainder otherwise. One- and two-byte residues use a
32-bit reciprocal; four-byte residues use a 64-bit reciprocal. Products fit below
`p² < 2^62`; subtraction uses an unsigned wrap mask.
[Scalar F2 observations](../reports/bench-results/hexgroebner-xor.md) retain
matched development comparisons and the remaining msolve gap.
On x86 with runtime AVX2 support, odd moduli use eight exact products at a time.
Sixteen-lane dispatch is opt-in: run
`lake -R -KhexGroebnerAVX512=true build` to enable it, and `lake -R build`
to restore the default. Lake retains these settings for later plain builds;
reconfiguration resets other `-K` settings too, so supply any you need again.
With that option, AVX-512F/DQ/BW/VL and the corresponding
OS register state available, the ordinary sparse scan first attempts sixteen exact products. Refused packets
continue through the eight-lane and scalar paths in order. The optional dense
pivot cache retains its existing AVX2 path.
One- and two-byte coefficients use a 32-bit Barrett reciprocal: the product is
below `2^32`, so the approximate quotient is low by at most one. Four-byte
coefficients use Montgomery products. The factor alone is temporarily converted
to Montgomery form; stored coefficients remain canonical residues. For
`R = 2^32`, the unreduced numerator is below `p² + R*p < 3*2^62`, so unsigned
64-bit lanes cannot overflow and one correction suffices.

For `p = 2^31 - 1`, a separate dispatch uses exact Mersenne folding on both contiguous
and scattered vectors. The folded product is below
`2*p`, so one subtraction gives the canonical residue. The native harness counts
these folds inside complete F4 calls and checks both vector layouts separately. Contiguous columns
use vector loads/stores; other supports use gathers and scalar stores. Narrow
gathers mask the requested scalar out of a four-byte read and require that the
entire read lies within the logical buffer. Boundary vectors use scalar updates.
A vector is validated before mutation; a malformed vector falls back to scalar handling
so the exact failure prefix is preserved. Other architectures and CPUs use the
scalar implementation. No floating-point arithmetic or global ISA flag is
required. CPU detection checks CPUID and the OS-enabled YMM/ZMM state, caches the
result atomically and needs no compiler-runtime CPU model symbols.
The internal `HEX_GROEBNER_NO_AVX512` test define retains AVX2 dispatch;
`HEX_GROEBNER_NO_AVX2` disables both vector providers. [Matched observations](../reports/bench-results/hexgroebner-avx512.md)
show kernel improvements on the measured Zen 5 host without an overall F4 speed claim.
Performance on other microarchitectures and unmeasured coefficient widths remains
unevaluated; the default remains AVX2 or scalar.

`scripts/ci/check_groebner_rows.sh` runs the standalone native tests and the
compiled matrix harness. `scripts/ci/check_groebner_matrix.py` compares all six
opt-in/forced-AVX2/scalar and Barrett/remainder build combinations with the portable model,
including valid strided vectors and even moduli. Native call counters ensure
that the linked test implementations actually run; successful contiguous and
strided SIMD calls are counted separately at each of the three coefficient
widths. `HEX_GROEBNER_REQUIRE_AVX2=1` requires
hardware SIMD coverage. `HEX_GROEBNER_REQUIRE_AVX512=1` requires actual
sixteen-lane execution in the automatic variants. Set `HEX_GROEBNER_SANITIZE=1` for UBSan and ASan on
C-owned memory (the kernel buffers themselves are Lean sarrays), and
`HEX_GROEBNER_NATIVE_LOG_DIR` to retain its generated Lake project. The compiled
variant harness uses ELF linker wrapping on Linux; ordinary Lean conformance
and standalone tests apply on other platforms too. Sanitizer runtime and loader
overrides for Nix hosts are documented in the script. Lean's mimalloc buffers
lack ASan heap redzones; the standalone SIMD tests instead place each buffer's
last valid byte immediately before a protected page and exercise contiguous,
strided and rejected boundary vectors. UBSan failures are fatal regardless of
`UBSAN_OPTIONS`.

The [small-field measurements](../reports/bench-results/hexgroebner-small-fields.md)
retain matched production comparisons, full-system observations and alternative
accumulator measurements. These extend the registered matrix cases to moduli
251 and 32003 and add a cyclic-6 case at modulus 32003.

`reduceRowsWith` instead reduces every target independently against the same
reducer echelon space. It preserves scalars, input order and zero rows; no target
becomes a pivot for another target. Final interreduction shares symbolic closure
across nonzero tails and uses this mode. `Limits.batchInterreduce := false`
retains separate tail calls. The `*Separate` lean-bench registrations compare
these routes under identical fields, inputs and allowances.

`ColumnMap` assigns matrix positions using packed u32 positions plus one for
identifier prefixes with at most eight slots per column, or exact open-addressed
u32 key/value buckets for sparse IDs. Full keys resolve every hash collision.
Geometry alone selects the representation; unsupported IDs, addressability and
insertion chains beyond 64 probes retain the hash-map route. Every attempted
probe and initialized packed payload is charged, including a discarded index.
Rows reserve the maximum recorded probe count per entry; sorting reserves
two such lookups per comparison. Consequently this
conservative work model and cumulative packed-byte charges can exhaust earlier
than the old unit-cost hash map. Both candidate and certificate row construction
use the same map. Bounded native translation consumes at most 4096 IDs per call;
`nativeRows := false` retains its scalar Lean model. Marked borrowed/output
alias handling is defensive support for C callers with one output owner; it
does not extend Lean’s marked-linearity contract to shared marked values. The
encoder creates fresh unmarked output. Kernel benchmarks cover
construction, translation and complete map/output hashing over fixed sizes.

`MatrixLimits` bounds one call's columns, rows, input/output nonzeros, packed
payload, work and optional provenance nodes. Packed payload counts input,
workspace and output buffers plus 64 logical bytes per recorded derivation
operation; it excludes other headers and allocator capacity, and
may count shared buffers twice. Work covers row visits, sparse updates
(including their products), dense-column visits, normalization/inversion
products and workspace bytes initialized. Monic sparse rows reuse their
buffers. Dense scans reserve blocks of at most 64 positions. Counters survive
errors. Matrix calls expose no partial echelon result as success.

Optional `RowOp` provenance shares input, scaled-addition and scaling nodes.
References point backward and each output pivot refers to its derivation.
This data alone does not certify a Gröbner basis: both ideal containments,
all final S-pair reductions and reducedness remain separate obligations.

`Certificate.Basis` supplies shared derivations for both ideal containments and
cofactor arrays for every ordered final S-pair. The Mathlib-free `checkBasis`
validates canonical residue lists, nonzero monic reduced output, decreasing
leading order, both containments and every S-polynomial identity. It also checks
that each cofactor-times-divisor product has degree at most that S-polynomial's
actual degree, keeping zero separate from degree zero. Unrestricted ideal
identities cannot replace this bound. `HexGroebnerTheory.checkBasis_sound`
proves the complete semantic postcondition through the existing polynomial and
order correspondences. Literal examples replay in the ordinary kernel.

Pair replay validates the common basis once, and shape checking caches its
leading terms. The initial dense pair witness still occupies Θ(|G|³) cofactor
slots and checks both orientations and the diagonal. This type is provisional,
not a stable interchange format. Sparse shared pair witnesses and triangular
pair coverage remain necessary for large computations.

The pure predicates have no operational allowance. The separate
`Certificate.BasisVerification.verifyWith` wrapper validates and reserves nested
replay work, coefficient products, degree comparisons, shared derivations,
term storage and certificate nodes/pairs before invoking `checkBasis`. Repeated
preflight work is charged on resumption. Compressed S-pair derivations remain
required. Candidate timing excludes certificate production and replay.

`divideWith` performs exact ordered division on canonical natural-residue term
lists and returns explicit quotients plus an irreducible remainder. Divisors
need not form a Gröbner basis; zero divisors are skipped and nonmonic divisors
use exact prime-field inverses. Independent `Certificate.checkDivision` replay
checks reconstruction, irreducibility and product-degree bounds before success.
`Certificate.Division.computeWith` separately exposes unchecked division
candidates. Quotient and remainder terms accumulate in reverse and undergo
one final balanced normalization. This list-based certificate route is separate from packed F4 hot
loops. `normalFormWith` requires a `CheckedBasis` and yields the unique normal
form in the original ideal coset. Positive queries compose the accepted
containment and checked division proofs, avoiding repeated evaluation of the
forward derivation; the standalone checker remains independent. `memberWith` distinguishes membership with
explicit cofactors against that accepted basis and a standalone composed
certificate against the original generators from a checked nonmembership
witness with nonzero normal form. `checkMember` accepts direct shared derivations or a forward containment with
explicit zero-remainder cofactors;
`checkNonmember` checks the complete basis and division witness.
`Certificate.Derivation` stores direct nodes and a result root; wrap it with
`Certificate.Member.derivation`. `Certificate.Member.combination` specializes
in standard zero-remainder representations and shares a forward containment.
Direct derivations also support arbitrary cofactor identities with cancellation.

`Certificate.Budget` counts cumulative scalar/coordinate work, attempted
division steps, certificate nodes and pairs. `allocatedBytes` and
`allocatedTerms` are cumulative logical allocation allowances, including input
and temporary payload; they measure neither live nor peak memory. It also
bounds variables and exponent bits. Logical bytes reserve list
cells, exponent limbs and auxiliary payload, excluding allocator capacity,
call stacks and general runtime control objects. Exponent width is an
allowance: 81-bit exponent inputs work when the allowance is raised. Natural
size arithmetic is checked before allocation. Addressability checks apply to
single allocations separately from cumulative allocation counters. Production, reconstruction replay and membership classification
consume the same parent allowance. `resumeDivideWith`, `resumeMemberWith` and
basis replay retain sealed input/field/order identity and consumed counters;
production retains committed division transitions. Replay preflight is atomic
and retains identity and counters, rather than a validated prefix; retrying it
charges repeated work and allocation. Node/pair caps count witness structure
once, including across retries. Basis-replay continuations retain the parent
baselines. Membership applies the caps to all returned certificate data,
including pointer-shared forward/backward derivations and final pairs. Low-level `verifyFrom` helpers accept caller-supplied
parent counters, which callers must preserve across nested operations. Invalid
input, rejection, exhaustion and arithmetic invariant failure remain distinct.
Completed checked receipts carry actual Boolean acceptance proofs. Compiled
verification and downstream kernel checking remain separate stages.

`basisWith context limits generators` accepts canonical natural-residue
polynomials in descending lex storage; `context.order` selects the mathematical
order independently. Coefficients are nonzero and below the explicit prime.
`certifyWith` takes an additional candidate in the same format. Its accepted
receipt is indexed by the exact original context, generators and candidate;
no producer metadata can substitute a different ideal. Access the receipt's
`value` to use its `CheckedBasis` with normal forms and membership.

`BasisLimits.computation` controls F4 shape, matrix, pair and round allowances.
`BasisLimits.certificate` controls certificate work, cumulative logical
allocation, term slots, division steps, nodes/pairs and exponent bits. Both
phases use the smaller work, allocation and variable cap, including input
conversion and final receipt construction. Completed F4 history is retained
through certification: lowering a consumed F4 allowance on resume still
reports exhaustion. Node/pair caps bound certificate structure; work and
allocation include failed/repeated attempts. The node allowance also bounds
the unpruned polynomial derivation during traced F4; pruning can make the final
witness smaller. Matrix input records reuse existing roots and have an
additional row-count allowance rather than consuming polynomial-node capacity.

A separate traced F4 pass constructs the forward containment using the same
packed polynomials, pair queue, reducer lookup, symbolic closure and exact
matrix elimination. Shared `RowOp` derivations become polynomial certificate
nodes. Independent tail reductions retain each target's coefficient one, so
restoring its head gives the corresponding full derivation. Original-generator
divisions construct the reverse containment, and every ordered final S-pair
gets explicit degree-bounded cofactors. A bounded reverse reachability pass
drops unused forward nodes and renumbers the retained shared derivation before
replay. Matrix provenance reserves logical bytes per operation actually recorded,
then polynomial-node construction charges its separately allocated data. Complete
independent `checkBasis` replay precedes success.

The current `certifyWith` implementation reruns traced F4 and compares its
canonical output with the supplied candidate before generating the certificate.
It does not use the external producer's seed or internal state, but still needs
a full F4 rerun within its allowance. Candidate-only certificate generation with
early shape, containment and S-pair checks remains required. Checking an existing
supplied complete certificate through `BasisVerification.verifyWith` does not
rerun F4. Rejection and exhaustion never produce a checked basis.

The traced producer is separate from the fast unchecked candidate route.
Certificate production and final replay are separately charged and reported;
these costs are excluded from existing candidate benchmark claims. Traced
input/pair/interreduction stages retain committed checkpoints. Certificate
assembly and final replay are atomic reservations: resumption keeps the
completed traced candidate and all consumed work, and repeated attempts pay
again. `resumeBasisWith` retains the original input identity through all stages.
Invalid input, rejection, F4 exhaustion, certificate exhaustion and platform
representation limits remain distinct.

The prime-field route retains its current unsigned-32-bit exponent arena.
Canonical inputs beyond that representation return an explicit exponent
representation failure; a larger certificate exponent allowance does not
silently narrow them. Wider representations, compressed/shared S-pair
witnesses and more efficient certificate production remain required.

Verification:

```sh
lake build HexGroebner +HexGroebner.Conformance +HexGroebner.MonomialConformance \
  +HexGroebner.F4Conformance +HexGroebner.DivisionConformance \
  +HexGroebner.DivisionAPIConformance +HexGroebner.MembershipConformance \
  +HexGroebner.BasisReplayConformance +HexGroebner.NormalFormConformance \
  +HexGroebner.TraceConformance +HexGroebner.CertificateProducerConformance \
  +HexGroebner.ProducerConformance \
  +HexGroebner.BasisConformance hexgroebner_emit_fixtures hexgroebner_emit_f4 \
  hexgroebner_emit_division hexgroebner_bench
HEX_LIBRARY_FILTER=HexGroebner bash scripts/ci/run_oracles.sh
lake exe hexgroebner_bench verify
```

The 175 matrix cases independently check row-space equality, reducer subspaces
and derivations with Python exact modular RREF. The oracle also checks every
unscaled independent target remainder and tracks input coefficients to ensure
its derivation contains its own target exactly once and no other target. Native/portable comparisons cover every matrix fixture, both provenance modes,
and a 5000-entry pivot spanning multiple native calls. Primitive tests cover
all coefficient widths, boundary moduli, aliasing and malformed slices. Both
compiled C arithmetic paths have standalone reference checks and sanitizer
coverage. A downstream literal row update reduces in the kernel with no
axioms. Core checks cover malformed
representations, all resource categories, inclusive boundaries, retained failure
counters, scalar/sugar metadata, scan-block extension and 100,000-column sparse
work bounds. Monomial tests force collisions, table growth and both widening
boundaries, check overflow rejection and compare packed ordering with the
lawful Hex orders. Ordinary-kernel byte decoding has an axiom audit.

The literal prime-field example shares Mathlib-free data with an exact
automatic-generation regression check. The emitter also computes and
independently certifies all 567 systems with each scheduling strategy, comparing its accepted basis with fast candidate production. The
indexed API separately certifies supplied candidates, exercises all phase
allowances and resumes sealed computations with their original input identity.

The 567-system F4 corpus has 1134 degree/sugar profiles. Exact problem and basis
equality binds the paired profiles; each unique problem is checked once by
SymPy F5B and,
when available, Singular over
seven primes and three orders. Cases include cyclic-3, Katsura-2, generated
quadratic systems, positive-dimensional systems, nonmonic inputs, raw
cancellation and ordinary characteristic-two polynomials. Oracle rejection
tests cover wrong ideals, missing S-pairs, nonmonic output, wrong orders and
false Boolean-quotient reductions. Core tests also exercise cumulative-state
resumption at every work boundary of the S-pair example, every resource
category, scalar-preserving remainders and sealed checkpoint identities. The
emitter also recomputes all 1134 profiles with batch size one and requires the
same reduced basis. It also compares shared versus separate tail reductions.
Core resume sweeps switch both pair criteria and final-reduction strategy at
every work boundary. Product/chain counters demonstrate criterion use.

The division emitter checks 1,134 ordered divisions against exact SymPy
quotients and remainders over seven fields and three orders, using both
original generator lists and completed bases. Another 154 bounded normal-form
and membership cases use independently replayed basis receipts over `𝔽₂` and
`𝔽₇`. SymPy recomputes the complete reduced bases from their original generators
and checks every normal form and membership outcome. Zero, unit, linear and
nontrivial three-polynomial bases are included. Fixture data excludes work
counters. Core tests sweep every work boundary of a nontrivial division and
of a smaller independent replay, exercise all relevant resource categories
and oversized exponents, and reject malformed division and shared-basis
witnesses. Bounded basis replay agrees with the pure checker on the complete
three-polynomial witness and its malformed-certificate variants. Ordinary
characteristic-two division retains `x² mod (x²+x) = x`.

Lean-bench registrations cover dense elimination with/without provenance,
clustered and spread sparse supports, monomial interning, and fixed cyclic-4,
cyclic-5, cyclic-6 and Katsura-3 F4 calls. Full-system timings are candidate production
through final interreduction; input generation, certification and kernel
checking are excluded. IO-backed input reads prevent cached pure fixed results.
Packed helpers require canonical workspace-owned identifiers and coefficients;
`Polynomial.remainder` operates on unchecked internal divisors and supplies no
certified membership claim. Portable accessors retain checked byte operations and `Nat` indices. Wide gaps
inside an active interval are still scanned. No performance leadership is
claimed from these kernel or candidate measurements.

Deterministic producer correctness/termination, finite-extension adapters,
elimination block orders, the full pair-coverage proof, checked probabilistic
computation, validated learning/traces, delayed reduction, additional SIMD and parallel kernels
and balanced multi-comparator acceptance comparisons remain outstanding.
Complete basis, division and both membership checkers and soundness proofs are
available; standalone pure predicates have no operational allowance.
[#10987](https://github.com/kim-em/hex-dev/issues/10987) tracks the continuing
correctness, finite-field scope and fastest-open-source requirements. No
library phase or performance milestone is claimed.

Reducer-trie traversal caches node depths and keeps node IDs alone on its stacks.
[Matched allocation measurements](../reports/bench-results/hexgroebner-allocation.md)
retain all successful and unsuccessful variants and their complete samples.

`Limits.gebauerMoller` enables minimal-LCM pair installation and proper-LCM
chain pruning by default. When a newer leading monomial divides an older one,
the older index retires from future pair generation after installation of their
connecting pair obligation. Its polynomial remains available as a reducer and
all existing queued pairs remain. Equal-LCM retirement chains require a
retirement-depth component in the outstanding pair-coverage proof.
Set the option to false at the start for the product/resolved-chain reference.
A mid-run change preserves the existing queue and retirements; it does not
reconstruct a fresh reference run. Omitted obligations remain distinct from
completed pairs, and the basis is not deleted or renumbered.
The `pairs` statistic and allowance count considered pairs: retired indices
produce no future pair attempts under GM. [Matched pair-management measurements](../reports/bench-results/hexgroebner-gm.md)
include the small-system regression and full raw samples. Full F4 invariant
and termination proofs remain required.
[Retirement measurements](../reports/bench-results/hexgroebner-retirement.md)
retain both tested data structures, per-family regressions and the matched
remaining gap to msolve.

GM installation interns LCMs even for pairs later omitted by its criteria.
Those stable monomials remain in the arena and count against `monomials` and
`packedBytes`; a GM run can exhaust an allowance that suffices for the reference
route. Native execution, pair criteria, final reduction and batch-cap controls
may change on resume; allowances remain absolute cumulative bounds. Scheduling
is fixed when the computation starts and retained by its sealed continuations.

Scheduling timing evidence currently covers grevlex only; relative lex/grlex
performance remains unmeasured. All three orders have independent correctness
coverage with both strategies.

`Limits.scheduling` defaults to `.degree`, selecting the actual critical-pair
LCM total degree; `.sugar` selects the propagated sugar degree. Both use stable
basis-index ties and process a whole priority class in bounded batches. A new
inhomogeneous pair may have lower degree than an earlier batch. Sugar remains
separate propagated metadata under both strategies.
[Matched scheduling measurements](../reports/bench-results/hexgroebner-scheduling.md)
retain work reductions, timing regressions and all samples. Pair coverage, final
interreduction and independent certification remain required.

The default batch cap is 1024; `Limits.batchSize` permits smaller or
larger caps. Degree/sugar boundaries still separate batches, and all nested
matrix/memory/work allowances remain in force. The retained
[batch comparisons](../reports/bench-results/hexgroebner-batches.md) explain the
choice and include failures, full output comparisons and variability.

Candidates report the batch cap and implementation controls supplied at
completion; earlier resumed stages may have used different controls. The
reported scheduling strategy is the original retained choice. Checked results
record that choice in `history.scheduling`.
`Statistics.largestBatch` records the largest selected pair batch, while
`peakMatrixRows` and `peakMatrixEntries` record maximum rows and logical
validated input-plus-output entries of one matrix call, including failed calls.
These are matrix-size counters, separate from process peak RSS and cumulative
matrix work.


F4 batches group multiplied basis rows by their actual critical-pair LCM.
Each group uses its sparsest participating face as a known reducer and retains
every other face once as a target. Symbolic closure preserves those pivots;
certificate production records fresh basis multiples before matrix operations.
Selected S-polynomial identities remain in the resulting row span, including
disconnected same-LCM pair components. Final certification independently checks
the complete reduced-basis contract. See the retained
[multiplied-row measurements](../reports/bench-results/hexgroebner-pair-rows.md).

## Standalone candidate computation

`lake build hexgroebner_compute hexgroebner_compute_full` builds a JSON driver from
`bench/HexGroebner/Driver` and an otherwise identical full-initialization reference.
The default uses the SDK's internal `libinitialize_minimal` archive only on the
pinned compiler revision `470d5ce1400764999581fd26d5d72b00d990b0f4`, when present.
Other compiler revisions or missing archives use ordinary initialization. CI
checks the actual linked initializer as well as complete output agreement.
The dedicated driver never elaborates Lean source or invokes its interpreter.
Its import closure must also initialize every module reachable through
extern/export calls; ordinary imports alone do not guarantee that condition.
These restrictions require review when extending the driver. Benchmark and
kernel replay executables keep their own initialization contracts.

For example, save this input as `input.json`:

```json
{"p":7,"variables":2,"order":"grevlex","generators":[[[[2,0],1],[[0,1],6]],[[[1,1],1],[[0,0],6]]]}
```

Run `.lake/build/bin/hexgroebner_compute input.json`. Terms are
`[exponents, coefficient]`; coefficients must lie in `[0,p)` and exponent-vector
lengths must equal `variables`. Orders are `lex`, `grlex` and `grevlex`. Field
bounds are checked before primality testing. The usual canonicalization and
zero/unit-ideal conventions apply, including ordinary polynomial semantics at
characteristic two.

Successful output has `kind: "unchecked_candidate"`, explicit field/order
metadata, `scheduling: "degree"` or `"sugar"`, the complete candidate basis and cumulative statistics. It is not a
checked basis receipt. Use `certifyWith` or `basisWith` for checked results.
Consumers must compare parsed JSON values: object field order and whitespace
are not part of the output contract. The driver emits `basis` after its metadata.
Malformed input, exhausted allowances, representation exhaustion and internal
matrix failures have distinct kinds: exit 2 is invalid input, 3 exhaustion,
4 representation exhaustion and 5 an internal matrix error. Uncaught IO failures
(such as a broken output stream) use the ordinary Lean process error exit, 1.
Only `kind` is a stable machine-readable discriminator; `message` is diagnostic
text. On handled failure, no partial basis is
reported as a completed candidate. The driver does not serialize resumable
states; the library APIs retain that facility.

`--help` lists options; options precede the input filename.
`--scheduling degree` is the default; `--scheduling sugar` selects sugar batches.
`--basis` and `--variables` adjust their corresponding bounds.
`--batch-size 0` selects the effective minimum batch size one. Allowances are the same absolute cumulative
`Limits` used by `computeWith`; for example `--work 1000000000` raises the work
cap. Input parsing and filesystem work lie outside those computation counters.
The deterministic driver returns random state zero without sampling.
`hexgroebner_compute_full` accepts the same inputs and options, providing a
reference for initialization and full-output comparisons.
Freeze a staged build with `python3 scripts/bench/groebner_freeze.py output-dir`.
Matched development sweeps use `scripts/bench/groebner_cli_measure.py`; its help
requires that frozen binary/source manifest, a suite and explicit output directory.
msolve comparisons require its `.libs/msolve` ELF and a clean source tree.
It retains raw samples and inputs, checks full outputs and applies no timing gate.

Import `HexGroebnerStateNative` to use the matrix continuation separately.
`MatrixState` provides an owned continuation for untraced matrix elimination.
`start` fixes the field, inputs, column map and resource limits. `advance`
returns an exact paused state or a terminal result; its phase count is bounded
by the matrix shape. Saved snapshots and input buffers remain immutable.
The 64-bit native frame admits up to 65,536 columns and input rows; other
shapes use ordinary Lean scheduling with bounded native scan/gather. The
scalar `advancePortable` is independent of those kernels. `advance_spec`
relates their Lean models; agreement with C is a tested native obligation.

The continuation has a separate native carrier. Untraced F4 matrix calls retain
the small bounded bulk frame. When it declines, calls within the native
scheduler's 65,536-column/input-row limits use the continuation; larger frames
retain the reference's bounded native scan/gather kernels.
`MatrixState.finish_reference` proves that completion returns exactly the
`Elimination.reference` result and counters for every input, budget, quantum and
provider choice. Import `HexGroebner.EliminationDispatchProof` for
`Elimination.run_spec`, which covers production dispatch without adding proof
modules to the executable import graph.
Conformance compares complete rows, metadata, intermediate states and charged
counters. `finishState_done` proves that the shape-based allowance suffices for
terminal completion, including suspended scan/gather states. Per-row scan/gather
quantum exhaustion can still produce `rowUpdate`; these quantum counts and
error boundaries match the reference, and neither implementation currently has
a proof excluding that error on validated inputs. Standalone matrix kernel
benchmarks make no full-system performance claim.

Terminal continuations retain their workspace for inspection of exact phase
state and charged prefixes. `finishState` returns this terminal state with its
workspace attached; `finishWith` extracts the result and statistics and releases
the state. Manual drivers should drop terminal-state references after extracting
the result.
The build-time `MatrixLayout` conformance check compares the listed matrix records and tags with the layout table mirrored
from `matrix_state.c`, including field names, object slots, scalar offsets
and same-type swaps.

Within the admitted 64-bit geometry, native validation admits at most
`columns+1` entries per phase, bounding charge amounts as well as reads and preserves the first error's row/entry indices
and resource prefix. Larger well-shaped rows use the checked Lean phase.
Malformed packed lengths fail before the entry loop. `validate_ok` and
`validate_error` state the corresponding successful and failed Lean model
transitions; agreement with C is checked by native conformance.

The admitted native workspace phase charges packed bytes and work before
allocating its zeroed dense and slot buffers. At most 524,288 bytes are
allocated for the admitted column/width geometry. Exhaustion retains the
exact charged prefix and leaves the previous buffers unchanged.
Every Lean workspace phase in `advanceKernels` or the exported `next` uses
`Matrix.zerosWith` for each buffer: a native zeroing call admits at most one MiB, with larger buffers falling
back to portable initialization. Address and cumulative byte/work checks precede
both allocations. `advancePortable` retains independent scalar initialization.
[Wide-frame measurements](../reports/bench-results/hexgroebner-workspace-zero.md)
report the effect separately from full-system F4 timings.

`MatrixValidation.validateFrom_zero` equates combined-cursor validation with the
reference's reducer-then-target loops, including first errors and charged
prefixes. `Native.Scan.untraced_events` proves that an untraced scalar scan produces
no derivation events. `State.valid` combines workspace geometry and the
terminal-result invariant, preserved by `next_valid`, `advance_valid` and
`finishState_valid`. `finishState_result` guarantees a stored success or error,
excluding the empty-result fallback. `finishState_schedule` proves exact whole-state
agreement for arbitrary completion quanta and either provider's Lean definition;
`finishState_resume` proves exact agreement after arbitrary bounded suspension.
`advance_one` identifies single-phase calls, and `finishState_next` supplies their
resumption corollary. Native C agreement remains separately audited and tested.
Equivalence with `Elimination.reference` remains required before integration.
Excluding per-row quantum exhaustion on validated inputs is a separate proof
obligation shared with the reference.
