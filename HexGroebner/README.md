# HexGroebner

Mathlib-free finite-field F4 under [the governing contract](../SPEC/Libraries/hex-groebner.md).

`Hex.Groebner.computeWith` performs deterministic prime-field F4 candidate
production. Its explicit context fixes the prime field, variable count and
lawful lex, grlex or grevlex order. Raw terms are validated, repeated monomials
combined, zero coefficients removed and supports sorted. Sugar-degree critical
pairs are held in a persistent leftist heap; product and resolved-dependency chain criteria
discard unneeded pairs. Symbolic preprocessing closes a selected batch under a
basis-specific divisibility trie and constructs one joint Macaulay matrix.
The chain test visits indexed LCM divisors; final tail reductions share one
immutable reducer index.
F4 checkpoints retain a `ReducerCache` of multiplied reducers from the same
append-only monomial arena. Stable IDs survive exponent-width changes. Field/order metadata is checked before
reuse, and the complete base payload identifies the basis polynomial. A cache
hit checks the complete base polynomial, comparing at most 4096 bytes per native
call; basis changes cannot silently reuse a different row. Sugar and certificate
derivations are rebuilt from the current basis. The private cache retains at most
16384 entries, charges eight logical key bytes per insertion and all comparison
work to the parent allowance, and shares already charged polynomial buffers.
When key storage would not fit, multiplication continues without caching that
product. Every hit also validates all product exponents against the current
arena, with at most 4096 coordinate comparisons per native call; incompatible
identifier meanings in public raw calls therefore cannot return a stale row.
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
operational counters, not predictions of elapsed time.

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
errors. Shared states copy the workspace before mutation; unique owners reuse it. Native primitives have transparent portable bodies,
check geometry before access and preserve borrowed source bytes under aliasing.
The `*Arrays` benchmarks compare complete candidates on these two routes.

`eliminateWith` accepts a fixed column count, canonical sparse reducer rows and
target rows. Columns must follow decreasing monomial order. Reducers with free
leading columns install directly; other rows scan their active interval,
extending it when a pivot introduces a later term. Empty rows bypass the dense
accumulator. Target rows reduce against reducers and earlier target pivots.
Outputs are monic echelon rows in the original column order. `fromTarget`
identifies added row-space dimension. The retained reducer rows span the input
reducer space. Pivot metadata retains the normalization scalar and propagated
sugar, allowing ordinary remainders to preserve their original coefficients.
Native scan and row-extraction calls process at most 4096 transitions or
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

The native scan dispatches once per bounded call to specialized one-, two- or
four-byte scalar loops. Scalar products use uint128 Barrett reduction when
available and exact word remainder otherwise. One- and two-byte residues use a
32-bit reciprocal; four-byte residues use a 64-bit reciprocal. Products fit below
`p² < 2^62`; subtraction uses an unsigned wrap mask.
On x86 with runtime AVX2 support, odd moduli use eight exact products at a time.
One- and two-byte coefficients use a 32-bit Barrett reciprocal: the product is
below `2^32`, so the approximate quotient is low by at most one. Four-byte
coefficients use Montgomery products. The factor alone is temporarily converted
to Montgomery form; stored coefficients remain canonical residues. For
`R = 2^32`, the unreduced numerator is below `p² + R*p < 3*2^62`, so unsigned
64-bit lanes cannot overflow and one correction suffices. Contiguous columns
use vector loads/stores; other supports use gathers and scalar stores. Narrow
gathers mask the requested scalar out of a four-byte read and require that the
entire read lies within the logical buffer. Boundary vectors use scalar updates.
A vector is validated before mutation; a malformed vector falls back to scalar handling
so the exact failure prefix is preserved. Other architectures and CPUs use the
scalar implementation. No floating-point arithmetic or global ISA flag is
required. CPU detection checks CPUID and the OS-enabled YMM state, caches the
result atomically and needs no compiler-runtime CPU model symbols.

`scripts/ci/check_groebner_rows.sh` runs the standalone native tests and the
compiled matrix harness. `scripts/ci/check_groebner_matrix.py` compares all four
SIMD/scalar and Barrett/remainder build combinations with the portable model,
including valid strided vectors and even moduli. Native call counters ensure
that the linked test implementations actually run; successful contiguous and
strided SIMD calls are counted separately at each of the three coefficient
widths. `HEX_GROEBNER_REQUIRE_AVX2=1` requires
hardware SIMD coverage. Set `HEX_GROEBNER_SANITIZE=1` for UBSan and ASan on
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
independently certifies every one of the 567
systems, comparing its accepted basis with fast candidate production. The
indexed API separately certifies supplied candidates, exercises all phase
allowances and resumes sealed computations with their original input identity.

The 567-system F4 corpus compares complete reduced bases with SymPy F5B and,
when available, Singular over
seven primes and three orders. Cases include cyclic-3, Katsura-2, generated
quadratic systems, positive-dimensional systems, nonmonic inputs, raw
cancellation and ordinary characteristic-two polynomials. Oracle rejection
tests cover wrong ideals, missing S-pairs, nonmonic output, wrong orders and
false Boolean-quotient reductions. Core tests also exercise cumulative-state
resumption at every work boundary of the S-pair example, every resource
category, scalar-preserving remainders and sealed checkpoint identities. The
emitter also recomputes all 567 systems with batch size one and requires the
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
chain pruning by default. Set it to false for the product/resolved-chain
reference. Omitted obligations remain distinct from completed pairs, and the
basis is not deleted or renumbered. [Matched pair-management measurements](../reports/bench-results/hexgroebner-gm.md)
include the small-system regression and full raw samples. Full F4 invariant
and termination proofs remain required.

GM installation interns LCMs even for pairs later omitted by its criteria.
Those stable monomials remain in the arena and count against `monomials` and
`packedBytes`; a GM run can exhaust an allowance that suffices for the reference
route. The strategy controls in `Limits` may be changed on resume, while all
allowances remain absolute cumulative bounds.

The default sugar-batch cap is 1024; `Limits.batchSize` permits smaller or
larger caps. Degree/sugar boundaries still separate batches, and all nested
matrix/memory/work allowances remain in force. The retained
[batch comparisons](../reports/bench-results/hexgroebner-batches.md) explain the
choice and include failures, full output comparisons and variability.

Candidates report the batch cap and implementation controls supplied at
completion; earlier resumed stages may have used different controls.
`Statistics.largestBatch` records the largest selected pair batch, while
`peakMatrixRows` and `peakMatrixEntries` record maximum rows and logical
validated input-plus-output entries of one matrix call, including failed calls.
These are matrix-size counters, separate from process peak RSS and cumulative
matrix work.
