# hex-groebner

Finite-field Gröbner bases by Faugère's F4 algorithm, with a production
implementation in Lean, specialized native operations, and independently
checkable certificates. The target is a state-of-the-art F4 implementation:
the fastest fully open-source implementation over finite fields, and ideally
the fastest implementation available, including proprietary systems.

This is a continuing performance requirement. A correct implementation that
matches a textbook algorithm, or beats an obsolete comparator, does not
complete the performance objective. Useful implementations may ship before
that objective is reached. Preserve the outstanding comparisons and measured
obstacles in the implementation issue. Revisit representations, generated
code and native operations as Lean compiler and runtime improvements ship.
Do not lower the objective to match a temporary compiler limitation.

## Scope and library placement

`HexGroebner` is Mathlib-free. Its namespace is `Hex.Groebner`. It depends on
`HexBasic`, `HexArith`, `HexModArith` and `HexMvPoly`, with `HexGFqField` and
`HexGF2` supplying extension-field adapters. `HexGroebnerTheory` depends on
`HexGroebner`, `HexMvPolyTheory`, `HexModArithTheory` and `HexGFqTheory`, plus
Mathlib. This document specifies both libraries.

The executable F4 implementation, field adapters, packed storage, monomial
tables, matrix construction, elimination, certificate data and Boolean
checkers belong in `HexGroebner/`. Native sources belong in
`HexGroebner/ffi/`. Mathlib ideal semantics, the Buchberger criterion,
correspondence proofs and certificate soundness belong in
`HexGroebnerTheory/`. State elementary executable invariants without Mathlib
where practical. Do not duplicate ideal theory in the executable library.

Provide these capabilities:

- Reduced Gröbner bases of finitely generated ideals over finite fields,
  including homogeneous, inhomogeneous, positive-dimensional and inconsistent
  systems.
- Direct F4 in degree reverse lexicographic, graded lexicographic,
  lexicographic and elimination block orders. Degree reverse lexicographic
  order is the primary performance target.
- Deterministic elimination and accelerated probabilistic candidate
  computation, with a checked complete-result interface.
- Polynomial division, canonical normal forms against a completed basis,
  and separate positive and negative ideal-membership certificates.
- Reusable computation state, reproducible random state, work counters,
  bounded execution and independently bounded certificate construction and
  checking.

Rational reconstruction over `ℚ`, FGLM, Gröbner walks, root enumeration,
general module and noncommutative bases, and signature-based F5 are separate
extensions. Keep monomial tables and F4 traces reusable by those consumers.
An implementation over a finite extension field is in scope, not a promise
to compute over the rationals by pretending a large prime is characteristic
zero.

Ordinary polynomials over `𝔽₂` are in scope. They satisfy neither `x² = x`
nor `x^q = x` as formal polynomial identities. The specialized Boolean
quotient representation and Boolean F4 library described in
[future work](../future-work.md#boolean-polynomial-systems) remain separate.
Here field equations participate only when explicitly supplied as generators.

## Coefficient fields and input contracts

The algebraic algorithms require executable lawful field operations and
decidable equality. Reuse `Lean.Grind.Field K` and existing Hex field
instances. Finite-field metadata and optimized encoding are additional
explicit data, not a second incompatible field hierarchy. An adapter records
the characteristic, extension degree, defining polynomial or other exact
field presentation, canonical element encoding and its inverse. Prove that
encoding preserves equality and the arithmetic used by the implementation.
Do not enumerate a field merely to establish its cardinality.

The first optimized domain is `ZMod64 p` for prime `2 ≤ p < 2^31`, matching
`ZMod64.Bounds`. Support all those primes, including characteristic two,
using coefficient-width specializations rather than forcing every residue
through a 64-bit heap object. Require actual primality evidence for field
operations. Composite moduli are invalid field inputs, even when a particular
matrix happens to have invertible pivots. Raw input can accept supplied
prime evidence or use Hex's checked primality facilities within a budget.
No unchecked Boolean flag stands for primality.
For `p < 2^31`, `Hex.Nat.isPrimeTrial` and its soundness/completeness
theorems in `HexArith` provide checked trial division. Using that
route requires no additional primality-library dependency.

Provide generic adapters for the quotient fields in `HexGFqField` with
supplied irreducibility evidence, and the packed characteristic-two fields
in `HexGF2`. Conway tables are conveniences, not a bound on supported field
presentations. Preserve the defining polynomial and basis in serialized data
and comparisons. Equal cardinalities do not make coefficient encodings
interchangeable. Every extension modulus must have positive degree as well
as supplied irreducibility evidence. Reject constant moduli, including `1`:
`GF2Poly.Irreducible 1` holds, but its quotient is the trivial ring. The
`GF2nPoly` adapter must install `GF2nPoly.fieldOfDegreePos` from the
positive-degree proof. The `HexGFqField` adapter retains the corresponding
`hf` parameter. Reject reducible moduli and invalid presentations too.

The performance programme includes larger machine-word primes and specialized
extension-field arithmetic. Add a lawful carrier or widen the existing
carrier with proofs before advertising larger modulus support. Do not
silently bypass `ZMod64.Bounds`. A generic lawful finite-field adapter remains
usable when no specialized kernel applies, with the selected route reported.
No unimplemented shared finite-field interface is a prerequisite for the
prime-field F4 implementation.

Deliver the optimized prime-field route first, then extension-field adapters
and wider-prime optimizations without changing the meaning of completed
results. Partial field coverage must be explicit in release documentation
and performance claims. It does not complete the finite-field scope.

Input fixes the number and ordering of variables, field presentation and
monomial order. Raw terms are checked for arity and coefficient range,
combined on repeated monomials, stripped of zero coefficients and sorted.
Conversions to and from `Hex.MvPoly` preserve every coefficient. Validate
serialized counts, indices, lengths and size arithmetic before allocation.

For `n = 0`, nonzero generators are constants and generate the unit ideal.
Empty or all-zero generators have the empty reduced basis. The unit ideal
has basis `[1]`. Zero generators and duplicates require no special caller
precondition. A reduced basis has no zero polynomial, every leading
coefficient is one, no monomial of one basis polynomial is divisible by the
leading monomial of another, and the polynomials are sorted by decreasing
leading monomial. These conventions make output canonical for fixed input
field and monomial order.

## Monomial orders and packed polynomials

Use `Hex.MvPoly` and its kernel term lists for interchange and certificate
semantics. The F4 hot representation is a separate compact sparse format.
Do not use `ExtTreeMap`, lists of arbitrary-precision exponents or generic
boxed coefficient arrays as the intended production representation.

An order carries the faithful total-order, multiplication compatibility,
zero-minimality and well-foundedness laws of `IsMonomialOrder`. A transitive
comparator alone is insufficient. Define block orders from ordered disjoint
variable blocks with lawful component orders, with explicit block precedence
and complete variable coverage. Reject local orders. Weighted orders require
positive weights and the corresponding laws before use. Internal column
sorting must agree exactly with the selected mathematical order.

Provide packed exponent storage with checked width selection, monomial
hash-consing, integer monomial identifiers, cached degree and hash data, and
fast divisibility tests. Hash collisions require full equality checks.
Divisibility masks may reject impossible divisors but never certify an
unverified divisor. LCM, quotient and product operations must check their
exponent bounds. Widen and re-encode, or return explicit representation
exhaustion, before overflow. Never wrap exponents or confuse a hash-table
slot with a stable monomial identifier after rehashing.

Store supports and coefficients in compact contiguous buffers, with metadata
separate where that improves access. Reuse arenas across F4 rounds. Preserve
stable identifiers across growth and clearly delimit the lifetime of
round-local identifiers. Sort supports once when constructing canonical rows
instead of repeatedly converting through the interchange representation.
Keep immutable basis data borrowed and mutable workspaces uniquely owned.

The monomial table must support batched insertion of multiplied supports,
cached product hashes where valid, reserved capacity and efficient reducer
lookup. Reducer choice considers sparsity and degree. Cache multiplied
reducers when measured reuse justifies the memory, including F4's Simplify
optimization. All caches include the field, order and basis identity needed
to prevent reuse under incompatible inputs.

## Public operations and resource limits

The names below describe the intended API under `Hex.Groebner`. Concrete
records may evolve without weakening these contracts.

| Operation | Result and contract |
| --- | --- |
| `computeWith` | A candidate reduced basis or explicit exhaustion, with advanced random state and computation statistics. A candidate is not a certificate. |
| `certifyWith` | Check a candidate against the original generators and construct a complete certificate, or report rejection or exhaustion. |
| `basisWith` | Compute and certify. Success contains the reduced basis and its accepted certificate. |
| `divideWith` | Quotients and a remainder satisfying the reconstruction identity, with every remainder monomial irreducible by the supplied divisors. |
| `normalFormWith` | The unique normal form against a certified basis. |
| `memberWith` | Membership with cofactors, nonmembership with a certified basis and nonzero normal form, or exhaustion. |
| `checkBasis` | Boolean replay of a complete basis certificate tied to the field, order and original generators. |
| `checkMember`, `checkNonmember` | Independent Boolean checks for the two membership certificate kinds. |

Invalid input, exhausted resources and rejected certificates are distinct.
An incomplete basis, an unfinished degree batch or a probabilistically
missed pivot is never a completed answer. Candidate APIs are explicitly
named and documented as unchecked. No coercion upgrades them to certified
results. Independent candidate checking must accept correctly formed results
without relying on the producer's seed, heuristics or internal state.

Limits cover memory, monomials, pairs, matrix entries, rounds, arithmetic
work, random retries, certificate size and replay work. State each unit.
Check multiplication and addition of allocation sizes for overflow. Charge
nested operations to the remaining parent allowance rather than resetting
their limits. Native bulk calls have a bounded work quantum so cancellation
and exhaustion can be observed between calls. Wall-clock cancellation is an
operational interruption, not mathematical evidence of absence.

Partial results may expose a resumable state but must retain unresolved
pairs, order/field identity and advanced random state. Resumption with
incompatible inputs is invalid. No hidden unbounded fallback follows an
exhausted call. Deterministic reference F4 has a separate termination argument
for unbounded mathematical execution.

## F4 algorithm and invariants

Implement the executable operations described by Faugère's F4 algorithm.
Maintain the evolving basis, its leading monomial ideal, a critical-pair
queue and the dependency information needed by pair criteria.

1. Normalize input generators and eliminate initial redundancies without
   changing their ideal. Create the initial critical pairs.
2. Select a degree or sugar-degree batch. Make batch size and pair limits
   configurable and report them. Fair selection must eventually process or
   soundly discard every outstanding pair.
3. Construct multiplied basis rows for selected pairs. Symbolic
   preprocessing closes their supports under required reducers and assigns
   columns in decreasing monomial order. Share repeated monomials and rows.
4. Reduce the resulting Macaulay matrix by specialized finite-field linear
   algebra. Extract rows whose leading monomials add information beyond the
   existing reducer rows. Zero reductions add no polynomial.
5. Normalize new polynomials, update the basis and pair queue, and apply
   sound redundancy and pair criteria. Each accepted new leading monomial
   lies outside the preceding leading monomial ideal.
6. When the queue is resolved, remove redundant generators, interreduce,
   make the result monic and sort it canonically.

Implement Buchberger's product and chain criteria and the Gebauer-Möller
pair installation strategy. Prove the conditions under which each pair is
discarded. Deleting a basis polynomial must preserve both ideal generation
and the unresolved-pair obligations. Degree selection and a heuristic
decision that a row is probably redundant cannot substitute for those laws.

The key algebraic invariants are preservation of the generated ideal,
correct polynomial meaning of every matrix row, correspondence of column
indices with monomials, and completeness of the resolved-pair information.
Prove strict growth of the leading monomial ideal at an insertion and use
Dickson's lemma, together with fair finite processing between insertions,
for termination. Finiteness of the coefficient field alone does not prove
termination of a polynomial algorithm.

Inhomogeneous systems support documented fair total-degree and sugar-degree
strategies, with an explicit choice retained across resumption. Total-degree
selection uses the actual critical-pair LCM degree; sugar labels remain separate
propagated metadata. A new pair may have lower degree than an earlier batch.
Neither scheduling strategy replaces pair coverage, the Gröbner-property proof
or independent final certification. Verified homogenization and dehomogenization
is another permitted route. If homogenization is used, prove the
order compatibility and dehomogenization result. Do not assume that a basis
computed in one order remains a basis after reordering the output.

## Specialized linear algebra and arithmetic

The elimination interface consumes rows with a fixed, ordered monomial
column map. Its deterministic contract is equality of input and output row
spaces and echelon form relative to that column order. Row operations may
permute rows. Column permutations must be tracked and restored before
interpreting leading terms. Rank alone is insufficient for extracting new
polynomials. Preserve enough row provenance for certification without
materializing a dense transformation matrix on every production call.

Exploit the known reducer pivots and the partially triangular block
structure of F4 matrices. Support sparse reducer rows, dense accumulators,
compact pivot tables and blocked dense operations. Choose sparse-to-dense
conversion and block sizes from measurements. A generic dense RREF call on
the entire matrix is not the intended implementation. Reuse workspaces and
avoid clearing untouched portions of a dense accumulator unnecessarily.

Specialize residue storage by modulus width. Keep coefficients in a
consistent Montgomery or Barrett representation across a round. Hoist
modulus parameters and inverse computations out of coefficient loops.
Delayed reduction must carry explicit bounds on the accumulator, the number
of products between reductions and the normalization range. Test these
bounds at width and batch boundaries. Include wide multiplication and
carry operations when the modulus needs them. A small-prime kernel must not
silently run outside its supported range.

SIMD implementations may use integer or exact floating-point arithmetic.
Floating-point kernels must specify why conversion, multiplication,
accumulation and reduction are exact for their admitted ranges. Record FMA
and rounding assumptions. Disable transformations that invalidate the proof,
including unsafe reassociation. A modular answer obtained by approximate
real arithmetic without a verified correction is not an exact kernel.

Provide multithreaded elimination with owned workspaces and bounded task
granularity. Synchronize pivot publication and preserve the algebraic result
despite scheduling differences. Single-thread performance remains a separate
requirement. GPU support is an optional route to the overall performance
goal, justified by full-call measurements including transfer and setup costs.
It must not become a dependency of the portable library.

## Probabilistic computation and traces

Provide deterministic elimination as a complete reference and production
fallback. Accelerated candidate computation may reduce random combinations
of row blocks to exploit low rank and avoid repeated reductions to zero.
Use explicit reproducible pseudorandom state, advance it across retries,
and record parameters and seeds. Correctness of a certified result is
independent of any probability estimate or assumption about the generator.

For probabilistic row selection, output rows remain in the input row space
but need not span it. Expose that weaker contract honestly. Certify that no
necessary relation was omitted, or verify the resulting basis independently.
On rejection, retry with advanced state, enlarge sampling, or use
deterministic elimination within the remaining allowance. `basisWith` must
never return a probabilistic candidate as certified success. A Las Vegas
route requires exact final verification. A Monte Carlo route remains only
in the explicitly unchecked candidate API.

The error-bound and Las Vegas constructions in Demin's paper in the
references are implementation references. State the actual sampling model
before applying a probability bound. Do not infer rank preservation from one
zero random combination or import a guarantee for uniform samples into an
unrelated pseudorandom distribution.

Support learning and applying F4 traces for repeated systems with compatible
support, including later multi-modular consumers. A trace records selected
pairs, symbolic rows, monomial maps and usable pivot information. Check
field/order/support compatibility and every algebraic condition whose failure
would invalidate reuse. Unlucky pivots, changed cancellations and new support
require rejection or renewed symbolic work. A trace from a successful run is
neither a Gröbner certificate nor a proof for another input.

## Certificates, checking and headline theorems

Let `F` be the original generators and `G` the proposed reduced basis,
interpreted in `K[x₁, …, xₙ]` in the chosen global monomial order. A complete
basis certificate establishes all of the following:

1. Every `g ∈ G` is a polynomial combination of `F`.
2. Every `f ∈ F` is a polynomial combination of `G`.
3. Every S-polynomial of two distinct nonzero members of `G` reduces to zero
   by `G`, using the LCM and leading coefficients in the chosen order.
4. `G` satisfies the reduced, monic, sorted output conventions above.

The two containment directions are essential. S-pair checks alone accept a
basis of the wrong ideal. Containment alone does not establish that division
decides membership. Checking solutions at some or all finite-field points
does not establish equality of formal polynomial ideals.

Represent polynomial identities by cofactors or a shared acyclic derivation
of add, scale and monomial-multiply operations. Validate node order, every
index and every referenced polynomial. S-pair witnesses may be leading-term
division traces: each step checks the nonzero divisor, leading monomial
divisibility, coefficient quotient and exact subtraction, terminating at
zero. An alternative standard representation must enforce the monomial
bounds required by Buchberger's criterion. An arbitrary ideal-membership
identity for an S-polynomial is insufficient, since such an identity always
exists even for a non-Gröbner generating set.

The initial independent checker may inspect every final S-pair. Compressed
pair-criterion certificates and shared zero-reduction traces may avoid that
cost only with their own soundness proofs. Do not claim that candidate
production time includes complete verification when it does not. Derivation
recording, backward slicing and a separate certificate pass should avoid
carrying expanded cofactors through every arithmetic operation. Certificate
size and proof replay are performance requirements in their own right.

`checkBasis` is a pure Boolean function of explicit literal data. Its kernel
path uses ordinary field encodings, exponent lists and polynomial term lists
with transparent arithmetic. It must not call a native-only provider or
rerun F4. Native acceleration of its compiled execution does not replace
kernel reduction when constructing a proof. Use a proved `@[csimp]` equality
when runtime and kernel implementations differ, except for the explicitly
approved native primitives below. Preserve a kernel-reducible specification
body for every such primitive used by replay.

The correspondence with Mathlib includes the order, not just the polynomial
ring. Construct `toMonomialOrder : MonomialOrder (Fin n)` from each
`Hex.IsMonomialOrder cmp`, using `HexMvPolyTheory.monoEquiv` on exponent
vectors. Prove that `cmp a b = .lt` exactly when
`toMonomialOrder.toSyn (monoEquiv a) < toMonomialOrder.toSyn (monoEquiv b)`.
Prove agreement of leading monomials, leading coefficients, divisibility,
LCMs and S-polynomials under the polynomial conversion. The existing ring
equivalence alone does not establish these order-dependent statements.

Supply `IsGroebnerBasis` for the converted polynomial family and order: every
nonzero polynomial in the generated ideal has leading monomial divisible by
the leading monomial of some nonzero family member. Prove its equivalence
with Buchberger's S-pair criterion and prove reduced-basis uniqueness. Reuse
Mathlib's monomial-order division results where applicable. Obtain the
ascending-chain condition for monomial ideals from Dickson's lemma, using
the `Finsupp` partial-well-order results. These are explicit obligations of
`HexGroebnerTheory`, not consequences of the ring equivalence.

`HexGroebnerTheory` supplies the following named theorem contracts, with all
field, order and representation hypotheses explicit:

- `checkBasis_sound`: acceptance implies that `G` is the reduced Gröbner
  basis of the ideal generated by `F` in `MvPolynomial (Fin n) K`.
- `basisWith_sound`: every successful checked computation satisfies that
  same postcondition, with no producer-provenance hypothesis.
- `f4_spec`: deterministic mathematical F4 terminates and returns that
  reduced basis. Resource-limited execution has sound successful results,
  not a promise to finish within arbitrary limits.
- `normalForm_spec`: division by an accepted basis gives the unique
  irreducible representative modulo the input ideal.
- `checkMember_sound`: accepted cofactors prove ideal membership without
  requiring a complete basis.
- `checkNonmember_sound`: an accepted complete basis, exact reconstruction
  `h = Σ qᵢ gᵢ + r`, irreducibility of `r` and `r ≠ 0` prove nonmembership.

Prove or reuse the Buchberger criterion, reduced-basis uniqueness and the
monomial-ideal termination results in the theory library. Consult the pinned
Mathlib and upstream work before developing missing results. Transport through
the existing `HexMvPolyTheory` equivalence instead of introducing another
meaning for the same polynomials. Checkers reject malformed certificates and
never accept based only on a native success bit. No new axiom or
`native_decide` is allowed.

For end-to-end proof production, apply the soundness theorem to an explicit
certificate and a kernel-checked proof that its Boolean check is true.
Provide resource bounds before constructing large proof terms. If replay
exceeds its budget, report proof-production exhaustion while retaining any
separately identified native result. Native checking alone is not a Lean
kernel proof. Kernel examples and replay benchmarks must import only the
modules required by their actual result.

## Approved native operations and compiler evolution

Useful `@[extern]` implementations are explicitly allowed for this library.
The authorization covers the operation families below, including their
batched, blocked and parallel variants. It is not restricted to scalar
arithmetic, and does not require waiting for a compiler improvement.
This is the explicit family-level authorization recognized by
[the project proof policy](../SPEC.md#project-wide-proof-policy).
Bindings within these families need no separate SPEC amendment or approval.
Document each binding's precise contract alongside its implementation.

| Operation family | Native contract | Portable behavior |
| --- | --- | --- |
| Packed buffers | Allocate, reserve, read, write, copy and fill typed contiguous scalar storage. Preserve logical elements and ownership. Validate lengths and offsets. | Lean definitions over the logical sequence, with byte-backed or other portable compiled storage. |
| Monomial operations | Packed comparison, equality, divisibility, product, quotient, LCM, hashing and batched table insertion. Respect exponent bounds and exact collision handling. | The same exponent-vector and table operations in Lean. |
| Finite-field arithmetic | Wide products, carry operations, exact SIMD multiply-add, normalization, delayed reduction, inversion and extension-field operations. Respect the admitted field and range. | Lawful Lean field operations and bounded accumulators. |
| Matrix operations | Sparse scatter, scaled row addition, dense block update, pivot search, triangular solve and exact block or matrix elimination. Preserve the declared row-space and column-order contracts. | Deterministic sparse/dense elimination in Lean. |
| Probabilistic matrix operations | Form combinations and propose pivots or reduced rows. Return data satisfying only the stated candidate contract until checked. | Lean computation of the same proposals, followed by the same exact verification. |
| Allocation and scheduling | Aligned arenas, workspace reuse, prefetch hints, CPU feature dispatch and parallel bulk execution. Preserve observable mathematical results. | Ordinary allocation, no-op hints, scalar kernels and serial execution. |

Each binding must document its exact argument and result representation,
range preconditions, aliasing rules, platform assumptions and fallback. Pure
operations have actual kernel-reducible Lean bodies. Resource-owning IO/ST
buffers require a logical sequence interpretation and checked lifetime rules.
A C implementation's agreement with its Lean body is an audited native
implementation obligation, not established merely by proving a theorem about
the Lean body. Include native-versus-portable conformance tests. A bound
whose native violation could corrupt memory must be enforced before the call.

An explicitly seeded probabilistic algorithm can be a pure function with a
Lean body. Its native implementation must agree with that logical function,
including the returned data and advanced random state. Producing a different
echelon matrix with the same row space is not by itself agreement with a pure
Lean function's result. Use an explicit IO operation or an untrusted candidate
provider when implementation-dependent choices require that distinction.

An optional external provider that proposes candidates without implementing
a specified Lean function follows the project's untrusted-dispatch rule:
its hook is `opaque`, returns data only, and is absent from the kernel replay
path and all proof assumptions. Validate its ABI and returned shapes. Its
output reaches a completed result only through `checkBasis` and
`checkBasis_sound` (or the membership checker and soundness theorem for that
result kind). Absence or rejection uses the native Lean algorithm within the
remaining budget. Never assert equality with a pure fallback merely because
both outputs are candidates. Seeded pure kernels are not automatically
optional-provider hooks.

Bulk mutation acquires unique ownership once and borrows immutable inputs.
Overlapping views require explicitly supported semantics or rejection. Do not
invoke undefined C aliasing, alignment or integer-overflow behavior. Dispatch
by actual CPU features and retain a scalar route on unsupported machines.
GPU absence, unavailable SIMD and unavailable huge pages are ordinary
capability choices, not invalid mathematical input.

Keep F4 selection, symbolic preprocessing policy and basis management in Lean.
All shipped native sources and required build inputs must be available under
the project's compatible open-source licensing. Calling a proprietary F4
engine, or merely wrapping another complete F4 executable, does not meet the
implementation objective. Native row or matrix kernels are allowed. No extern
may manufacture a proof or merely trampoline into its Lean fallback.

Follow [the FFI conventions](../../PLAN/Conventions.md#ffi) for native carrier
modules, `moreLinkObjs`, exported symbols and Windows linkage. A native
carrier owns declarations binding the symbols and must not create a cyclic
import into its consuming library. Enable `precompileModules` only for the
executable library or carrier that needs these externs loaded during
elaboration. Never enable it on the Mathlib theory companion.

Packed scalar arrays, efficient borrowed slices and unique mutation, bulk
SIMD access, wide arithmetic intrinsics, and generated-loop optimization are
the compiler/runtime requirements to pursue. Keep their use behind stable
library operations so each can replace a local native implementation without
changing the algebraic API or certificates. Record upstream requests and
reproducible generated-code or allocation examples in the implementation
issue. On compiler upgrades, compare before and after on unchanged inputs,
remove native workarounds when the replacement is measured to be competitive,
and retain native kernels where they remain useful. Upstream delivery is
not assumed to make all remaining performance differences disappear.

## Conformance and adversarial cases

Use [the shared conformance framework](../testing.md). Add
`conformance/HexGroebner/{Conformance,EmitFixtures}.lean`, committed fixtures
under `conformance-fixtures/HexGroebner/`, and independent oracle code under
`scripts/oracle/`. Extend the existing oracle runner and existing CI job.

The `core` profile has oracle `none` and mode `always`. Singular is the
independent basis oracle. Use the shared CI job's Singular dependency.
Use mode `if_available` for the CI oracle profile, recording a skip if it is
absent, and mode `required` for manual oracle validation. Declare these modes
and covered operations in the conformance module docstring. No Sage or Julia
installation is required by this library's CI checks.

Use Singular to compute canonical reduced bases over prime and explicitly
presented extension fields. Additional msolve and Groebner.jl correctness
comparisons run manually alongside their comparator sweeps, with their
requirements checked explicitly. Transport coefficients through an explicit
presentation isomorphism for extension-field comparisons. Oracle comparison
includes the whole canonical basis, division identities and normal forms,
not just dimension, leading degrees or sampled zeros. Add small exhaustive
finite-field cases without confusing equality of functions with equality
of polynomials.

Required families include homogeneous and inhomogeneous systems, positive
dimension, elimination blocks, sparse and dense inputs, empty and unit ideals,
zero variables, duplicate and zero generators, nonmonic inputs, and changes
of term order. Cover `p = 2`, small odd primes, 16-bit boundaries and primes
near `2^31`, plus odd- and even-characteristic extension fields.

Adversarial checks must corrupt each certificate obligation independently:
wrong input ideal, missing S-pair, unbounded S-pair representation, nonreduced
output, false membership, false nonmembership, cyclic derivation, bad index,
incompatible field/order and stale trace. Include the generating set
`[x² - y, x*y - 1]` in degree reverse lexicographic order with `x > y`:
the S-polynomial of these two generators is an input-ideal combination, but that fact alone
does not make the two generators a Gröbner basis.

Force hash collisions, table growth, exponent widening, maximal accumulation
lengths, sparse/dense crossover, random rank loss, retries, cancellation and
every exhaustion category. Compare native and portable kernels, deterministic
and checked probabilistic results, and single- and multithreaded results.
Kernel tests use downstream modules with literal certificates and ordinary
`decide`. Exercise prime-field and extension-field soundness theorems and
audit their axiom dependencies.

## Performance evidence and acceptance

Follow [benchmarking](../benchmarking.md). Use lean-bench for Hex scaling and
fixed inputs, with Mathlib-free drivers under `bench/HexGroebner/`. Use manual
cross-system sweeps for external comparisons. CI runs bounded correctness
verification, not timing-sensitive scientific campaigns.

Measure the following independently where the result informs a decision:

- Monomial insertion, multiplied-support construction, divisibility lookup
  and symbolic preprocessing, including allocation and rehashing costs.
- Sparse/dense row updates, delayed reduction and blocked elimination,
  varying matrix shape, density, rank defect and modulus width.
- Full F4 candidate production through the canonically interreduced basis.
- Certificate production, independent native checking and kernel proof
  checking. Report their costs separately and in complete checked calls.
- Repeated compatible systems with trace reuse, extension-field arithmetic,
  and parallel scaling at explicitly fixed thread counts.

Do not claim a polynomial time law in the number of variables for general
F4. State kernel operation-count models in dimensions, nonzeros and rank,
and use fixed full-system problems for comparisons whose matrix sequence
cannot be predicted independently of the computation.

The corpus includes cyclic, Katsura, eco, noon, Reimer and MinRank families,
random dense quadratic systems, sparse structured systems, and elimination
and positive-dimensional examples. Include the hard public GamBa examples
when feasible, including cyclic-9/10, Katsura-14/15 and eco-14/15. Compare
small primes such as 32003 and large primes such as `2^31 - 1` separately.
Specify input files, seeds, variable order, monomial order, basis reduction
conventions and source hashes. Fix the balanced corpus and measurement
protocol before tuning against it. Keep additional held-out inputs to detect
overfitting.

The minimum external comparator set is msolve, Groebner.jl, Giac and Singular
for their supported routes, supplemented by any faster fully open-source F4
implementation. GamBa, Magma and FGb are performance targets wherever usable.
Verify licensing and source availability for the exact compared version.
A partially published implementation remains a speed comparator even when
it cannot qualify as fully open source. Published author timings motivate
tests but are not substitute measurements on the same host.

Use matched coefficient fields, outputs, thread counts, instruction-set
availability and comparable deterministic or probabilistic guarantees.
Report candidate-only Monte Carlo comparisons explicitly alongside checked
results. Never compare a competitor's entire solving pipeline with Hex's
grevlex basis production alone. Include conversion, parsing and setup costs
consistently, or state and measure the separately excluded costs. Compare
optimized builds of supported versions and retain the invocation and flags.

The fastest-open-source milestone requires no reduction in solved-instance
coverage under matched resource limits and a family-balanced geometric mean
of paired runtime ratios strictly below one against each fully open-source
comparator on the fixed suite. For each comparator, compute the geometric
mean of Hex/comparator time ratios on jointly solved inputs within each
family, then the geometric mean of those family values with equal family
weights. This is the primary speed criterion. Report per-family and
per-instance results, total elapsed time and solved-count and cactus
summaries as secondary evidence, including all failures. A geometric mean
that hides timeouts is not success. Report substantial losses and peak
memory separately.
No finite corpus establishes universal dominance. State the precise domain
and hardware for every leadership claim.

The overall-fastest goal applies the same discipline to GamBa, Magma, FGb
and future competitors. Single-thread leadership and equal-thread parallel
leadership are separate claims. Beating a single-thread competitor with
more threads is useful but does not establish single-thread leadership.
Performance targets move with competitors and compiler releases. Keep the
implementation issue open until correctness, finite-field scope and the
fastest-open-source milestone are demonstrated. Record remaining gaps when
useful intermediate PRs land, including the gap to the overall-fastest goal.
Subsequent regressions or a faster comparator require renewed work rather
than weaker comparisons. Report paired variability and do not claim leadership
from inconclusive differences.

Collect on the shared host with automatically selected CPU affinity when
supported. Adjacent comparisons alternate AB/BA. Retain every completed
sample, host activity and all seeds. Allow at most one unchanged repeat
after an inconclusive run. Do not use best-of-three selection, quiet-core
preflights or contamination-based sample removal. Commit comparator-sweep
records under `reports/bench-results/`, with content fingerprints and
measurement manifests following
[figure freshness](../benchmarking.md#figure-freshness). Published figures
must identify the records and source fingerprints used to generate them.
Declare any mechanically enforced figure family under that shared policy.
Written reports under `reports/` are optional. Retain source, toolchain,
compiler and ISA identity, elapsed time, peak memory, round/pair/matrix
counts, reduction work and certificate sizes. Attribute unexpected gaps before choosing between
algorithm changes, representation changes and compiler/runtime requests.

## Documentation and completion

Document the field and order contracts, unchecked versus checked results,
budgets, native assumptions, portability and reproducibility. Include a
prime-field example computing a basis and checking membership and
nonmembership, an explicit finite-extension example, and an elimination
example. Show a case where omitting a final S-pair would give a wrong answer.
Theory examples begin with Mathlib polynomial and ideal statements and keep
the conversion to Hex data inside the proof.

Implement incrementally with actual F4 operations and intended complexity.
Follow the project phase checks. Useful intermediate functionality may ship
with explicit measured limitations.
Correctness completion requires the headline theorems and the conformance
suite. Performance completion additionally requires the evidence above.
Neither a placeholder Buchberger loop nor permanently delegating the whole
computation to another CAS meets this SPEC.

## References

- Faugère, [A new efficient algorithm for computing Gröbner bases
  (F4)](https://doi.org/10.1016/S0022-4049(99)00005-5), 1999.
- Faugère and Lachartre, [Parallel Gaussian Elimination for Gröbner bases
  computations in finite fields](https://hpac.imag.fr/gbla/data/bib/FaLa10.pdf),
  2010, and [GBLA](https://github.com/ederc/gbla) for specialized matrix
  representations and elimination.
- Berthomieu, Eder and Safey El Din, [msolve: A Library for Solving
  Polynomial Systems](https://arxiv.org/abs/2104.03572), and
  [msolve sources](https://github.com/algebraic-solving/msolve).
- Demin and Gowda, [Groebner.jl: A package for Gröbner bases computations
  in Julia](https://arxiv.org/abs/2304.06935), and
  [Groebner.jl sources](https://github.com/sumiya11/Groebner.jl).
- Demin, [Probably correct row echelon form in the F4
  algorithm](https://arxiv.org/abs/2609.14433), for probabilistic elimination,
  error bounds and a Las Vegas construction.
- [GamBa](https://github.com/gblanco92/gamba), including its public
  monomial, matrix and field implementation and benchmark inputs.
- [Magma's Gröbner-basis implementation](https://magma.maths.usyd.edu.au/magma/info/topic_gb)
  and [dense F4 and Boolean options](https://docs.magma-maths.org/CommutativeAlgebra/GrobnerBases/groebner.html).
- [Lean boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/),
  [reference counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/)
  and [FFI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/).
