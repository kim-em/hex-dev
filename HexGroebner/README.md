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
Final minimal-leading-monomial selection and tail reduction produce canonical
monic, sorted, reduced output. Empty/all-zero input produces an empty basis;
the unit ideal produces `[1]`, including zero-variable inputs. Ordinary
characteristic-two polynomials receive no implicit field equations.

Success is an **unchecked candidate**, carrying the field/order identity,
canonical interchange polynomials and explicit random state. Deterministic
execution consumes no random samples. No API promotes a candidate to a
certified result. `certifyWith`, `basisWith`, complete basis certificates and
soundness theorems remain separate work.

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
cumulative packed polynomial/matrix allocation and decoded interchange scalar
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
Native row updates operate in chunks of at most 4096 entries;
`eliminateWith (... native := false)` and `Limits.nativeRows := false` retain
the scalar Lean row-update route. Both routes
produce identical pivots, provenance and resource counters. The binding has a
transparent structurally recursive Lean body, validates all shapes and accessed
residues, and preserves original borrowed buffers when inputs alias. C code
uses little-endian scalar access, uint128 Barrett reduction when available and
exact word remainder otherwise. No ISA extension or floating point is required.
Barrett parameters are hoisted outside coefficient loops; products fit below
`p² < 2^62`.

`reduceRowsWith` instead reduces every target independently against the same
reducer echelon space. It preserves scalars, input order and zero rows; no target
becomes a pivot for another target. Final interreduction shares symbolic closure
across nonzero tails and uses this mode. `Limits.batchInterreduce := false`
retains separate tail calls. The `*Separate` lean-bench registrations compare
these routes under identical fields, inputs and allowances.

`MatrixLimits` bounds one call's columns, rows, input/output nonzeros, packed
payload, work and optional provenance nodes. Packed payload counts input,
workspace and output buffers; it excludes headers and allocator capacity, and
may count shared buffers twice. Work covers row visits, sparse updates
(including their products), dense-column visits, normalization/inversion
products and workspace bytes initialized. Monic sparse rows reuse their
buffers. Dense scans reserve blocks of at most 64 positions. Counters survive
errors. Matrix calls expose no partial echelon result as success.

Optional `RowOp` provenance shares input, scaled-addition and scaling nodes.
References point backward and each output pivot refers to its derivation.
This data alone does not certify a Gröbner basis: both ideal containments,
all final S-pair reductions and reducedness remain separate obligations.

Verification:

```sh
lake build HexGroebner +HexGroebner.Conformance +HexGroebner.MonomialConformance \
  +HexGroebner.F4Conformance hexgroebner_emit_fixtures hexgroebner_emit_f4 hexgroebner_bench
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

Complete basis/negative-membership certificates and their soundness proofs,
resource-bounded certificate production/replay (the pure `checkMember` currently
has no allowance), deterministic producer correctness and termination,
finite extensions,
elimination block orders, the full pair-coverage proof, checked probabilistic
computation, validated learning/traces, delayed reduction, SIMD/parallel kernels
and matched full-system external comparisons remain outstanding.
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
