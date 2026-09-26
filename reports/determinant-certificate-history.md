# Archived polynomial determinant certificate design

This report preserves the superseded design and its measurements. It is not
a requirement for the symbolic determinant implementation. The authoritative
contract is [hex-poly-det-mathlib](../SPEC/Libraries/hex-poly-det-mathlib.md).

The sources below are the SPECs at revision `cd58c3e0449b7f70ef402d82d2568b2bac593faa`. Historical claims and
implementation notes describe that revision, not the replacement.


---

# hex-poly-det (determinants of polynomial matrices, depends on hex-bareiss and hex-mv-gcd)

The determinant of a matrix with multivariate polynomial entries, certified
by [hex-bareiss](../HexBareiss/SPEC/hex-bareiss.md)'s polynomial
determinant certificate instantiated at the carrier `MvPoly k C cmp` with
hex-mv-gcd's exact quotient. This is the determinant analogue of
[hex-generic-rank](../SPEC/Libraries/hex-generic-rank.md) and exists for the same reason:
`HexBareiss` cannot depend on `HexMvGcd`, and `HexBareissMathlib` is a
published mirror whose import closure may not reach the unpublished
hex-reflect and hex-mv-gcd, so the instantiation and the symbolic `det`
arm live in an unpublished pair above both. The companion
[hex-poly-det-mathlib](../SPEC/Libraries/hex-poly-det-mathlib.md) owns the symbolic `det`
handler, its soundness and its proof probes.

The determinant algorithm and witness are hex-bareiss's generic ones
([hex-bareiss §Polynomial determinant certificate](../HexBareiss/SPEC/hex-bareiss.md#polynomial-determinant-certificate)),
the exact quotient is hex-mv-gcd's, and the list arithmetic is
hex-mv-poly's. A second checker uses hex-kronecker's packed products on
the same witness.

## Scope and dependencies

In scope: `polyDetWitness` and `polyDet` over `MvPoly k C cmp` for a
coefficient domain `C` with `LawfulGcdOps C`; the checked `polyDetWitness?`
that returns the witness only when `checkDetPolyList` accepts it in
compiled code; the list-form instantiation of the checker with
hex-mv-poly's canonical arithmetic and `checkDetPolyPacked` with
hex-kronecker's product checks; conformance fixtures with a SymPy
oracle; and lean-bench families. This library supplies executable
instantiation and checking only. The theorem that a passing check means
`Hex.Matrix.det P = d` (`checkDetPolyList_sound`) and producer correctness
(the producer's witness passes) are both the companion's, as for
hex-generic-rank; hex-bareiss's own SPEC excludes that proof surface from
the Mathlib-free layer.

Out of scope: reification (hex-reflect), any statement about a specialised
matrix (the companion), and univariate `F[x]` matrices, whose determinant
the `DensePoly` carriers of hex-bareiss's carrier table already cover.

Dependencies: `HexBareiss`, `HexMvGcd` (hence `HexMvPoly`, `HexResultant`),
`HexDeterminant`, `HexMatrix`, `HexBasic`, and `HexKronecker`, downward in the
DAG. The library remains Mathlib-free and unpublished.

## The instantiation

```lean
namespace Hex.PolyDet

variable {k : Nat} {C : Type u} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C] [DecidableEq C]
  [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [IsMonomialOrder cmp] [LawfulGcdOps C]

/-- hex-bareiss's generic polynomial witness producer at the multivariate
polynomial carrier, with hex-mv-gcd's exact quotient. -/
def polyDetWitness (P : Matrix (MvPoly k C cmp) n n) : Except String (DetWitness (MvPoly k C cmp)) :=
  Hex.Matrix.detWitnessWith Hex.exactDiv n (check n) (P.rows.toList.map (·.toList))

def polyDet (P : Matrix (MvPoly k C cmp) n n) : MvPoly k C cmp
def polyDetWitness? (P : Matrix (MvPoly k C cmp) n n) : Option (DetWitness (MvPoly k C cmp))

def produce (budget : DetWitness.Budget) (n : Nat)
    (check : List (List (MvPoly k C cmp)) → DetWitness (MvPoly k C cmp) → Bool)
    (rows : List (List (MvPoly k C cmp))) :
    Except DetWitness.Error (DetWitness (MvPoly k C cmp))
```

`Hex.Matrix.detWitnessWith` is generic over entry arithmetic, with the
integer API retained as a specialisation. The witness type is `DetWitness R`;
its matrix dimension and row shapes are checked by the list checker.
`polyDetWitness?` returns the witness only when the list-form check accepts
it in compiled code; its kernel encodings are integer and residue
coefficients, so its initial carriers are `Int` and `ZMod64 p`, and `Rat`
enters only through the companion's row-scaling arm, which checks integer
lists.

`Hex.PolyDet.produce` in `Basic.lean` instantiates `Hex.Matrix.detWitnessBudgeted` with
`MvPoly` support cardinality as its size measure, for both integer and
residue coefficient domains. Its intermediate budget governs round admission
by term-product counts and the total support of the retained blocks after
each round, as specified in hex-bareiss. Its certificate budget is checked
before the compiled self-check. Structured declines preserve the exhausted
budget name, count reached and limit through the frontend.
The companion calls this shared wrapper from its integer route and from
`Frontend.residueWitness?`, supplying the corresponding serialization
self-check. The unlimited `polyDetWitness` API and its error type stay intact.

The exact quotient and its law are `Hex.MvPoly.instDiv` and
`Hex.MvPoly.instExactDivLaws` from `HexMvGcd/Divide.lean`, under
`[LawfulGcdOps C]`, which `HexMvGcd/Instances.lean` supplies for `Int`,
`Rat` and `ZMod64 p` (under `ZMod64.Bounds p` and `ZMod64.PrimeModulus p`);
the term order is fixed at `Hex.Mono.grevlex`. The witness is over the
polynomial ring: the transform rows and the value `det P` for a
nonsingular matrix (nonzero polynomial determinant), or a nonzero left
kernel vector over the polynomial ring with value zero when `det P` is
identically zero. No specialisation chooses or certifies the branch.

The kernel form is `checkDetPolyList` instantiated with hex-mv-poly's
canonical term-list operations: coefficients `Int` for the integer
carrier, canonical `Nat` residues for the residue carrier through
`Hex.PolyDet.opsMod`, and exponent vectors as `List Nat`. Every modular
operation comes from `HexMvPoly.KernelResidue`. Its soundness is the companion's.

## Packed certificate

`Hex.PolyDet.checkDetPolyPacked` returns `Bool` and takes a
`MulMode`, atom count `k`, dimension `n`, canonical
integer polynomial row lists, and the same `DetWitness (PolyList Int)` as
`checkDetPolyList`. It replaces only the product identities with
[`Hex.Kronecker.Kernel.mulTerms`](../HexKronecker/SPEC/hex-kronecker.md#kernel-evaluation)
after elaborator preflight; resource reports and budget comparisons are not
kernel replay. The kernel-facing form has no resource budget argument.
Canonicality, exponent arity, matrix and witness shapes, swap validity,
nonzero transform diagonals or a nonzero singular vector remain checked in
the kernel. Nonzeroness is a canonical polynomial test, never a test at the
packed point or at the user's atom valuation.

The product inputs are determined by the witness, without another matrix
payload. For `.triangular swaps T d`, let `P` be the input rows permuted in
swap order, and `lᵢ := Tᵢ[i]`. Require exactly `n` transform rows, with row
`i` of length `i + 1`, each `lᵢ ≠ 0`, and `l₀ = 1` when `n > 0`. For each
`i < n`, use a `1 × (i + 1)` row `Tᵢ` and the leading
`(i + 1) × (i + 1)` submatrix of `P` in `Kernel.mulTerms`. Its result row is
`[0, …, 0, uᵢ]`, where `uᵢ := lᵢ₊₁` for `i + 1 < n` and
`uₙ₋₁ := sign(swaps) * d`. Thus it checks exactly the zero products below
the diagonal and the adjacent-diagonal identities of
`HexBareiss/Polynomial.lean`; entries above the product diagonal are not
computed. For `n = 0`, require empty transform and swaps and `d = 1`.
For `.singular v`, require length `n` and a nonzero entry, and check
`[v] * A = [0, …, 0]` with dimensions `1 × n`, `n × n`, `1 × n`.
The singular witness cannot pass at `n = 0`.

`checkDetPolyPackedTree` accepts the same list-valued witness and an input
matrix of `Hex.Kronecker.Expr` trees. It applies the same swaps and checks
the same row-prefix or singular-vector identities through the mixed
list/tree product checker. Entries are evaluated directly at the Kronecker
point; their bounds are structural tree degrees and ℓ¹ bounds. The common
plan for each identity includes those bounds and the witness bounds. A
target tree is compared with the witness value by mixed tree/list equality,
with both operands included in its plan. The target is never expanded by
the kernel. Witness lists still require canonicality and the same nonzero
diagonal or vector checks. Keep `checkDetPolyPacked` and its modular form
for term-list certificates, including the residue route.
Its kernel-facing signature is
`checkDetPolyPackedTree (mode : MulMode) (k n : Nat)
(rows : List (List Hex.Kronecker.Expr)) (w : DetWitness (PolyList Int)) : Bool`.
All three kernel-facing determinant entry points, including
`checkDetPolyPackedMod`, omit the resource `Budget` argument; any outer
signed-packing widths are validated by the product checker.

### Bounds and selection

After compiled witness production and canonical list conversion, run
`sizeMulTerms` (or `sizeMulTree` for tree entries) on every product above before
packing or emitting any kernel
proof for the certificate. For each output coordinate the degree bound is
the componentwise maximum of `degree(Mᵢₜ) + degree(Aₜⱼ)` over `t` and
`degree(Cᵢⱼ)`; the coefficient bound is
`∑t ‖Mᵢₜ‖₁ ‖Aₜⱼ‖₁ + ‖Cᵢⱼ‖₁`. These include the input entries and the
actual witness, not just the entry degrees or atom count. Use Kronecker's
`SizeBound`, mixed-radix strides, base and saturating preflight unchanged;
no dense polynomial expansion or packed integer is built to choose the arm.
Each product check derives its own plan; its interface has no shared
plan argument. The kernel repacks entries shared by different row-prefix
products, potentially at different bases and strides. Account for that
repeated support traversal and packing, rather than assuming cached columns.

The preregistered hard limits are `maxDenseDigits := 65536` and
`maxPackedBits := 16777216`, with caller tightening allowed. Every product
must fit both limits. The separate certificate/source/proof budgets still
apply. These per-product limits bound operand sizes, not total certificate
runtime. Runtime eligibility relies on the measured sparse/packed table and
the full-certificate shipping comparison; fitting the hard limits alone
promises no win or compliance with a proof-build ceiling.

The digit condition is `∏ⱼ (dⱼ + 1) ≤ 65536`, using the product/witness
bounds above. For a uniform bound in every atom, the maximal degrees are
`65535, 255, 39, 15` at arities `1, 2, 3, 4` respectively. These are bounds
on the checked identities, not on input entries: growing minors can make a
few-atom input ineligible. Record such cases as expected preflight declines.

Above either packing limit, the whole certificate uses term lists;
there is no kernel trial of the packed checker followed by a sparse retry.
Within the limits, use the measured sparse/packed crossover table required
by [hex-kronecker §Consumers](../HexKronecker/SPEC/hex-kronecker.md#consumers), keyed by
`packedBits`, input supports and inner dimension (with result support as an
additional conservative equality key). Require an eligible entry
for every product; an absent entry selects term lists. Explicit comparison
probes may force either arm within its budgets to establish that table.
The table is fixed before consumer activation. This first interface selects
one checker for the whole witness, keeping one Bool proof and one trace
route. It accepts the overhead of small prefixes and measures it in the
full certificate. Per-product mixing is a separate extension, not an
assumed source of speedups in the initial comparison.

`MulMode.plain` is the packed default. A separate mode-selection table from
hex-kronecker's term-list-product benchmark may select `signedPacked`; its
preflight includes the outer signed-dot operands and intermediates as well as the inner Kronecker
values. A mode whose bound fails is ineligible; select one mode eligible
for every product, otherwise use term lists. Both modes denote the same
identities. The Bool checker itself revalidates shapes and bounds before
packing, so untrusted dispatch is never a soundness assumption.

After preflight selects a checker, run that same Bool in compiled code on
the exact lists and payload to be quoted, charging its work to the producer
budget. A preflight budget decline selects term lists before this step;
`false` after an accepted preflight is a certificate failure, even if the
list checker accepted the witness. It exposes a checker/serialization
inconsistency or a wrong identity rather than hiding it with fallback.
Only a compiled `true` proceeds to the single kernel check, which remains
the authority; no compiled result is used as a proof.

### Positive characteristic

`checkDetPolyPackedMod` uses `Kernel.mulTermsMod` with canonical residue
`PolyList Nat` inputs lifted coefficientwise to integers in `[0,p)`.
The `DetWitness` is unchanged. A supplemental payload supplies one integer
quotient term list per output entry of each product above: `n` quotient
rows of lengths `1, …, n` in the triangular branch, or one length-`n` row
in the singular branch (empty payload for the empty triangular witness).
Form the final signed value in the residue carrier before lifting it.

Compiled code computes `Qᵢⱼ = (∑t M̃ᵢₜ Ãₜⱼ − C̃ᵢⱼ) / p`
coefficientwise, checking exact integer divisibility. It normalizes `Q` to
canonical integer term lists; the kernel never repeats its multiplication
or division algorithm. Production is charged to the existing intermediate
term/coefficient budgets, and quotient support is included in the certificate
term budget. Budget exhaustion while preparing this optional payload
selects residue term lists; failure of exact divisibility is a rejected
certificate, not a budget decline.

The quotient-witness variant of `sizeMulTerms` includes `degree(Qᵢⱼ)`
in the componentwise maximum and adds `p * ‖Qᵢⱼ‖₁` to the coefficient
bound. The kernel checks `0 < p`, canonical residues, canonical quotients
and their exponent arity, all quotient/product shapes, and the common
bounds before checking the packed integer identity `M̃ Ã − C̃ = p Q`.
There is no base-`p` packing or reduction of a whole packed integer modulo
`p`. The polynomial producer still requires a prime coefficient domain
(`Bounds p` and `PrimeModulus p` for `ZMod64 p`). A certificate without a
quotient payload uses [the residue term-list form](https://github.com/kim-em/hex-dev/issues/10257).
A supplied malformed or incorrect payload is rejected, never silently
retried as a successful sparse certificate.

## Coefficient carriers

| `C` | `LawfulGcdOps` source | fixture family | oracle |
|---|---|---|---|
| `Int` | `HexMvGcd/Instances.lean` | two- and three-variable integer matrices: dense, structured, with pivot swaps, identically singular, and with valuations at which a nonzero determinant vanishes | SymPy `Matrix.det(method="berkowitz")` over `ZZ[x0, …]` |
| `Rat` | same | the same shapes with rational coefficients | SymPy over `QQ[x0, …]` |
| `ZMod64 p` | same, under `Bounds` and `PrimeModulus` | the same shapes at a fixed prime below `2^31` | SymPy over `GF(p, symmetric=False)[x0, …]` |

Fixtures store the realised support of the entries and the expected
determinant; emission follows hex-bareiss's `MvPoly` encoding to
`conformance-fixtures/HexPolyDet/det.jsonl`, with a tuple in
`scripts/ci/run_oracles.sh` and a handler in the existing
`scripts/oracle/matrix_carriers.py`; no new package, workflow or job.

The determinant fixture schema, expected values and SymPy oracle are unchanged:
both checker arms certify the same `DetWitness`. Packed implementation adds
kernel tests comparing both arms on integer witnesses and residue witnesses
with supplemental quotients. Include triangular and singular branches, the
empty case, budget boundaries, malformed shapes and corrupted quotients.
A characteristic-two regression rejects `[1, 1] * [1, 1]ᵀ = [x]` and accepts
the true zero result with quotient `[1]`; this guards against unsound
base-`p` arithmetic. Also test the determinant payload directly: at `p = 2`,
use `A = [[1,1],[1,0]]`, swap `(0,1)`, transform `[[1],[1,1]]` and value
`1`, with quotient rows `[[0],[1,0]]` (each scalar denotes a constant term
list). The permuted product prefixes are `[1]` and `[2,1]` over integers,
with residue targets `[1]` and `[0,1]`. Accept this payload and reject a
corrupted second quotient row. These direct checker tests do not change the
small-form handler or put quotient data in the determinant fixtures.

## Complexity and benchmarking

The producer is fraction-free elimination, `n³/3` polynomial products and
exact divisions whose cost is the realised support of the intermediate
minors, bounded as in
[hex-bareiss §Symbolic coefficient growth](../HexBareiss/SPEC/hex-bareiss.md#symbolic-coefficient-growth);
expression swell is not controlled here. The term-list checker is `n³/3`
polynomial products (or `n²` for the singular vector) at the witness's realised
support. The plain packed mode performs `∑ᵢ₌₁ⁿ i²` integer multiplications
in the triangular branch and `n²` in the singular branch. Each replaces one
term-list polynomial product with one GMP multiply; its benefit depends on
the operand bit sizes and supports. Add the repeated per-call packing cost
above. The `signedPacked` mode has its independently measured outer packing
costs and multiplication counts.

The `symbolic` family (dimensions `2, 4, 8`, atoms `1, 2, 4`, degrees
`1, 2, 4`, supports `1, 4, 16`, with infeasible support requests marked as
such) is registered in `bench/HexPolyDet/Bench.lean` (Mathlib-free), with
producer and compiled checker separate and the checker preparation holding
a precomputed witness; support and degree ladders are not one cubic model,
so each registration states its mode per
[benchmarking §Choosing the complexity claim](../SPEC/benchmarking.md#choosing-the-complexity-claim).
The report is `reports/hex-poly-det-performance.md`. There is no timed
external comparator for multivariate polynomial determinants (SymPy is the
conformance oracle, a Python process); the absence is declared as
**no-comparable-surface-in-named-comparator**.

The packed comparison uses the same precomputed witnesses and result hashes,
with preflight, support traversal/packing, integer multiplication and
quotient production reported separately. Extend the few-atom grid to atoms `1, 2, 3, 4`, degrees `2, 4, 8, 16`, dimensions
`4, 8, 16`, and include many-independent-atom declines. Measure support
traversal plus big-integer arithmetic against the packed bit size, following
hex-kronecker's complexity claim; polynomial product counts alone do not
predict elapsed time. Record every decline and all completed samples under
[benchmarking](../SPEC/benchmarking.md)'s shared-host discipline. The proof-level
comparison and default-family decision belong to the companion.

## File organisation

```
HexPolyDet/
  Basic.lean        -- polyDetWitness, polyDet, polyDetWitness?, the instance section
  Packed.lean       -- integer and residue packed checks
  PackedTests.lean  -- kernel checker, boundary, quotient, and selection tests
  Select.lean       -- compiled bounds, selection, and quotient payload preparation
HexPolyDet.lean
```

The `libraries.yml` entry is

```yaml
  HexPolyDet:
    deps: [HexBareiss, HexMvGcd, HexDeterminant, HexMatrix, HexBasic, HexKronecker]
    mathlib: false
    done_through: 3
    status: active
```

## Consumers

[hex-poly-det-mathlib](../SPEC/Libraries/hex-poly-det-mathlib.md), the symbolic `det`
handler. Applying the same packed checks to hex-generic-rank's
`checkRankPolyList` identities is a follow-on, outside this amendment.
A later polynomial-matrix library (Popov forms, approximant
bases) would import this rather than re-instantiate the certificate.

## Executable API

The implementation retains the existing numeric witness API by giving
`DetWitness` a default entry type, `Int`. Its type is `DetWitness R`;
the dimension is an explicit checker/producer argument, and every row length
is checked. `polyDetWitness` returns `Except String (DetWitness (MvPoly k C cmp))`,
`polyDetWitness?` returns its `Option`, and `polyDet` returns the existing
row-pivoted Bareiss value. A failed witness check never produces a certified
result. The companion proves `PolyDet.check_of_ok`: every successful
`polyDetWitness` return passes the checker. Errors remain possible; the theorem
does not assert that every input produces a successful result. `PolyDet.toList` performs compiled merge sorting into canonical order;
the kernel sees and validates only its output.
The companion's `produce_check` applies `detWitnessBudgeted_check` to
establish the same successful-check contract for `produce`; neither contract
claims that every input succeeds within a resource budget.

The packed entry points are `checkDetPolyPacked`, `checkDetPolyPackedTree`
and `checkDetPolyPackedMod` with the argument and payload contracts above.
Compiled quotient preparation and selection are in `Select.lean`;
its budget-decline outcome is distinct from a malformed or incorrect
certificate. The existing `polyDetWitness?` remains the list-validation API;
the handler additionally validates with its selected checker before quotation.


---

# hex-poly-det-mathlib

The symbolic arm of the `det` tactic: a second handler attached to the
`det` syntax kind that [hex-bareiss-mathlib](../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md)
owns, accepting a Mathlib matrix whose entries are ring expressions,
certifying the determinant of the reified polynomial matrix through
[hex-poly-det](../SPEC/Libraries/hex-poly-det.md), and closing `A.det = e` against the
user's expression. It is the Mathlib companion of hex-poly-det and the
determinant analogue of
[hex-generic-rank-mathlib](../SPEC/Libraries/hex-generic-rank-mathlib.md). It lives here and
not in hex-bareiss-mathlib because that library is a published mirror
whose import closure may not reach hex-reflect, hex-reflect-mathlib or
hex-mv-gcd (`scripts/release/check_released_manifest.py`,
`published_import_closure_violations`); the generic witness and checker
stay in hex-bareiss, and the numeric `det` stays in hex-bareiss-mathlib.

Dependencies: `HexPolyDet`, `HexBareissMathlib`, `HexReflect`,
`HexReflectMathlib`, `HexMvPolyMathlib`, `HexMatrixMathlib`, plus Mathlib;
not `correspondence_only`, since it implements a handler and owns proof
probes. Implementing the packed arm additionally depends on
`HexKroneckerMathlib` for product-check soundness; register that downward
dependency when the planned library is implemented. This SPEC-only amendment
changes neither the library registry nor the released manifest.

## Input and dispatch

- **Any commutative ring as the target.** Determinant transport is
  `RingHom.map_det`, which needs no injectivity, so the user's carrier `F`
  is any `CommRing`; `CharZero` is unnecessary for this transport. With integer coefficients the arm is sound
  over every commutative ring and complete over rings without additive
  torsion; in characteristic `p` a true goal can be declined when `d` and
  the target agree only modulo `p`, which the residue provider and the
  residue list form remove (for primes below `2^31`, the provider's
  range). The certificate fragment is: a square literal over any
  commutative ring whose entries and target are ring expressions in the
  same atoms, with fixed natural exponents, within the reflection budgets.
  `norm_det` followed by `ring` also closes targets that mention atoms
  absent from the matrix (`x + y - y`) and identities with variable
  exponents (`2 * 2 ^ m`), which this arm declines; those inputs are
  outside the certificate fragment. Structural proofs may accept some of
  them; otherwise Hex reports a decline without invoking Mathlib.
- **Structural dispatch.** After numeric delegation, automatic dispatch tries
  direct triangular/zero identities, common row factors, the existing formulas
  for `n ≤ 3`, bounded sparse cofactor expansion, then the polynomial frontend.
  Forced polynomial checker modes bypass the structural shortcuts. Literal
  recognition and the dimension limit remain shared. The tactic, `det%`, and
  `Hex.normPolyDet` use the same structural computation.
- **Triangular and zero identities.** Canonical zero entries are verified
  against the carrier's ring operations. Diagonal, upper/lower triangular and
  zero-row/column literals return the diagonal product or zero with a generic
  structural proof. No symbolic zero testing or polynomial expansion is needed.
- **Common row factors.** Integer coefficients times one syntactically shared
  expression per row retain the existing arbitrary-`CommRing` transport. Over
  `Rat`, recognize closed scalar multiplication/division around a row factor,
  including signs, coefficient one and zero entries. Authenticate operation
  instances and apply the existing scalar bit/exponent bounds before evaluation.
  The existing numeric determinant certificate certifies the extracted arbitrary
  coefficient matrix. Row expressions remain opaque in entry and target proofs.
  A factored target may combine closed denominators outside the product;
  scalar arithmetic and reassociation are proved over abstract row variables
  before substitution. Zero denominators have Lean's rational semantics.
  Unsupported/expanded targets use the existing frontend, without assigning
  unresolved metavariables. The term form returns the certified scalar times
  row factors in row order.
- **Closed forms.** Inputs of dimension at most three not handled structurally
  retain the existing Mathlib determinant formulas and residual `ring` step.
  The term form returns that formula with its proof.
- **Bounded sparse cofactors.** For a literal with dimension above three,
  expand a row or column with at most two entries not verified as zero. Choose
  the smallest count, breaking ties by row before column and then index. Use
  the cofactor sign for the original position and keep minor indices in order.
  At dimension four use a generic factored cofactor formula; below four use
  the existing formulas. A dense input without a qualifying sparse step does
  not enter this shortcut. Count actual scalar-product leaves in the selected
  expansion, including the terminal formulas, with a limit of 64. Check the
  shared proof-node budget during construction; exhaustion stops expansion and
  selects the polynomial frontend. Residual `ring` may compare the structural
  expression with an expanded target. If it cannot close the goal, restore the
  original goal and try the polynomial frontend; report its decline if unavailable.
- **Proof construction.** Share matrix/factor payloads and assemble applications
  with explicit arguments and expected-type hints. Count distinct proof nodes
  with the compiled shared counter, not unshared interpreted traversals for
  tracing. Structural proofs receive the existing synchronous kernel check.
- **Opt-in until measured.** The symbolic handler is not placed in the
  default `Hex.norm_det` chain. It ships as the `det` handler and
  `det%` term form for symbolic input, and enters the simp-set chain only
  for the size regime where the sweep below shows a win, if one exists.

### Certificate routes

The packed extension applies after numeric delegation and the structural
shortcuts above. For remaining symbolic inputs, retain the same reified matrix and
`DetWitness`; the producer uses canonical polynomials, while the packed tree
route quotes input expression trees. After compiled witness
production, run [the executable preflight](../SPEC/Libraries/hex-poly-det.md#bounds-and-selection)
on all witness products before emitting the certificate proof. Existing
reflection/producer budgets are checked at their earlier boundaries; the
witness-dependent packing bound cannot be known from matrix entries alone.

| Condition | Route |
|---|---|
| Numeric fragment | Delegate to the existing numeric handler |
| Automatic mode, verified triangular/zero or common row-factor structure | Structural identity and numeric coefficient certificate where needed |
| Remaining symbolic `n ≤ 3` | Existing closed form |
| Automatic mode, sparse cofactor expansion within 64 leaves and proof budget | Structural cofactor proof |
| Malformed supplied certificate, including its quotient payload | `failure` |
| Symbolic capability unavailable | Explicit decline |
| Producer exhausts its intermediate or certificate budget | Structured decline naming the budget, count reached and limit |
| Tree product or target preflight exceeds a packing limit | Apply the existing packed/list selection to canonical entry lists, restoring list quotation and entry interpretation proofs |
| Supported certificate, every packed product within digit/bit limits and covered by the crossover table | `checkDetPolyPackedTree` for retained integer trees; `checkDetPolyPacked` or `checkDetPolyPackedMod` for term-list inputs |
| Packing budget exceeded, crossover absent/selects sparse, or residue quotient payload absent | `checkDetPolyList` with the appropriate integer/residue operations |

The packing configuration embeds `Hex.Kronecker.Budget`, with preregistered
limits `65536` dense digits and `16777216` packed bits. Its size report and
mode selection follow hex-poly-det; `signedPacked` requires the independent
Kronecker product crossover evidence. No second kernel attempt runs after a
packed rejection. After preflight, the compiled side validates using the
selected checker on exactly the quoted payload, as specified by hex-poly-det.
An unexpected `false` is a hard certificate failure before proof emission;
it is not a budget decline. The optional quotient preparation is compiled,
budgeted work; inability to afford it selects residue lists before proof emission.

The determinant producer is `Hex.Matrix.detWitnessBudgeted`, instantiated
through `Hex.PolyDet.produce` in `Basic.lean`, with polynomial support as
the size measure. The integer frontend and `Frontend.residueWitness?`
call this wrapper with their respective compiled self-checks. Its limits are
100,000 and 65,536. It admits each round by the term-product bound of its
actual operands, checks total block support after the round, and checks
witness support before the self-check, following the hex-bareiss contract.
The diagnostic is `det: symbolic determinant declined: <budget> budget
exhausted (count <count>, limit <limit>)`. The worst-case minor estimate
`n! * support^n` is diagnostic only; it does not reject a matrix before
elimination. Reflection budgets still apply at their own boundaries.
Retain the independent pre-elimination coefficient-bit check
`2 * n * (entryBits + support.log2 + n.log2 + 2)` against the remaining
4,096-bit reflection budget. Removing the support estimate as an admission
guard does not remove this coefficient-growth guard.

When packing exceeds a limit, use the diagnostic
`det: packed certificate declined: dense box requires <D> digits and <N> packed bits (limits <Dmax> digits, <Nmax> bits); using term lists`.
Include the product row, per-atom degrees, and `limitingStage`; saturated
bounds print `at least <limit + 1>`. Missing crossover coverage or missing
quotients have distinct reasons (`no measured packed regime` or
`residue quotient payload unavailable`). These are declines of the packed
arm, not of the entire symbolic attempt when the list checker succeeds.
If residue lists are unavailable too, use the existing carrier decline.

The certificate trace records `term-list`, `packed/plain`, or
`packed/signedPacked`, plus integer/residue encoding, each product's
`SizeBound`, quotient support where present, and any packing-decline reason.
Retain the `closed-form` route and report unsupported symbolic attempts as
`declined`. Trace the chosen checker in tactic, term and simproc forms, so
the sweep cannot count a structural success as a packed success. Mathlib
determinant tactics are never an implicit route.

## Prerequisites and input classification

The shared prerequisites are the same as
[hex-generic-rank-mathlib §Prerequisite changes](../SPEC/Libraries/hex-generic-rank-mathlib.md#prerequisite-changes-in-other-libraries):
canonical list arithmetic in hex-mv-poly and its denotation theorem in
hex-mv-poly-mathlib block the kernel route (the list form has landed);
the numeric handlers' `throwUnsupportedSyntax` refactor has landed
(https://github.com/kim-em/hex-dev/issues/10230); and the residue coefficient
provider in hex-reflect-mathlib blocks positive characteristic. The
polynomial producer generalisation belongs to hex-bareiss, its determinant
soundness to this companion. These are implementation obligations, not
claims that the proposed declarations already exist. Both residue checker
arms also require #10257's canonical residue lists, validity, equality and
nonzero tests. Supplying quotient polynomials does not remove that dependency.

Two frontend adaptations are also required: a proved pass clearing closed
rational coefficients, and batch quotation using the canonical list
layer's denotation constructor. Neither is provided by the current ring
reifier. They belong to the symbolic frontend and its reflection bridge;
they do not extend hex-reflect's fixed ring language with symbolic division.
This library imports `HexReflect`, `HexReflectMathlib`, `HexMvPolyMathlib`
and, through `HexPolyDet`, `HexMvGcd`; hex-bareiss and hex-bareiss-mathlib
import no polynomial provider. The `det` syntax kind remains owned by
`HexBareissMathlib/Tactic.lean`; this library's handler attaches to it
without redeclaring the syntax, and answers `throwUnsupportedSyntax` for
input outside its fragment.

Input classification is shared with
[the symbolic `rank` arm](../SPEC/Libraries/hex-generic-rank-mathlib.md#input-classification).
Handler order is registration order in reverse, so a handler registered by
this library runs *before* hex-bareiss-mathlib's numeric handler and its
diagnostic fallback. The symbolic handler therefore begins by classifying
the numeric fragment itself and throws `throwUnsupportedSyntax` for it, so
numeric inputs reach the numeric handler with no symbolic work, exactly as
`HexGenericRankMathlib/Tactic.lean` does for `rank`; it is registered with
`@[tactic HexMatrixMathlib.Det.detTac, no_fallback]`. The term form has its
own registration on `HexMatrixMathlib.Det.detTerm` with the same numeric
guard, since the numeric `det%` elaborator raises an ordinary error on its
`notApplicable` rather than delegating; the two elaborators never both
run on one input. For a square literal of dimension at most three the
symbolic handler takes the closed-form route above and never reifies. Otherwise it reads the square matrix through the
shared literal layer, including definitions
unfolded within budget. It canonicalises and reifies all entries with
`reifyRing?`, with top-level variables enabled, in one hex-reflect batch.
For symbolic `fun` and `Matrix.ofArray` inputs, literal recognition is
shared but proof identification uses finite extensionality and the batch's
entry interpretation proofs, with structural unfolding of the literal's
indexing. It must not use the numeric `entriesEq`/`decide` route, which
requires reducible `DecidableEq F`. No equality decision on symbolic values
is needed; these entrywise identification proofs are measured separately.
The batch seals its environment at `k` atoms, converts with the
characteristic-aware conversion when `Sym.Arith` supplies the characteristic
and the plain conversion otherwise, and uses `cmp := Hex.Mono.grevlex`.
It yields

```text
P : Hex.Matrix (Hex.MvPoly k C cmp) n n
v : Fin k → F
ι : C →+* F
```

and an interpretation proof `eval₂ ι v P[i, j] = A i j` for every entry.
Here `F` is the user's carrier and `C` the coefficient provider's carrier.
Routing is by the converted polynomials: any nonconstant entry selects the
symbolic arm; if all entries convert to constants after cancellation, the
same arm handles the resulting constant matrix, even with `k > 0`.

Atoms are independent indeterminates. Expressions outside the fixed ring
language, including `x / y`, opaque constants, `Real.exp t` and symbolic
powers, become atoms. No hypotheses or algebraic relations between atoms
are used: `hx : x = 0` does not change the polynomial for `x`. Atomisation
can prove polynomial identities involving these terms, but cannot prove
relations between them. The budgets are hex-reflect's (atoms, terms,
coefficient bits and proof nodes), plus matrix dimension and certificate
size; exhaustion returns `declined` naming the exhausted budget.

In equality mode the user's expression `e` is reified in the same batch,
using the matrix's atoms. Record the atoms allocated by the entries;
reifying `e` must not allocate additional atoms. Seal once after both have
been reified and convert both with that sealed environment. An expression
which cannot be reified as a ring expression in those atoms declines with
`det: symbolic determinant declined: target is not a ring expression in the matrix atoms`.
This includes an opaque term appearing only in `e`.

## Kernel certificate and soundness

The compiled producer returns transform rows and a value `d : MvPoly k C cmp`,
or a polynomial left kernel vector with value zero. Its meaning is always
`Hex.Matrix.det P = d`, including when the determinant is identically zero;
a matrix which becomes singular only at some atom valuations still has a
nonzero polynomial determinant. All witness entries lie in the polynomial
ring, never in a chosen specialisation or in the fraction field.

The term-list arm checks `checkDetPolyList` on the row lists of canonical
polynomial term lists and the witness in the same representation. Coefficients are
encoded by `Int` for the integer arm and canonical `Nat` residues for the
residue arm; exponent vectors are lists of `Nat`. Shape, canonicality,
nonzero diagonals, vanishing products and the determinant value identity
are checked as specified on the executable side. In particular the final
value check uses `l₀ = 1`, `lᵢ₊₁ = uᵢ` and `d = sign σ * uₙ₋₁`
(`d = 1` when `n = 0`), without expanding the product of pivot polynomials.
Polynomial equality uses the list layer's `beq_iff` contract, not evaluation at sample points.

The existing `checkDetPolyList_sound` in this library identifies a passing
check with `Hex.Matrix.det P = d`, where `P` and `d` denote the supplied
lists and `Hex.Matrix.det` is the Leibniz reference. It uses the list
arithmetic denotation theorem, `HexMatrixMathlib.det_eq`, row permutation
signs and the triangular determinant lemmas, just as `det_eq_of_checkList`
does. Require `[CommRing C] [IsDomain C] [DecidableEq C]` on the
coefficient carrier, in addition to the producer's lawful GCD/order context.
Transport through `HexMvPolyMathlib.equiv` to `MvPolynomial (Fin k) C`,
whose existing domain instance supplies cancellation and the singular-vector
argument; no existing `IsDomain (MvPoly …)` instance is assumed. The
transform's diagonal product is nonzero there. Its cancellation is a
propositional argument using the checked adjacent-diagonal equalities, not
an expansion of the product by the kernel. The singular branch uses
`Matrix.exists_vecMul_eq_zero_iff` over that domain to prove determinant zero.
Neither argument requires the vector or diagonal product to stay nonzero after
specialisation.

### Packed soundness

`checkDetPolyPacked_sound` has the same conclusion as
`checkDetPolyList_sound`: a passing check implies `Hex.Matrix.det P = d`
for the denoted input and witness value (zero for `.singular`). It takes
the mode as a checker parameter, without trusting a producer
correctness claim or external bound hypothesis. Its integer polynomial
model is a domain; subsequent evaluation transports the conclusion to
**any** commutative ring, without `CharZero` or injectivity at the atoms.

Factor the determinant argument into one statement about the witness
identities: valid shapes and swaps, nonzero transform diagonals and the
row-prefix product equalities with the adjacent-diagonal/value conditions,
or a nonzero vector whose product with the matrix is zero. The list checker
derives these with its arithmetic denotation laws. The packed checker
derives the same identities with
[`Kernel.mulTerms_sound`](../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md#denotation-and-polynomial-model),
instantiated in `MvPolynomial (Fin k) Int` at the indeterminates, and the
existing `HexMvPolyMathlib.equiv` bridge. This shares the permutation,
triangular determinant, cancellation and singular-vector proof above; it
neither re-runs `checkDetPolyList` in the kernel nor duplicates determinant
algebra. Extracting that shared statement from the current `Decode.sound`
is an implementation obligation.

`checkDetPolyPackedTree_sound` supplies the same determinant argument for
tree-valued input entries and list-valued transform rows and witness value.
The mixed Kronecker product soundness theorem supplies each row-prefix
identity from list packing and tree evaluation in the integer polynomial
model. Entry and target degrees and ℓ¹ bounds come structurally from the
trees and enter the checked common plans. The frontend translates retained
`ReifiedRing.expr` values with `fromGrind`; entry identification uses their
denotation hints and the translation's denotation theorem alone. It quotes
no input entry lists and emits no `HexReflectMathlib.Kernel.eval_checked`
proofs on this route. Target equality checks
`evalKron(target tree) = packTerms(d)` with bounds for both sides, so it
does not expand the target in the kernel. The term form reconstructs the
witness value without a reflexive target comparison.

`Tree.evaluated` denotes the tree matrix in the target carrier. The frontend
uses the existing finite-extensional `Polynomial.identify` to assemble the
entry denotation hints against that matrix. `Tree.target_det`,
`Tree.result_det` and `Tree.scaled_det` transport the polynomial-domain
determinant identity through `RingHom.map_det`; the scaled form supplies the
existing rational cancellation layer. These are implementation obligations
in `HexPolyDetMathlib/Tree.lean`.

Structural tree bounds do not use cancellation and can exceed the bounds
of canonical entry lists. Both tree products and the target comparison must
pass preflight before emitting a tree certificate. A tree preflight decline
falls back to the existing list-based selection before any kernel attempt;
its entry proofs again use list interpretation. The entry/target performance
bar therefore applies to probes that select the tree route.

Kernel-facing packed certificates call `Hex.Kronecker.Kernel.mulTerms`
or the corresponding mixed tree form. Preflight reports and budget
comparisons remain elaborator work. The kernel validates mathematical
shapes and bounds once; it does not replay the resource policy.

Proof assembly gives the nested conjunction its stated `AllFin` expected
type and constructs identification and transport applications directly,
without Meta unification through the literal matrix and quoted payload.
The frontend uses compiled, capped counting of distinct nodes in the closed
proof, including retained syntax and let-bound payloads, before kernel admission.
Repeated subexpressions of the closed type and proof are shared before adding
the auxiliary theorem, as in Lean's ordinary declaration elaboration.
The outer application's proof arguments may be closed and checked as opaque
auxiliary lemmas before checking their composition. Every component and the
composition are charged to the same proof-node budget before their respective
kernel checks; distinct nodes are counted across the entire batch, so shared
payload is charged only once. Component checks are not omitted
from performance measurements. This proof organization applies independently
of matrix shape and does not change certificate selection or soundness.
Early admission counts the quoted payload itself; it does not estimate proof
size by multiplying term counts by a constant.
Do not traverse the assembled proof with an interpreted node counter.

`checkDetPolyPackedMod_sound` uses `Kernel.mulTermsMod_sound` in the residue
polynomial model for each supplemental quotient row. It recovers the
integer identity `M̃ Ã − C̃ = p Q`, then transports to characteristic `p`
through the residue coefficient laws, including
`HexReflectMathlib.residueHom` for target evaluation. The determinant
argument still requires a coefficient domain (prime characteristic for the
residue producer); the final target only needs `CommRing` and `CharP`.
Neither nonzero polynomials nor nonzero transform diagonals are assumed to
remain nonzero after that evaluation. Quotient shape/canonicality/bounds
and the integer identities are checked premises, not producer assertions.

The rational row-clearing route may use the integer tree checker for the
scaled matrix `B`. Its target check compares `t * dB` with the tree
`D * qZ` at the checked Kronecker point, retaining the nonzero-scale proof.
Term-list routes retain their canonical-list target comparison and entry
interpretation proofs. The term form avoids comparing its value with itself.
The tree route adds no reification or small closed-form solver.

For term-list routes, the batch must quote `P` with each entry *defined to be* the canonical
list layer's denotation applied to its quoted entry list. Thus the batch's
`P` and the checker's denoted row matrix contain the same constructor
applications, giving definitional identification without evaluating them.
This is a quotation contract, not a claim that independently constructed
`MvPoly` trees are definitionally equal. Today's `HexReflect/Session.lean`
quotes `ofIntTerms`; the list prerequisite must supply the bridge from
conversion terms to canonical exponent lists and adapt that quotation and
its entry interpretation proofs. A compiled `MvPoly` matrix is still built
for the producer, but its tree representation is never quoted as a second
matrix for the kernel to compare. The denotation lemmas justify list
arithmetic without reducing reference polynomial operations or rebuilding
trees; conversion, quotation and identification costs are recorded in the
proof probes.

Every definition on either kernel arithmetic path is `@[expose]`, uses
structural recursion on lists of `Nat`/`Int` and `Hex.Kronecker.Expr`, and obeys
[matrix-tactics §Kernel discipline](../SPEC/matrix-tactics.md#kernel-discipline).
In particular the kernel never evaluates `bareissWith`, `detWitness`, a
reference checker, or `Hex.Matrix.det` on `Hex.Matrix (MvPoly …)`. The
reference determinant occurs in soundness statements only; neither `Array`,
`Vector`, `Fin`, `Finset`, matrix indexing nor well-founded polynomial
arithmetic is reduced to check a certificate. The packed checkers of
[hex-bareiss §Packed evaluation](../HexBareiss/SPEC/hex-bareiss.md#packed-evaluation)
are sound through `checkDetList_of_packed` and `checkDetRat_of_packed`:
`triangularCheckPacked_eq` and `zeroDotsPacked_eq` identify the packed
walk with the plain one under the entry bounds, by `dotIntPacked_eq` of
[hex-matrix-mathlib §Kronecker-packed dot products](../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#kronecker-packed-dot-products),
and the columns of the arranged matrix inherit the bounds of the rows
(`mem_applySwaps`, `columns_bound`); `det_eq_of_checkListPacked'` and
`det_eq_of_checkRatPacked'` are the plain theorems after the implication.
One auxiliary lemma is
checked synchronously through the literal layer's `addClosedProof`; there
is no elaborator `Kernel.whnf` pre-check, no elaborator type check of the
proof before the kernel's, and no `native_decide`.

## Transport and result reconstruction

Write `E := HexMatrixMathlib.matrixEquiv` (to avoid confusing the matrix
equivalence with the user's expression `e`) and
`φ := HexMvPolyMathlib.eval₂MathlibHom ι v`. The entry proofs and
`eval₂MathlibHom_apply` give `A = (E P).map φ`. Determinant correspondence
and `RingHom.map_det` then give

```text
A.det = φ (Hex.Matrix.det P) = φ d.
```

If `q` is the polynomial reified from `e`, its batch proof gives `φ q = e`.
The tactic checks equality of the canonical term lists of `d` and `q` in
the kernel, uses `beq_iff` and denotation to obtain `d = q`, and composes
these equalities. It proves agreement with the user's expression, without
printing a polynomial and asking `ring` to prove it equal. A mismatch is a
`declined` outcome displaying `φ d` and explaining that the target is not
a polynomial identity in the sealed atoms; it is not evidence that the
specialised target is false. For example, `!![x].det = 0` under `hx : x = 0`
requires substitution before this arm can close it.

The accepted goals are `A.det = e` and `e = A.det`, the latter by symmetry.
With no target expression, `det% A` returns the existing
`HexMatrixMathlib.Certified Matrix.det A`, with `value := φ d` and
`proof : A.det = value`; the value is the denoted computed polynomial in
`F`, not a polynomial object or an unproved pretty-printed expression.
These results are unconditional. Even if a pivot polynomial vanishes at
`v`, determinant transport is valid: unlike symbolic rank, this arm has no
nonvanishing condition to discharge or leave as a goal. The empty matrix
returns one.

## Carriers and composition

The integer arm uses the integer provider (`C := Int`,
`ι := Int.castRingHom F`) for any `[CommRing F]`: `RingHom.map_det` needs
no injectivity, and there is no assumption that evaluation of polynomials
at the atoms is injective. Soundness is unconditional. Completeness holds
whenever `ι` is injective on the coefficients that occur; in positive
characteristic a polynomial identity that holds only modulo `p` is not
found by the integer arm and the residue arm below is the complete one.

Rational coefficients use row scaling as `checkDetRat` does. Before ring
reification, a proved coefficient-normalisation pass over `ℚ` recognises
closed rational scalars and clears their denominators in each row. It
returns positive integer scales `sᵢ` and integer polynomial expressions
for `B`, with entry proofs `eval₂ ι v B[i, j] = sᵢ * A i j`. The pass
shares the atom environment with matrix and target reification and treats
division by symbolic terms as atoms; it does not rewrite `x / y` into
polynomial division. Current `reifyRing?` atomises division, including
`1 / 2`, so this pass is an explicit additional implementation obligation.
Until it exists, denominator-clearing requests decline with
`det: symbolic determinant declined: rational coefficient normalisation unavailable`;
ordinary polynomial identities in atomised division terms remain sound.

Certify the integer polynomial matrix `B` by the selected list or packed
checker. If `D := ∏ sᵢ` and `dB` is its certified determinant, the entry proofs and
row-scaling theorem give `D * A.det = φ dB`. This arm requires `[Field F] [CharZero F]` on
the target, unlike the integer arm: cross-multiplication needs the scales
`t * D` to be cancellable and the term form needs division, and `CharZero`
alone does not give cancellation in a commutative ring (in `ℤ × ZMod 2`
the element `2` kills `(0, 1)`). Positivity and `CharZero` then prove
`(D : F) ≠ 0`. Apply the same proved pass to
the target to obtain a positive integer `t` and integer polynomial `qZ`
with `φ qZ = t * e`. Kernel list equality checks
`t * dB = D * qZ`, again with nonzero integer scales interpreted in `ℚ`.
The term form returns `φ dB / D`. All computational checks use integer
lists; the entry/scalar normalisation proofs establish the scaling equations,
so no rational polynomial list representation is assumed. Nonzero closed
scalar denominators are proved by the normalisation pass, never left as
user side goals.

Positive characteristic uses the residue provider
(https://github.com/kim-em/hex-dev/issues/10255, merged) with the residue
list form of https://github.com/kim-em/hex-dev/issues/10257, the Mathlib
ring/domain bridge and the lawful exact quotient at `MvPoly`. For `ZMod64 p`, this includes both
`ZMod64.Bounds p` and `ZMod64.PrimeModulus p`; a composite modulus does not
satisfy the domain contract. Characteristic-aware conversion reduces
coefficients, not exponents or polynomial functions: `X³ - X` over
`ZMod 3` is not the zero polynomial. The residue term-list arm is enabled:
`Hex.PolyDet.opsMod` instantiates `checkDetPolyList`, `Residue.decode` supplies
its `denoteMod` laws, and `Residue.target` transports the checked determinant
through `HexReflectMathlib.residueHom`. Entry replay uses the shared
`HexReflect.Kernel.ringListMod`. Kernel tests cover the formal `X³ - X`,
4×4 multivariate determinants, singular witnesses, and malformed residues.
The packed residue arm remains a separate implementation obligation (#10274).

hex-bareiss-mathlib's simproc `Hex.norm_det` uses the numeric Hex certificate.
This library provides the opt-in symbolic simproc `Hex.normPolyDet`.
Neither invokes Mathlib's `norm_det` or `eval_det`. A symbolic success rewrites
to `φ d`; inapplicability or decline leaves the original expression unchanged.
The tactic reports `det: symbolic determinant declined: <reason>` immediately
on a capability or budget decline, including carrier or entry coordinate where
relevant. It must not re-enter the symbolic attempt through a simproc.
Mathlib determinant tactics remain explicit user choices and independent
comparators, never a means of making a declined Hex attempt appear successful.
Check budgets before invoking the producer where the required bounds are
available; production itself uses the actual intermediate and certificate budgets.
A malformed or rejected producer certificate is `failure`, never a weaker
result disguised as success. The axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`, as for the numeric arm.

## Proof probes and shipping bar

Add symbolic probes under `bench/HexPolyDetMathlib/ProofProbe`, with the
executable producer measurements owned by hex-poly-det. Sweep dimensions
`2, 4, 8`, atom counts `1, 2, 4`, total entry degrees `1, 2, 4` and entry
supports `1, 4, 16`, recording the actual canonical degree and support.
Use all feasible combinations: a requested support larger than the number
of monomials of the given degree bound and arity is marked infeasible,
not silently generated with smaller support. Include dense, structured,
pivot-swap and identically singular matrices, rational coefficient variants,
and valuations at which a nonzero polynomial determinant becomes zero.

The closed-algebraic family uses `ℚ(√2)` blocks, including
`!![α, 1; 2, α]`. The shared polynomial target is `α² - 2`; both arms
must be measured on that target with `α` treated as an atom. The target
zero using `α² = 2` is a separate scope probe: independent-atom reification
cannot use that relation, in Hex as in `norm_det`. Record the decline;
do not claim an algebraic-number scope win without a separate certified
coefficient provider that can prove the relation. Strictly larger scope
must instead be demonstrated on accepted surfaces such as the shared
literal layer's `fun i j => …`/`Matrix.ofArray` forms and `det%`.

Compare against the unmodified pinned `norm_det` from
`Mathlib/Tactic/NormDet.lean` on identical targets, with the same residual
ring normalisation if the Mathlib arm needs it, in fresh modules against
matched import-only baselines. Use `scripts/bench/fresh_module_sweep.py`:
six samples, adjacent pairs, alternating `AB`/`BA`, retaining all completed
runs on the shared host. Record batch reification, producer, list conversion,
kernel check, entrywise identification and total elaboration separately,
plus proof node count, `.olean` size, realised minor support/degree and
coefficient bits. Record
one kernel-only profile per family and median ratios in this SPEC before
shipping; these are planned measurements, not inferred timing results.
Preregister per-case cleanup timeouts and proof-build ceilings in the runner
manifest; a timeout is reported as such and never removed from the ladder.
Measure time to decline separately from successful proof time. A declined Hex
invocation is never counted as a completion or assigned a speedup ratio.

Bird's `O(n⁴)` ring-normalised certificate chain is expected to lose as
matrix dimension grows while minor support remains modest: the fraction-free
list check uses about `n³ / 3` polynomial products (or `n²` for a singular
vector), and never replays pivot search or division. With many variables,
higher degrees or dense support, expanded minors and intermediate products
can swell enough to reverse that advantage; small matrices can also be
dominated by reification and list conversion. Report those losses and
budget declines rather than extrapolating scalar operation counts to time.

The shipping rule is the opt-in exception recorded in
[matrix-tactics §The bar against Mathlib](../SPEC/matrix-tactics.md#the-bar-against-mathlib):
this arm does not clear the strict bar, since its certificate fragment
is not strictly larger than `norm_det`'s and a shared family may lose. The handler and term
form ship regardless, as opt-in; the simproc enters the default chain only
for families where the fresh-module median is smaller than `norm_det`'s,
and the table records every family either way. Declines count as failures to solve, not scope preservation. A win on selected
rungs enables the chain on those rungs only.

### Packed-arm comparison

The packed implementation reruns the shared families in
[the recorded report](hex-poly-det-mathlib-performance.md),
retaining its infeasible cases, failures and declines. For every certificate
case compare forced term lists and forced packed checking on the same
witness and proposition. Fix the sparse/packed crossover table from those
measurements first, with separate tables for list entries and retained trees.
Each tree key uses its structural packed bound and retained entry-node count;
list keys use canonical entry support. Witness support and inner dimension
remain common coordinates. Evidence never transfers between the two tables.
The two-arm sweep measures the preferred packed encoding of each witness. It
fits the tree table from those tree observations and may add measured list
fallback keys; it does not erase the historical list table without a dedicated
list-packed comparison. The retained list table and its source hash are named
in the sweep record and table artifact. Fresh automatic-dispatch measurements
include the costs of whichever retained route actually runs.
The forced proof module, not the supplemental list-only compiled driver,
determines the measured encoding and keys. Use the mode-selection table
supplied by Kronecker's product benchmark. Then run fresh comparisons of the full automatic dispatch
using the fixed tables against unmodified `norm_det`. An empty-table dispatch
run is a sparse-fallback control, not evidence about packed dispatch. Forced
packing still obeys the hard limits; an ineligible case records a decline, not a packed timing. Keep the `n ≤ 3`
controls on their existing route. Extend the certificate grid to dimensions
`4, 8, 16`, atoms `1, 2, 3, 4` and degrees `2, 4, 8, 16`, retaining the
original support ladder and recording actual per-atom degrees. Add matrices
with independent atoms to exercise early packing declines, as well as
prime-residue quotient cases and missing-payload fallback cases. Residue
comparisons include a small prime and a prime near the provider's `2^31`
upper bound, with `p` and quotient support recorded alongside packed bits.

Classify the grid by actual product/witness bounds before timing: large
three- and four-atom identities often exceed the digit envelope stated in
hex-poly-det. Keep these rows as expected declines, distinct from infeasible
support requests or timeouts. They measure the preflight and any supported Hex list route,
not forced packed evaluation. Retain the full shared ladder and report the
accepted few-atom region explicitly; do not omit losing or declined cells.

Use the existing fresh-module runner with matched import-only baselines,
six adjacent pairs per comparison and alternating `AB`/`BA` order on one
automatically selected CPU where supported. Retain every completed run and
host context, with at most one unchanged rerun if inconclusive. Preregister
the cases, crossover keys and the existing 45-second cleanup/proof ceilings
before collecting samples. Time quotient generation, preflight and list
conversion, repeated inner/outer packing, integer multiplication, kernel
check, identification, total elaboration and time to decline separately where applicable; record proof
nodes, `.olean` size, support, degree bounds, packed bits and route. Collect
one representative kernel profile per family, not a profile per change.

Start performance investigation with a small representative subset: the main
4×4 quadratic probe, a simple 4×4 control and the named monomial 8×8 probes.
Report the observed wins and losses before considering broader coverage.
Use the runner's `--case` selections and label the result as a subset; subset
evidence cannot fit the shipping crossover table or establish family-wide wins.
The maximum allowance is a backstop, not a target duration.

The complete manual determinant measurement workflow has a hard one-hour
wall-time allowance, including import warmup and attribution: at most ten
minutes for classification, twenty for forced comparison and thirty for
automatic dispatch. A persistent shared budget ledger reserves each stage
before launching it; an interrupted stage does not obtain a fresh allowance
on an implicit retry. The parent runner terminates the stage and its descendants
at the deadline, including builds that start separate process sessions.
This is an operational ceiling, not a performance claim about a tactic.

After a timeout, do not repeat that case or attempt a coordinatewise larger
case in the same arm, mathematical family and carrier. Compare dimension,
atom count, degree and support; increasing one coordinate while decreasing
another is incomparable. Modulus, quotient availability and scope mode must
also agree. Preserve the timeout and record each skipped case with its blocking
case and arm. Carry this evidence into later stages for the same arm only.
A Hex timeout does not censor Mathlib measurements. Deadline skips are recorded
separately. Neither kind of skip is a measured timeout or a successful sample;
it supplies no median or crossover evidence. A complete schedule accounts for
all rows, including skips, and does not imply complete measurement coverage.
Only six successful observations per arm support the final paired medians.
Preliminary results from fewer pairs must state their sample counts.

The implementation updates the report and this SPEC with per-family medians
for term lists, packed checking, automatic dispatch and Mathlib, plus
completion counts, ratios and an explicit `default-on` / `opt-in` decision.
The crossover table is fixed from the preregistered comparisons before
activation. Reconsider `Hex.normPolyDet` under
[matrix-tactics §The bar against Mathlib](../SPEC/matrix-tactics.md#the-bar-against-mathlib):
only an identifiable family whose full dispatched invocation has a smaller
median than `norm_det`, with declines counted as failures to solve, may enter the
default chain. Every other family remains opt-in. Faster packed kernel work
alone does not satisfy this rule. No family is enabled by default; the packed comparison outcome below records
the complete forced and automatic measurements and their opt-in decisions.

## Declaration inventory

Existing declarations used by this design:

| declarations | source |
|---|---|
| `Hex.Matrix.DetWitness`, `checkDetList`, `checkDetRat`, `detWitness` | `HexBareiss/Kernel.lean` (integer witness and producer today) |
| `HexMatrixMathlib.det_eq_of_checkList`, `det_eq_of_checkRat` | `HexBareissMathlib/Kernel.lean` |
| `Hex.norm_det`, `det` and `det%` syntax | `HexBareissMathlib/Tactic.lean` |
| `HexMatrixMathlib.Certified` | `HexMatrixMathlib/Literal.lean` |
| `HexMvPolyMathlib.eval₂MathlibHom`, `eval₂MathlibHom_apply` | `HexMvPolyMathlib/Aeval.lean` |
| `HexMatrixMathlib.det_eq` | `HexDeterminantMathlib/CoreTransport.lean` |
| `RingHom.map_det` | Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `Matrix.det_of_isLowerTriangular`, `det_of_isUpperTriangular` | Mathlib `LinearAlgebra/Matrix/Block.lean` |

The domain proof additionally uses `HexMvPolyMathlib.equiv` and
`instCommRingMvPoly` (`HexMvPolyMathlib/Equiv.lean`) and
`Matrix.exists_vecMul_eq_zero_iff` (Mathlib
`LinearAlgebra/Matrix/ToLinearEquiv.lean`). Batch quotation is in
`HexReflect/Session.lean`, sealing in `HexReflect/State.lean`, and
`convertTerms?`/`ofIntTerms` in `HexReflect/Convert.lean`.

`checkDetPolyList`, `checkDetPolyList_sound`, the polynomial generalisation
of `detWitness`, and the canonical list layer's `beq_iff`/denotation API
are implemented. `checkDetPolyPacked` / `checkDetPolyPackedMod` and their
soundness theorems are implemented, with the packed checkers owned by
hex-poly-det and the proofs here. The generic list checker stays Mathlib-free
in hex-bareiss, its `MvPoly` instantiation in hex-poly-det, and its determinant soundness
in this library.

The tree extension adds `Tree.evaluated`, `Tree.target_det`, `Tree.result_det`
and `Tree.scaled_det` in `Tree.lean`, reusing `Polynomial.identify` and the
existing rational cancellation lemmas. `checkDetPolyPackedTree_sound`
connects the mixed product checker to the shared determinant identities.
The producer wrapper and its `produce_check` contract remain independent
of which kernel certificate the frontend selects.

## File organisation

```
HexPolyDetMathlib/
  Sound.lean        -- shared witness identities, list soundness, transport
  Packed.lean       -- checkDetPolyPacked_sound and residue variant
  Tree.lean         -- tree certificate soundness, denotation, and transport
  Certificate.lean  -- compiled selection, self-check, quotation, and trace
  Scaling.lean      -- rational scaling transport
  Normalize.lean    -- proved coefficient normalization
  Frontend.lean     -- reification and certificate preparation
  Small.lean        -- closed forms
  RowFactor.lean    -- integer row factors and numeric determinant transport
  RatFactor.lean    -- rational scalar skeletons and numeric row-factor transport
  Structural.lean   -- triangular identities and bounded sparse cofactors
  Tactic.lean       -- the handler on hex-bareiss-mathlib's `det` syntax kind, det% for symbolic input, Hex.normPolyDet
  Tests.lean
  PackedTests.lean  -- packed routes, singularity, transport, and axiom audits
HexPolyDetMathlib.lean
```

The `libraries.yml` entry is

```yaml
  HexPolyDetMathlib:
    deps: [HexPolyDet, HexBareissMathlib, HexReflect, HexReflectMathlib, HexMvPolyMathlib, HexMatrixMathlib, HexKroneckerMathlib]
    mathlib: true
    proof_probes: [bench/HexPolyDetMathlib/ProofProbe]
    done_through: 3
    status: active
```

## Implementation and verification

The executable instantiation is `HexPolyDet/Basic.lean`; the companion separates
`Sound.lean`, `Scaling.lean`, `Normalize.lean`, `Frontend.lean`, `Small.lean`, and
`Tactic.lean`. Integer polynomial certificates transport to any `CommRing`.
The proved denominator-normalisation frontend currently operates on `Rat`;
divisions over other carriers remain eligible atoms. `Residue.lean` instantiates `Decode` with the shared Nat residue operations
and proves determinant transport. The closed checker contains no `ZMod64`
arithmetic.

Producer-side grevlex terms are converted to canonical list order by merge sort.
Generated value expressions use balanced sums. Tree entry identification uses
denotation hints; the list fallback uses direct list denotation. Neither route
makes a round trip through the Hex matrix data.
The term form does not replay a reflexive comparison of its own value list.

Limits are 16 rows, 65,536 certificate terms, 100,000 intermediate terms and
source nodes, 4,096 coefficient bits, exponent 64, and 1,000,000 proof nodes.
Producer admission uses the actual round operands and block support, as
specified in §Certificate routes. Worst-case minor and monomial counts are
diagnostics only. Budget exhaustion reports the count reached and limit,
including when a sparse 8×8 input reaches the producer and later declines.
The manifest preregisters 45-second cleanup/proof ceilings and six samples per
arm. The main 2/4/8 ladder contains 48 feasible dense combinations and 33
infeasible combinations; separate 3×3 cases measure the closed-form route.
Dense rows are scaled copies of seeded integer rows, so entries within one row
share a polynomial. This correlation is part of the measured input family.

`HexPolyDetMathlib.Tests` includes certificate-only tests beyond the small route,
nonconstant exact division, rational scaling, singularity, local let bindings,
composite-characteristic targets, and term forms. Its axiom audits include
integer, rational, singular and term-form proofs. Heavy fresh-module probes
belong to the manual sweep; merge-gating CI builds the bounded regression tests.
The symbolic simproc remains opt-in until the recorded sweep establishes a
smaller median for a size regime; no default integration is claimed here.

All Hex sweep modules emit the route taken (closed formula, polynomial
certificate, or decline), including the reason for a budget decline. The
packed implementation extends certificate traces as specified above. The
conservative preflight bound declines some high-degree, four-variable 8×8
cases before elimination in the retained historical sweep. Their recorded
fallback calls remain in that archive, not as successful Hex measurements.
The sweep reports faster cases separately from the opt-in release decision.
Its 70 cases include 4×4 function and array literals and a certificate whose
nonzero polynomial determinant vanishes at a stated atom valuation.

Rational addition, subtraction and row clearing use least common multiples
of their positive scales. Products and powers multiply scales as required.
Compiled comparison against the selected integer or residue list replay
checks conversion before quoting an entry proof. Composite-characteristic
requests decline the residue provider and use the universal integer certificate.
The same route preserves certificates over commutative rings lacking a domain
instance; it may decline identities that require coefficient reduction.

## Recorded measurement outcome

The handler and term form ship through the opt-in exception. The symbolic
simproc remains outside the default chain. The complete 840-sample schedule
and 14 profiles, including every failure and timeout, are retained in
[the report](hex-poly-det-mathlib-performance.md) and its linked
raw data. N-prefixed rows below are the correlated row-scaled family
(except N2K4D1S1); these ratios do not describe independent dense entries.
Times are fresh-module, baseline-subtracted medians in milliseconds. All six
samples are required; ratios use positive medians only. This retained dataset
includes implicit Mathlib fallbacks from the older dispatch. Rows labelled
`fallback` did not finish through Hex in that measurement; their historical
ratios do not establish a Hex speedup or justify default integration. Those
inputs have not been re-measured here under current dispatch, which may select
a different Hex route.

| Case | Mathlib ms | Hex ms | M/H | Completed M/H | Hex route |
|---|---:|---:|---:|---:|---|
| N2K1D1S1 | 41.33 | 89.80 | 0.460 | 6/6 | closed-form |
| N2K1D2S1 | 3.04 | 110.29 | 0.028 | 6/6 | closed-form |
| N2K1D4S1 | 74.68 | 102.87 | 0.726 | 6/6 | closed-form |
| N2K1D4S4 | 187.01 | 256.81 | 0.728 | 6/6 | closed-form |
| N2K2D1S1 | 90.42 | 103.44 | 0.874 | 6/6 | closed-form |
| N2K2D2S1 | 92.18 | 106.16 | 0.868 | 6/6 | closed-form |
| N2K2D2S4 | 112.02 | 188.86 | 0.593 | 6/6 | closed-form |
| N2K2D4S1 | 89.59 | 100.17 | 0.894 | 6/6 | closed-form |
| N2K2D4S4 | 198.88 | 286.75 | 0.694 | 6/6 | closed-form |
| N2K4D1S1 | 44.69 | 65.44 | 0.683 | 6/6 | unobserved |
| N2K4D1S4 | 101.81 | 157.70 | 0.646 | 6/6 | closed-form |
| N2K4D2S1 | 74.55 | 98.74 | 0.755 | 6/6 | closed-form |
| N2K4D2S4 | 190.64 | 197.10 | 0.967 | 6/6 | closed-form |
| N2K4D4S1 | 92.16 | 104.74 | 0.880 | 6/6 | closed-form |
| N2K4D4S4 | 188.84 | 197.71 | 0.955 | 6/6 | closed-form |
| N2K4D4S16 | 2788.30 | 1895.34 | 1.471 | 6/6 | closed-form |
| N4K1D1S1 | 101.54 | 297.30 | 0.342 | 6/6 | certificate |
| N4K1D2S1 | 279.68 | 412.29 | 0.678 | 6/6 | certificate |
| N4K1D4S1 | 240.79 | 406.35 | 0.593 | 6/6 | certificate |
| N4K1D4S4 | 1191.72 | 2005.28 | 0.594 | 6/6 | certificate |
| N4K2D1S1 | 103.55 | 293.17 | 0.353 | 6/6 | certificate |
| N4K2D2S1 | 291.93 | 481.72 | 0.606 | 6/6 | certificate |
| N4K2D2S4 | 1121.42 | 2293.34 | 0.489 | 6/6 | certificate |
| N4K2D4S1 | 293.59 | 426.24 | 0.689 | 6/6 | certificate |
| N4K2D4S4 | 2100.48 | 4077.43 | 0.515 | 6/6 | certificate |
| N4K4D1S1 | 150.07 | 288.65 | 0.520 | 6/6 | certificate |
| N4K4D1S4 | 692.92 | 1800.87 | 0.385 | 6/6 | certificate |
| N4K4D2S1 | 288.94 | 486.34 | 0.594 | 6/6 | certificate |
| N4K4D2S4 | 2098.92 | 4668.53 | 0.450 | 6/6 | certificate |
| N4K4D4S1 | 287.76 | 495.23 | 0.581 | 6/6 | certificate |
| N4K4D4S4 | 2256.02 | 4804.17 | 0.470 | 6/6 | certificate |
| N4K4D4S16 | — | — | — | 0/0 | unobserved |
| N8K1D1S1 | 690.61 | 999.66 | 0.691 | 6/6 | certificate |
| N8K1D2S1 | 2693.22 | 3196.05 | 0.843 | 6/6 | certificate |
| N8K1D4S1 | 2699.85 | 3146.19 | 0.858 | 6/6 | certificate |
| N8K1D4S4 | 36220.70 | — | — | 6/4 | fallback |
| N8K2D1S1 | 1074.74 | 1007.27 | 1.067 | 6/6 | certificate |
| N8K2D2S1 | 3049.37 | 3190.55 | 0.956 | 6/6 | certificate |
| N8K2D2S4 | — | — | — | 0/0 | unobserved |
| N8K2D4S1 | 2993.95 | 3207.48 | 0.933 | 6/6 | certificate |
| N8K2D4S4 | — | — | — | 0/0 | unobserved |
| N8K4D1S1 | 2066.74 | 1097.77 | 1.883 | 6/6 | certificate |
| N8K4D1S4 | — | — | — | 0/0 | unobserved |
| N8K4D2S1 | 4090.38 | 4253.46 | 0.962 | 6/6 | fallback |
| N8K4D2S4 | — | — | — | 0/0 | unobserved |
| N8K4D4S1 | 4010.25 | 4254.07 | 0.943 | 6/6 | fallback |
| N8K4D4S4 | — | — | — | 0/0 | unobserved |
| N8K4D4S16 | — | — | — | 0/0 | unobserved |
| N3K1D1S1 | 86.70 | 194.35 | 0.446 | 6/6 | closed-form |
| N3K2D2S4 | 392.63 | 595.00 | 0.660 | 6/6 | closed-form |
| N3K4D4S16 | — | — | — | 0/0 | unobserved |
| Rational2 | 175.98 | 207.96 | 0.846 | 6/6 | closed-form |
| Singular2 | 65.41 | 84.25 | 0.776 | 6/6 | closed-form |
| Algebraic2 | 2.02 | 83.58 | 0.024 | 6/6 | closed-form |
| Rational3 | 400.42 | 504.31 | 0.794 | 6/6 | closed-form |
| Singular3 | -0.62 | 191.08 | — | 6/6 | closed-form |
| Algebraic3 | 1.46 | 106.08 | 0.014 | 6/6 | closed-form |
| Rational4 | 2191.95 | 2395.61 | 0.915 | 6/6 | certificate |
| Singular4 | 103.02 | 259.09 | 0.398 | 6/6 | certificate |
| Algebraic4 | 104.85 | 293.94 | 0.357 | 6/6 | certificate |
| Rational8 | — | — | — | 0/0 | unobserved |
| Singular8 | 985.34 | 909.28 | 1.084 | 6/6 | certificate |
| Algebraic8 | 214.23 | 651.98 | 0.329 | 6/6 | certificate |
| Swaps | 90.46 | 195.88 | 0.462 | 6/6 | certificate |
| Tridiagonal | 91.97 | 197.33 | 0.466 | 6/6 | certificate |
| Function4 | — | 199.96 | — | 0/6 | certificate |
| Array4 | — | 190.34 | — | 0/6 | certificate |
| AlgebraicScope | 97.61 | 105.21 | 0.928 | 6/6 | unobserved |
| Valuation | 38.42 | 86.67 | 0.443 | 6/6 | closed-form |
| Valuation4 | 47.03 | 197.61 | 0.238 | 6/6 | certificate |


### Packed comparison outcome

The pre-tree baseline packed crossover contains 50 exact product keys from 14 witnesses with six
successful samples in each forced arm and a positive packed median smaller than
the term-list median. The automatic comparison uses the same fixture population
as table fitting, with fresh samples: it is an in-sample dispatch comparison,
not evidence of generalisation to unseen matrices. Exact product keys are a
conservative selection heuristic, not a per-product performance theorem.
The table is fixed before the automatic comparison. No effect-size threshold
was preregistered; small median differences and their spreads are reported
without treating them as robust wins. Both
full 2,064-observation schedules and all 14 family profiles are retained in the
[packed report](hex-poly-det-mathlib-performance.md#historical-list-entry-packed-certificate-comparison).
The report includes the complete 172-case ladder, 57 infeasible support requests,
quotient generation, preflight, conversion, packing, multiplication, synchronous
kernel checks, identification, elaboration and historical Mathlib fallback costs.
The fallback samples are not independent Hex completions. All
selected modes are plain; outer signed packing is inapplicable.

Every family remains **opt-in**. Family-wide wins against unmodified `norm_det`
are not established; historical fallback timings do not establish them.
`Hex.normPolyDet` stays outside
the default chain. Faster individual rungs, including Rational4, do not change
this decision. N-prefixed cases retain correlated row-scaled entries. Family
medians aggregate the completed cases in each column, while M/D uses only
matched cases with positive complete medians; differing completion sets do not
establish a speedup. The small closed-form controls preserve their old route.

Times are medians in milliseconds of six-sample, import-baseline-subtracted
fresh-module medians. Counts show cases with all six successful samples;
incomplete cases remain in the denominator and in the full ladder below.

| Family | Term lists | Packed | Dispatch | Mathlib | Median M/D | Complete cases L/P/D/M | Decision |
|---|---:|---:|---:|---:|---:|---|---|
| dense-row-scaled | 793.99 | 499.86 | 773.59 | 549.42 | 0.884 | 72/59/72/72 of 147 | opt-in |
| rational | 501.03 | 507.54 | 501.05 | 400.14 | 0.976 | 3/3/3/3 of 4 | opt-in |
| singular | 241.04 | 227.83 | 189.51 | 98.63 | 0.823 | 4/4/4/4 of 4 | opt-in |
| closed-algebraic | 194.56 | 202.79 | 199.18 | 77.04 | 0.397 | 4/4/4/4 of 4 | opt-in |
| pivot-swap | 191.71 | 202.95 | 201.68 | 89.84 | 0.445 | 1/1/1/1 of 1 | opt-in |
| structured | 196.11 | 203.21 | 199.65 | 100.70 | 0.504 | 1/1/1/1 of 1 | opt-in |
| literal-function | 198.35 | 223.25 | 202.60 | — | — | 1/1/1/0 of 1 | opt-in |
| literal-array | 197.10 | 199.40 | 203.18 | — | — | 1/1/1/0 of 1 | opt-in |
| closed-algebraic-scope | 110.74 | 99.50 | 100.33 | 98.64 | 0.983 | 1/1/1/1 of 1 | opt-in |
| valuation | 144.58 | 151.45 | 146.10 | 95.79 | 0.760 | 2/2/2/2 of 2 | opt-in |
| independent-atoms | 837.97 | — | 806.64 | 304.22 | 0.377 | 1/0/1/1 of 1 | opt-in |
| block-diagonal | 199.38 | 211.82 | 198.08 | 98.59 | 0.498 | 1/1/1/1 of 1 | opt-in |
| residue-quotient | 200.83 | 290.73 | 194.31 | 100.49 | 0.518 | 2/2/2/2 of 2 | opt-in |
| residue-missing | 200.44 | — | 202.25 | 98.25 | 0.486 | 2/0/2/2 of 2 | opt-in |

Classification: 27 closed-form, 74 eligible, 66 overall-decline, 4 packed-decline, 1 producer-timeout.
The manifest also retains 57 infeasible support requests.

Representative automatic profiles (milliseconds) record the kernel and frontend
phases separately. Nested phases are not additive. AlgebraicScope is the small
relation-supplied control, not a symbolic certificate.


One automatic-dispatch profile per family; milliseconds, with no baseline subtraction.
Kernel is the synchronous declaration check, including certificate replay and transport.
For the closed-form AlgebraicScope control it is Lean’s final type-checking time.
Identification includes the residue matrix-identification phase. Elaboration includes
the whole module. Nested phases are not additive. A dash means not applicable.

| Case | Conversion | Lists | Quotients | Preflight | Identification | Kernel | Elaboration |
|---|---:|---:|---:|---:|---:|---:|---:|
| N4K2D2S4 | 1.860 | 0.476 | — | 5.240 | 50.900 | 681.000 | 1800.000 |
| Rational4 | 1.960 | 0.481 | — | 5.200 | 60.700 | 831.000 | 1980.000 |
| Singular4 | 1.390 | 0.078 | — | 1.190 | 10.000 | 39.900 | 194.000 |
| Algebraic4 | 1.720 | 0.098 | — | 1.930 | 6.300 | 42.100 | 196.000 |
| Swaps | 1.210 | 0.091 | — | 1.960 | 5.360 | 35.100 | 121.000 |
| Tridiagonal | 1.230 | 0.099 | — | 1.920 | 5.790 | 39.800 | 136.000 |
| Function4 | 1.190 | 0.103 | — | 1.910 | 8.210 | 39.700 | 149.000 |
| Array4 | 1.200 | 0.096 | — | 1.730 | 6.030 | 42.700 | 136.000 |
| AlgebraicScope | — | — | — | — | — | 2.360 | 63.200 |
| Valuation4 | 1.230 | 0.091 | — | 1.930 | 5.050 | 37.100 | 125.000 |
| Independent5 | 3.300 | 0.418 | — | 3.260 | 18.600 | 477.000 | 724.000 |
| Block4 | 1.250 | 0.099 | — | 1.720 | 5.670 | 40.100 | 133.000 |
| Residue3 | 24.700 | — | 0.222 | 1.660 | 21.570 | 28.400 | 144.000 |
| Residue3Missing | 24.700 | — | — | 1.560 | 21.640 | 28.200 | 142.000 |

## Structural-route validation

The focused acceptance set comprises the five small diagnostic examples
(diagonal 2×2, rational 2×2, triangular 3×3, independent-block 5×5 and rational
row-scaled 3×3), plus the rational and sparse cases at approximately one and
ten seconds of Mathlib proof work. Require route assertions, both equality
orientations, term/simproc forms, generic carriers, changed numeric coefficients,
permuted sparse positions, false targets, unfamiliar operation instances,
metavariable preservation, and explicit budget/capability-decline tests. Accepted proofs depend
only on `propext`, `Classical.choice` and `Quot.sound`.

Compare the integrated tactic against unmodified `norm_det` followed by `ring`
with six adjacent alternating AB/BA pairs and matched import baselines. Keep
profiling, certificate tracing and axiom printing outside the timed modules;
audit routes and axioms separately. Retain all samples, report whole-build and
proof-attribution metrics separately, and treat tiny build differences within
Lake's polling resolution as inconclusive. Collect one representative attribution
per changed family. Start small, then run the one-second and ten-second cases;
investigate confirmed losses before increasing scale. Run serially on one
leased CPU, with a 60-second build ceiling and a 30-minute total measurement
ceiling. A timeout suppresses larger comparable cases. This focused comparison
does not change the default-on decision or authorize a broader family sweep.
