# hex-poly-det (determinants of polynomial matrices, depends on hex-bareiss and hex-mv-gcd)

The determinant of a matrix with multivariate polynomial entries, certified
by [hex-bareiss](../../HexBareiss/SPEC/hex-bareiss.md)'s polynomial
determinant certificate instantiated at the carrier `MvPoly k C cmp` with
hex-mv-gcd's exact quotient. This is the determinant analogue of
[hex-generic-rank](hex-generic-rank.md) and exists for the same reason:
`HexBareiss` cannot depend on `HexMvGcd`, and `HexBareissMathlib` is a
published mirror whose import closure may not reach the unpublished
hex-reflect and hex-mv-gcd, so the instantiation and the symbolic `det`
arm live in an unpublished pair above both. The companion
[hex-poly-det-mathlib](hex-poly-det-mathlib.md) owns the symbolic `det`
handler, its soundness and its proof probes.

The determinant algorithm and witness are hex-bareiss's generic ones
([hex-bareiss §Polynomial determinant certificate](../../HexBareiss/SPEC/hex-bareiss.md#polynomial-determinant-certificate)),
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
`HexDeterminant`, `HexMatrix`, `HexBasic`. Implementing the packed arm adds
`HexKronecker`, downward in the DAG; it remains Mathlib-free and unpublished.
The SPEC amendment does not change `libraries.yml` or the released manifest;
register the dependency when the planned Kronecker library is implemented.

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
```

`Hex.Matrix.detWitnessWith` is generic over entry arithmetic, with the
integer API retained as a specialisation. The witness type is `DetWitness R`;
its matrix dimension and row shapes are checked by the list checker.
`polyDetWitness?` returns the witness only when the list-form check accepts
it in compiled code; its kernel encodings are integer and residue
coefficients, so its initial carriers are `Int` and `ZMod64 p`, and `Rat`
enters only through the companion's row-scaling arm, which checks integer
lists.

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
carrier, canonical `Nat` residues for the residue carrier once
[the residue list form](https://github.com/kim-em/hex-dev/issues/10257)
exists, exponent vectors as `List Nat`. Its soundness is the companion's.

## Packed certificate

`Hex.PolyDet.checkDetPolyPacked` returns `Bool` and takes a
`Hex.Kronecker.Budget`, `MulMode`, atom count `k`, dimension `n`, canonical
integer polynomial row lists, and the same `DetWitness (PolyList Int)` as
`checkDetPolyList`. It replaces only the product identities with
[`Hex.Kronecker.checkMulTerms`](../../HexKronecker/SPEC/hex-kronecker.md#kronecker-evaluation).
Canonicality, exponent arity, matrix and witness shapes, swap validity,
nonzero transform diagonals or a nonzero singular vector remain checked in
the kernel. Nonzeroness is a canonical polynomial test, never a test at the
packed point or at the user's atom valuation.

The product inputs are determined by the witness, without another matrix
payload. For `.triangular swaps T d`, let `P` be the input rows permuted in
swap order, and `lᵢ := Tᵢ[i]`. Require exactly `n` transform rows, with row
`i` of length `i + 1`, each `lᵢ ≠ 0`, and `l₀ = 1` when `n > 0`. For each
`i < n`, use a `1 × (i + 1)` row `Tᵢ` and the leading
`(i + 1) × (i + 1)` submatrix of `P` in `checkMulTerms`. Its result row is
`[0, …, 0, uᵢ]`, where `uᵢ := lᵢ₊₁` for `i + 1 < n` and
`uₙ₋₁ := sign(swaps) * d`. Thus it checks exactly the zero products below
the diagonal and the adjacent-diagonal identities of
`HexBareiss/Polynomial.lean`; entries above the product diagonal are not
computed. For `n = 0`, require empty transform and swaps and `d = 1`.
For `.singular v`, require length `n` and a nonzero entry, and check
`[v] * A = [0, …, 0]` with dimensions `1 × n`, `n × n`, `1 × n`.
The singular witness cannot pass at `n = 0`.

### Bounds and selection

After compiled witness production and canonical list conversion, run
`sizeMulTerms` on every product above before packing or emitting any kernel
proof for the certificate. For each output coordinate the degree bound is
the componentwise maximum of `degree(Mᵢₜ) + degree(Aₜⱼ)` over `t` and
`degree(Cᵢⱼ)`; the coefficient bound is
`∑t ‖Mᵢₜ‖₁ ‖Aₜⱼ‖₁ + ‖Cᵢⱼ‖₁`. These include the input entries and the
actual witness, not just the entry degrees or atom count. Use Kronecker's
`SizeBound`, mixed-radix strides, base and saturating preflight unchanged;
no dense polynomial expansion or packed integer is built to choose the arm.
Each `checkMulTerms` call derives its own plan; its interface has no shared
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
by [hex-kronecker §Consumers](../../HexKronecker/SPEC/hex-kronecker.md#consumers), keyed by
`packedBits`, input supports and inner dimension. Require an eligible entry
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

`checkDetPolyPackedMod` uses `checkMulTermsMod` with canonical residue
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
[hex-bareiss §Symbolic coefficient growth](../../HexBareiss/SPEC/hex-bareiss.md#symbolic-coefficient-growth);
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
[benchmarking §Choosing the complexity claim](../benchmarking.md#choosing-the-complexity-claim).
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
[benchmarking](../benchmarking.md)'s shared-host discipline. The proof-level
comparison and default-family decision belong to the companion.

## File organisation

```
HexPolyDet/
  Basic.lean        -- polyDetWitness, polyDet, polyDetWitness?, the instance section
  Packed.lean       -- planned packed checks, bounds, quotient payload preparation
HexPolyDet.lean
```

When the packed implementation lands, the `libraries.yml` entry becomes

```yaml
  HexPolyDet:
    deps: [HexBareiss, HexMvGcd, HexDeterminant, HexMatrix, HexBasic, HexKronecker]
    mathlib: false
    done_through: 3
    status: active
```

## Consumers

[hex-poly-det-mathlib](hex-poly-det-mathlib.md), the symbolic `det`
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

The planned packed entry points are `checkDetPolyPacked` and
`checkDetPolyPackedMod` with the argument and payload contracts above.
Compiled quotient preparation belongs alongside them in `Packed.lean`;
its budget-decline outcome is distinct from a malformed or incorrect
certificate. The existing `polyDetWitness?` remains the list-validation API;
the handler additionally validates with its selected checker before quotation.
