# hex-poly-det

Native determinants and checked witnesses for multivariate polynomial matrices.
`polyDet` evaluates the row-pivoted Bareiss algorithm using hex-mv-gcd's exact
quotient operation. It returns a polynomial value without constructing a proof
or requiring a supplied answer. `polyDetWitness` and `polyDetWitness?` separately
produce checked triangular or singular witnesses using hex-bareiss's generic
certificate API.

The library remains Mathlib-free. Its required dependencies are `HexBareiss`,
`HexMvGcd`, `HexMvPoly`, `HexDeterminant`, `HexMatrix` and `HexBasic`, with the
usual transitive coefficient-arithmetic dependencies. Soundness and successful-
producer-check theorems live in the Mathlib companion. Native computation and
symbolic proof construction are separate operations: the symbolic `det` handler
uses the contract in [hex-poly-det-mathlib](hex-poly-det-mathlib.md), not a mandatory
polynomial witness from this library.

## Scope

Retain the native value, witness, checked witness and budgeted producer APIs, plus
canonical list conversion and plain checker instantiation. Coefficient domains
supply the existing gcd/exact-division laws; no new assumptions are imposed by
the symbolic tactic. Dense univariate determinant values continue to use the
existing Bareiss carrier interface.

Determinant-specific packed/tree/residue selection is not a required API.
Remove those wrappers when they have no independent consumers, together with
their crossover tables and obsolete tests. Keep shared Kronecker mixed-product
checks in their owning library. Native witness validation continues through the
plain checker; removing an optional kernel encoding does not remove its checks.

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
`polyDetWitness?` returns a witness only when the compiled plain check accepts
it. The check is instantiated with the coefficient carrier's operations. Any
kernel-facing consumer must additionally supply the relevant soundness theorem
and representation laws; native witness production alone is not a Lean proof.

`Hex.PolyDet.produce` in `Basic.lean` instantiates `Hex.Matrix.detWitnessBudgeted` with
`MvPoly` support cardinality as its size measure, for both integer and
residue coefficient domains. Its intermediate budget governs round admission
by term-product counts and the total support of the retained blocks after
each round, as specified in hex-bareiss. Its certificate budget is checked
before the compiled self-check. Structured declines preserve the exhausted
budget name, count reached and limit to the caller. The caller supplies the
compiled checker for its serialization. The unlimited `polyDetWitness` API and
its error type stay intact.

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

## Complexity and benchmarking

Bareiss performs cubic many polynomial arithmetic operations, whose cost depends
on realized intermediate support and coefficient growth. `polyDet` need not
construct the additional witness transform. The witness and its compiled plain
check have their own costs and budget outcomes; a witness decline is not a
successful certified result. Worst-case minor counts are diagnostic, not a
substitute for actual producer budgeting.

Retain Mathlib-free native value/witness benchmarks and conformance fixtures
against the independent SymPy oracle. Include dense, structured, singular,
empty, coefficient-carrier and budget-boundary cases. Do not replace native
measurements with symbolic tactic timings. The companion owns manual proof
probes, result-producing interface checks and comparisons with Mathlib.

## Consumers and source organization

`Basic.lean` owns native evaluation, witness production and checker instantiation.
The companion retains their soundness theorems separately from its general
symbolic evaluator. Preserve APIs consumed by polynomial-matrix clients; update
imports and library registrations when retiring determinant-only encodings.
Keep conformance and oracle integration in the existing scripts and jobs.

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
