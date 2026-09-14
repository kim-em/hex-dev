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

This is a specification. The library adds no algorithm: the witness,
producer and checker are hex-bareiss's generic ones
([hex-bareiss §Polynomial determinant certificate](../../HexBareiss/SPEC/hex-bareiss.md#polynomial-determinant-certificate)),
the exact quotient is hex-mv-gcd's, and the list arithmetic is
hex-mv-poly's.

## Scope and dependencies

In scope: `polyDetWitness` and `polyDet` over `MvPoly k C cmp` for a
coefficient domain `C` with `LawfulGcdOps C`; the checked `polyDetWitness?`
that returns the witness only when `checkDetPolyList` accepts it in
compiled code; the list-form instantiation of the checker with
hex-mv-poly's canonical arithmetic; conformance fixtures with a SymPy
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
`HexDeterminant`, `HexMatrix`, `HexBasic`; `libraries.yml` records the
planned entry and `scripts/check_dag.py` checks it.

## The instantiation

```lean
namespace Hex.PolyDet

variable {k : Nat} {C : Type u} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C] [DecidableEq C]
  [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [IsMonomialOrder cmp] [LawfulGcdOps C]

/-- hex-bareiss's generic polynomial witness producer at the multivariate
polynomial carrier, with hex-mv-gcd's exact quotient. -/
def polyDetWitness (P : Matrix (MvPoly k C cmp) n n) : Except String (DetWitness (MvPoly k C cmp) n) :=
  Hex.Matrix.detWitnessWith Hex.exactDiv P

def polyDet (P : Matrix (MvPoly k C cmp) n n) : MvPoly k C cmp
def polyDetWitness? (P : Matrix (MvPoly k C cmp) n n) : Option (DetWitness (MvPoly k C cmp) n)
```

`Hex.Matrix.detWitnessWith` and the carrier- and dimension-parametric
`DetWitness R n` are proposed changes to hex-bareiss, part of its
§Polynomial determinant certificate: today `DetWitness` is the integer
witness with no parameters and `detWitness` returns `Except String
DetWitness`. The generalisation keeps that failure behaviour (`Except`
with the producer's reason) and the integer API as a specialisation.
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

The producer is fraction-free elimination, `n³/3` polynomial products and
exact divisions whose cost is the realised support of the intermediate
minors, bounded as in
[hex-bareiss §Symbolic coefficient growth](../../HexBareiss/SPEC/hex-bareiss.md#symbolic-coefficient-growth);
expression swell is not controlled here. The checker is `n³/3` polynomial
products (or `n²` for the singular vector) at the witness's realised
support.

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

## File organisation

```
HexPolyDet/
  Basic.lean        -- polyDetWitness, polyDet, polyDetWitness?, the instance section
HexPolyDet.lean
```

`libraries.yml` gains

```yaml
  HexPolyDet:
    deps: [HexBareiss, HexMvGcd, HexDeterminant, HexMatrix, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
```

## Consumers

[hex-poly-det-mathlib](hex-poly-det-mathlib.md), the symbolic `det`
handler. A later polynomial-matrix library (Popov forms, approximant
bases) would import this rather than re-instantiate the certificate.
