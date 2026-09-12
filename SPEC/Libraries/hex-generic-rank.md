# hex-generic-rank (rank of polynomial matrices, depends on hex-rank and hex-mv-gcd)

The generic rank of a matrix with multivariate polynomial entries: the rank
over the fraction field `Frac(C)(x_1, …, x_k)`, certified by
[hex-rank](../../HexRank/SPEC/hex-rank.md)'s two-sided certificate at the
carrier `MvPoly k C cmp`. This is the one-line instantiation that
[hex-rank §Placement](../../HexRank/SPEC/hex-rank.md#placement) assigns to
its first consumer, placed in a library above `HexMvGcd`, and it is the
executable half of the symbolic arm of the `rank` tactic. The companion
[hex-generic-rank-mathlib](hex-generic-rank-mathlib.md) owns the three
outputs a symbolic rank may take on a Mathlib goal (generic, conditional,
locus), the tactic handler that produces them, and their soundness.

This is a specification. The library adds no algorithm: the producer,
checker and certificate are hex-rank's, the exact quotient is hex-mv-gcd's,
and the polynomial arithmetic is hex-mv-poly's.

## Why this library exists

[hex-rank](../../HexRank/SPEC/hex-rank.md) proves its certificate sound and
complete over every integral domain, but `HexRank` cannot depend on
`HexMvPoly` or `HexMvGcd` (`scripts/check_dag.py`), so the `MvPoly`
instantiation lives only in hex-rank's build-only conformance and bench
modules. A production consumer that wants a named rank of a polynomial
matrix has to define it in a library above both, and hex-rank names the
symbolic `rank` tactic and `rank_locus` as the first such consumers. This
library is that definition, with the fixture families and benches that
make polynomial-entry rank a supported operation rather than a typeclass
accident.

The name is the operation. "Generic rank" is the standard term for the
rank of a polynomial matrix over the fraction field of its coefficient
ring, as opposed to the rank of any specialisation; the distinction is the
whole content of the companion's three outputs.

## Scope and dependencies

In scope: `genericRankWith`, `genericCertWith` and `genericRank` over
`MvPoly k C cmp` for a coefficient domain `C` with `LawfulGcdOps C`; the
Mathlib-free statement that the certified `r` is the largest size of a
nonzero minor; conformance fixtures with a SymPy oracle; and lean-bench
families. The Mathlib-free goal form
`Hex.Matrix.rankWith Hex.exactDiv P = r` for a closed polynomial literal
`P` is hex-rank's obligation on `Hex.Matrix` inputs
([matrix-tactics §Placement](../matrix-tactics.md#placement)) and is not
restated here.

Out of scope: reification of Lean expressions (hex-reflect), any statement
about a specialised matrix (the companion), determinantal ideals and the
locus (hex-determinantal-ideal), and univariate polynomial matrices over
`F[x]`, whose rank hex-poly-smith already certifies through `snfRank` and
`rank_eq_ratFunc_rank`; the `DensePoly` instantiation of hex-rank's
certificate stays in hex-rank's conformance modules.

Dependencies: `HexRank`, `HexMvGcd` (hence `HexMvPoly`, `HexResultant`),
`HexBareiss`, `HexDeterminant`, `HexMatrix`, `HexBasic`. `libraries.yml`
records the planned entry; `scripts/check_dag.py` checks it.

## The certificate at `MvPoly`

```lean
namespace Hex.GenericRank

variable {k : Nat} {C : Type u} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C] [DecidableEq C]
  [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [IsMonomialOrder cmp] [LawfulGcdOps C]

/-- hex-rank's producer at the multivariate polynomial carrier. -/
def genericCert (P : Matrix (MvPoly k C cmp) n m) : RankCert (MvPoly k C cmp) n m :=
  Hex.Matrix.rankCertWith Hex.exactDiv P

def genericRank (P : Matrix (MvPoly k C cmp) n m) : Nat :=
  Hex.Matrix.rankWith Hex.exactDiv P
```

The exact quotient is `Hex.MvPoly.instDiv` with its law
`Hex.MvPoly.instExactDivLaws` from `HexMvGcd/Divide.lean`, which needs
`[LawfulGcdOps C]`; `HexMvGcd/Instances.lean` supplies it for `Int`, `Rat`
and `ZMod64 p` (under `ZMod64.Bounds p`). `DomainLaws (MvPoly k C cmp)` is
`DomainLaws.of_exactDivLaws` with `LawfulGcdOps.one_ne_zero`. The term
order is fixed at `Hex.Mono.grevlex`, whose `IsMonomialOrder`,
`Std.TransCmp` and `Std.LawfulEqCmp` instances exist; a consumer that
needs another order instantiates the section itself.

The certificate `c := genericCert P` is closed data: `c.rank = r`,
`c.denom` a nonzero polynomial `d` (a signed `r × r` minor of `P`,
`sign π · det B` for the producer's row order `π`, per
[hex-rank §Entry points](../../HexRank/SPEC/hex-rank.md#entry-points)), and
`c.adj` a polynomial matrix. `checkRank P c = true` by producer
correctness (`rankCertWith_check` in hex-rank-mathlib), and hex-rank's
Mathlib-free `RankCert.det_ne_zero` and `RankCert.det_succ_eq_zero` at `P`
say that `r` is the largest size of a nonzero minor of `P`. That is the
Mathlib-free content of "generic rank"; the fraction-field statement is
the companion's.

`d` is the datum every consumer reads. It is the condition of the
companion's conditional output, and its vanishing set contains the locus
where the rank drops (`d ∈ I_r(P)`, so `V(I_r(P)) ⊆ V(d)`; the inclusion
is strict in general, see the companion).

## Coefficient carriers

| `C` | `LawfulGcdOps` source | fixture family | oracle |
|---|---|---|---|
| `Int` | `HexMvGcd/Instances.lean` | two- and three-variable integer matrices of generic full rank, of known low rank (products of `n × r` and `r × m` polynomial factors, so `r` and a nonzero `r`-minor are known at generation), and with repeated subexpressions | SymPy `Matrix.rank()` over `ZZ[x0, …]` through its fraction-field domain |
| `Rat` | same | the same shapes with rational coefficients | SymPy over `QQ[x0, …]` |
| `ZMod64 p` | same, under `ZMod64.Bounds p` | the same shapes at a fixed prime below `2^31`, plus `[X^p − X]`-style entries vanishing at every base-field point | SymPy over `GF(p, symmetric=False)[x0, …]` |

Each record stores the realised support of the entries, the expected
generic rank, and the expected `denom` up to sign; the oracle checks the
rank, and the checker `checkRank P c` replayed in compiled code checks the
certificate. The three worked examples of the companion are fixtures.
Emission follows hex-rank's fixture encoding for `MvPoly` entries (ordered
exponent-vector terms, residues in `[0, p)`), to
`conformance-fixtures/HexGenericRank/generic.jsonl`, with a tuple in
`scripts/ci/run_oracles.sh` and a handler in the existing
`scripts/oracle/matrix_carriers.py`; no new package, workflow or job
(SPEC/CI.md).

## Complexity

`P` is `n × m` of generic rank `r` in `k` variables. The producer is
hex-rank's rectangular fraction-free Gauss–Jordan, `O(n · m · r)`
polynomial operations, each an exact multivariate division or product
whose cost is the realised support of the intermediate minors, bounded by
[hex-bareiss §Symbolic coefficient growth](../../HexBareiss/SPEC/hex-bareiss.md#symbolic-coefficient-growth):
every intermediate is a minor of `P`, so there are no rational
denominators, but expression swell in the minors is not controlled here.
The checker is `n · r · m` polynomial products at the certificate's
realised support. Evaluation and interpolation and modular techniques for
polynomial matrices are a later SPEC and are not substituted silently.

## Benchmarking

The `symbolic` family: dimensions `2, 4, 8`, variables `1, 2, 4, 8`, degree
`1, 2, 4`, support `1, 4, 16`, at `C = Int`, with generic full rank and
known low rank as above. Registrations in `bench/HexGenericRank/Bench.lean`
(Mathlib-free) register the producer and the compiled checker separately,
checker preparation holding a precomputed certificate. Support and degree
ladders are not one cubic model, so each registration states its mode under
[benchmarking §Choosing the complexity claim](../benchmarking.md#choosing-the-complexity-claim);
the fixed-workload registrations use mode 3 with preregistered absolute
ceilings from the first measurement. The report
`reports/hex-generic-rank-performance.md` records producer time, compiled
checker time, the certificate size (term count and maximum degree of
`denom`, total term count of `adj`, serialised bytes), and the realised
intermediate support of the producer.

There is no external comparator: python-flint has no multivariate
polynomial matrices, and SymPy's fraction-field rank is a Python-process
oracle used for conformance, not a timed comparator. The absence is declared
as **no-comparable-surface-in-named-comparator** for these targets, per
[benchmarking](../benchmarking.md).

## File organisation

```
HexGenericRank/
  Basic.lean        -- genericCert, genericRank, the instance section, minor facts
  Conformance.lean  -- build-only guards (in conformance/)
HexGenericRank.lean
```

`libraries.yml` gains

```yaml
  HexGenericRank:
    deps: [HexRank, HexMvGcd, HexBareiss, HexDeterminant, HexMatrix, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
```

## Consumers

- [hex-generic-rank-mathlib](hex-generic-rank-mathlib.md): the three
  outputs and the `rank` tactic's symbolic handler.
- `rank_locus` (later SPEC, see
  [hex-determinantal-ideal §Consumers](../../HexDeterminantalIdeal/SPEC/hex-determinantal-ideal.md#consumers)):
  takes `r := (genericCert P).rank` as its default threshold and runs
  `detIdealGens r P` on the same `P`.

## Open questions

- **A kernel form of the polynomial certificate.** The companion's
  conditional output checks `d • P = C * (adj * P_rows)` in the kernel as a
  polynomial identity. Whether that needs a list-structured kernel form of
  `MvPoly` arithmetic (as `RankWitness` is for `Int`), or whether the
  identity is small enough at the target sizes to check through the
  reference representation, is a measurement the companion's proof probes
  settle. The lower bound needs no polynomial arithmetic in the kernel at
  all, see the companion.
- **Univariate specialisation.** At `k = 1` the same certificate competes
  with hex-poly-smith's `snfRank`; whether one routes to the other is
  decided by the benchmark, not here.
