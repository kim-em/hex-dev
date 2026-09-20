# Shared real polynomial formulas

`HexRealFormula` is the Mathlib-free language shared by real-arithmetic
algorithms. `HexRealFormulaMathlib` supplies real semantics, normalization
proofs and the common reifier. The [SPEC](../SPEC/Libraries/hex-real-formula.md)
defines the public contract; [the tutorial](../HexRealFormulaMathlib/README.md)
connects that contract to source propositions and RCF.

```lean
import HexRealFormula

open Hex Hex.RealFormula

-- Coordinate 0 is the free parameter a; coordinate 1 is x.
def inequality : QF 2 :=
  .atom ⟨MvPoly.X 1 ^ 2 + MvPoly.C 2 * MvPoly.X 0 * MvPoly.X 1 - MvPoly.C 3, .le⟩

def problem : Prenex 1 := .quant .existsReal (.matrix inequality)
```

The arity of `Prenex 1` counts its free parameters. Its matrix has two
coordinates because the existential binder appends `x`. `toProp` never
silently universally closes the free parameters.

`QF` supports structural equality, `nodeCount`, `polys`, `support`, `degree`,
`rename`, `lift`, checked `drop?`, checked `moveLast?`, `nnf`, `imp`, `iff`,
`toKernel`, `ofKernel?` and exact `evalRat`. `degree i` is the maximum exponent
of coordinate `i` after polynomial normalization, including zero for the zero
polynomial. `rename` maps source indices to target indices and permits
collisions. `drop?` succeeds only when every atom is independent of that index.
`moveLast?` checks the selected index and exchanges it with the final one.

`Prenex.toView` exposes the ordered prefix and its correctly sized matrix;
`ofView` reconstructs it. `rename` acts only on free parameters. `swap?`
exchanges two adjacent quantifiers only when they have the same kind, and
renames the corresponding matrix coordinates. Exchanging an existential and
a universal quantifier is rejected.

Kernel encodings carry a version and explicit arity. Decode validates every
exponent-vector length before normalizing, including zero terms and unused
Boolean branches. DAG decode checks all nodes and input identifiers, requires
references to earlier nodes, and produces the ordinary tree semantics. A
validated kernel formula evaluates with list arithmetic. The wire format and
independent oracle are documented with the
[JSONL fixtures](../conformance-fixtures/HexRealFormula/README.md).

`evalRat` interprets quantifier-free formulas at exact rational points.
It does not search rationals to interpret real quantifiers. For example,
`∃ x : ℝ, x² = 2` is true despite having no rational witness.

Run the core checks and the independent oracle with:

```sh
lake build +HexRealFormula.Conformance
HEX_LIBRARY_FILTER=HexRealFormula scripts/ci/run_oracles.sh
```
