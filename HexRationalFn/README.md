# HexRationalFn

Mathlib-free canonical univariate rational functions over
`[Lean.Grind.Field K] [DecidableEq K]`.

```lean
import HexRationalFn
open Hex

def transfer : RationalFn Rat :=
  1 / ((1 - RationalFn.X) * (1 - 2 * RationalFn.X))

#guard RationalFn.eval? transfer 0 = some 1
#guard RationalFn.eval? transfer 1 = none
```

The stored numerator and denominator are coprime, and the denominator is monic.
Equality compares canonical coefficient arrays. `normalize` and `ofFraction?`
construct values from polynomial pairs; the latter rejects a zero denominator.
Arithmetic cancels common factors before forming products. Explicit `With`
operations accept lawful multiplication plans; ordinary instances use Karatsuba
with cutoff 8. The same executable type is a `Lean.Grind.Field` and can serve
as the coefficient field for polynomial Euclidean algorithms.

`inv?` and `div?` reject zero, while field inversion and division are total.
`eval?` rejects canonical poles. Normalization removes removable singularities
and does not preserve an original expression's excluded inputs.
`derivative` is formal differentiation in any characteristic; `split` returns
a polynomial part and a proper fraction, and `toPoly?` tests polynomial membership.

`certifyWith` generates Bézout normalization certificates; `check` and
`ofCert?` replay them without gcd search. The soundness and completeness theorems,
field laws, canonical uniqueness and plan independence are proved without
new axioms or unfinished proofs.

See the [SPEC](SPEC/hex-rational-fn.md),
[manual chapter](../HexManual/Chapters/HexRationalFn.lean),
[Mathlib companion](../HexRationalFnMathlib/README.md), and
[performance report](../reports/hex-rational-fn-performance.md).

Verification:

```sh
lake build HexRationalFn HexRationalFnMathlib HexRationalFn.Conformance \
  hexrationalfn_emit_fixtures hexrationalfn_bench
python3 scripts/oracle/rationalfn_sympy.py < conformance-fixtures/HexRationalFn/rationalfn.jsonl
.lake/build/bin/hexrationalfn_bench verify
```
