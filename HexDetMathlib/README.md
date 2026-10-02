# hex-det-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4.

`hex-det-mathlib` is the correctness companion for `hex-det`. It owns no runtime
determinant, conformance driver, benchmark or tactic: `HexDet` is the
computational conformance and performance owner.

Every shipped arm is proved equal to the Leibniz reference determinant
`Hex.Matrix.det`, by composing the algorithm correspondences of
`hex-bareiss-mathlib` and `hex-char-poly-mathlib`, and dispatch is proved to
report only routes it is entitled to report.

```lean
import HexDetMathlib

open Hex

example (M : Matrix Int 3 3) : Hex.Det.det M = Matrix.det M :=
  HexDetMathlib.det_eq M

example (M : Matrix Int 3 3) :
    Hex.Det.det M = _root_.Matrix.det (HexMatrixMathlib.matrixEquiv M) :=
  HexDetMathlib.det_eq_mathlib M
```

Both sides of the first law are Mathlib-free expressions, but its proof is not:
a Mathlib-free proof of the Berkowitz determinant identity is future work.

Carriers with no global Mathlib ring structure, such as `Hex.DensePoly`,
`Hex.ZPoly` and `Hex.ZMod64`, reach these theorems through
`HexPolyMathlib.commRingOfGrind`, which keeps every executable operation, and
`HexPolyMathlib.toGrind_commRingOfGrind`, which records that its lightweight
reduct is the instance the carrier computes with.
