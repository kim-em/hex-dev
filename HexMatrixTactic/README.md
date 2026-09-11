# hex-matrix-tactic

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-matrix-tactic` provides proof-producing `det`, `rank` and `char_poly`
frontends for executable `Hex.Matrix` inputs. Compiled code discovers the
value; the kernel replays a structural producer or a local certificate on the
matrix literal, so every result is a checked theorem with no trusted runtime
verdict. See [`hex-matrix-tactic-mathlib`](../HexMatrixTacticMathlib/README.md)
for the frontends on Mathlib matrices.

The design is [`SPEC/hex-matrix-tactic.md`](SPEC/hex-matrix-tactic.md).

# Quickstart

```lean
import HexMatrixTactic

open Hex
open scoped Hex

def A : Hex.Matrix Int 2 2 := #m[1, 2; 3, 4]

example : Matrix.bareiss A = -2 := by det
example : Matrix.rank A = 2 := by rank
example : Matrix.rank A ≤ 2 := by rank
example : Matrix.charPoly A = #p[-2, -5, 1] := by char_poly

#check det% A     -- Hex.MatrixTactic.Certified Matrix.bareiss A
#check rank% A    -- Hex.MatrixTactic.Certified Matrix.rank A
#check char_poly A
```

Supported carriers are `Int` (determinant by row-pivoted Bareiss, rank by the
`HexRank` domain producer, characteristic polynomial by the Berkowitz
certificate) and `Rat` (rank by field row reduction). A goal stated with
`Hex.Matrix.det` is replayed through its Leibniz expansion up to dimension 5.
