# hex-det

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4.

`hex-det` is the production determinant entry point for dense square matrices.
It adds no determinant algorithm: `Hex.Det.det` interprets a typed recipe,
running the `n ≤ 2` closed forms first and then the arm that recipe selects, and
reports which arms it attempted. Today the arms are fraction-free Bareiss from
[`hex-bareiss`](https://github.com/leanprover/hex-bareiss) on carriers with an
exact quotient, and the Samuelson--Berkowitz characteristic polynomial from
`hex-char-poly` on every other commutative ring.

The Leibniz reference determinant `Hex.Matrix.det` is untouched; `hex-det-mathlib`
proves every shipped arm equal to it.

# Quickstart

```lean
import HexDet

open Hex

def M : Matrix Int 3 3 := Matrix.ofFn fun i j => (i + 2 * j + 1 : Int)

#eval Hex.Det.det M                       -- the determinant
#eval (Hex.Det.DetOps.run M).route.completed  -- the arm that produced it
```

Importing the `HexDet` umbrella installs every carrier recipe. A consumer that
only needs one carrier can import its module, such as `HexDet.Int`; importing
only `HexDet.Basic` leaves every carrier on the generic Berkowitz default. A
partial import can change the arm a call selects, never its value.

# Choosing an arm explicitly

`Hex.Det.runWith` takes a recipe directly, which is how conformance forces each
available arm:

```lean
#eval (Hex.Det.runWith (Hex.Det.Policy.berkowitz inferInstance) M).value
#eval (Hex.Det.runWith (Hex.Det.quotientPolicy (R := Int)) M).value
```

A recipe is executable configuration. Its correctness is the law
`HexDetMathlib.LawfulPolicy`, not the recipe itself.
