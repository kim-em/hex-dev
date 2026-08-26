# hex-smith-mathlib

Part of [`hex`](https://github.com/leanprover/hex), a computer algebra library
for Lean 4.

`hex-smith-mathlib` connects the executable integer Smith algorithm to
Mathlib. It constructs an explicit `Module.Basis.SmithNormalForm`, proves its
coefficients form the canonical divisibility chain, and gives the rank-general
decomposition of the presented quotient into a free module and cyclic factors.

```lean
import HexSmithMathlib

open Hex

#check HexSmithMathlib.smithNormalForm
#check HexSmithMathlib.smithNormalForm_chain
#check HexSmithMathlib.quotientEquiv
```

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo; released repositories are generated mirrors.
