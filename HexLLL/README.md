# hex-lll

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4.

`hex-lll` computes Lenstra-Lenstra-Lovász reduced bases for integer row
lattices without depending on Mathlib. It provides an exact integer reducer
and a checker that can certify the output of an optional external reducer.
Both methods return a reduced basis for the same lattice.

# Quickstart

Add the package to `lakefile.toml`:

```toml
[[require]]
name = "hex-lll"
git = "https://github.com/leanprover/hex-lll.git"
rev = "main"
```

Then check the executable operations:

```lean
import HexLLL

open Hex

#check @lll
#check @lll.firstShortVector
#check @lll.shortVectors
#check @lllNative
#check @lllReduced
#check @certCheck
```

These commands work in the Lean interpreter. Running the native reducer on a
concrete basis requires a compiled executable because its exact division
operation is supplied by native code.

# Functionality

`lll b δ` returns a `(δ, 11/20)`-reduced basis spanning the same row lattice
as `b`. Its proof arguments express `121/400 < δ`, `δ ≤ 1`, and a nonempty
basis. The `lll.firstShortVector` and `lll.shortVectors` operations select the
first row or all rows of the reduced basis.

`lllNative` is the exact integer reducer. It satisfies the tighter classical
size-reduction bound `1/2`. The ordinary `lll` operation may instead use an
external candidate after `certCheck` proves reducedness and equality of the
generated lattice. If no candidate is installed or the check fails, it uses
`lllNative`.

The public predicates include `Matrix.memLattice`, `Matrix.independent`,
`Vector.normSq`, `isLLLReduced`, and the executable reducedness checks
`lllReduced`, `lllReducedInterval`, and `lllReducedCheck`.

Detailed timings against fpLLL and the verified Isabelle extraction are in
[PERFORMANCE.md](PERFORMANCE.md).

# Verification

The Mathlib-free package proves the rational short-vector estimate from
reducedness and proves the lattice-preservation part of the external
certificate. [`hex-lll-mathlib`](https://github.com/leanprover/hex-lll-mathlib)
proves that both reducers satisfy their reducedness and lattice-preservation
contracts and states the short-vector theorem using Mathlib's Euclidean norm.

The external reducer is not trusted. Its candidate must pass the integer
checker before it can affect the result. See the
[SPEC](SPEC/hex-lll.md) for the exact contracts, implementation invariants,
and benchmark protocol.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
