# hex-smith

Part of [`hex`](https://github.com/leanprover/hex), a computer algebra library
for Lean 4.

`hex-smith` computes Smith normal form for rectangular integer matrices. It
provides form-only and fully certified transform paths, canonical invariant
factors, determinantal divisors, integer-system solvability criteria, abelian
group presentation data, and an independently checkable certificate.

# Quickstart

```lean
import HexSmith

open Hex

def A : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => #[#[2, 0], #[0, 3]][i.val]![j.val]!

#eval (Matrix.snf A).rows
#eval (Matrix.invariantFactors A).toList
#eval Matrix.abelianStructure A
```

# Verification

`snfData_isSNF` proves the accumulated left and right transforms and their
inverses, the diagonal identity, positivity, and the divisibility chain.
Determinantal divisors prove uniqueness of the rank and invariant factors.
The form-only and full-data implementations share one deterministic schedule.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo; released repositories are generated mirrors. Make changes in the
monorepo rather than editing a released repository directly.
