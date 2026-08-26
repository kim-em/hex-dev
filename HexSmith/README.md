# hex-smith

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. `hex-smith` computes Smith normal form for rectangular integer
matrices. The computational library is Mathlib-free; its correspondence with
Mathlib bases and quotient modules lives in
[`hex-smith-mathlib`](https://github.com/leanprover/hex-smith-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-smith"
git = "https://github.com/leanprover/hex-smith.git"
rev = "main"
```

```lean
import HexSmith

open Hex Hex.Matrix

def A : Matrix Int 2 2 := #m[2, 0; 0, 6]

#eval (snf A).rows
#eval (invariantFactors A).toList  -- [2, 6]
#eval abelianStructure A

-- Ask for certified transforms and their explicit inverses only when needed.
#eval (snfData A).left
```

# Functionality

- `snf`, `snfRank`, and `invariantFactors` compute the canonical form, rank,
  and divisibility chain without accumulating transformation matrices;
- `snfData` additionally returns left and right unimodular transforms and
  explicit inverses, while `smithBasis` returns independent relation rows;
- `snfDiagonal` bypasses elimination for diagonal input, and
  `snfDiagonalData` supplies the corresponding certified transforms;
- `snfCert` independently checks supplied Smith data;
- `solvable_iff_dvd`, `latticeIndex_eq_invariantFactors`, and
  `abelianStructure` expose system, lattice-index, and presentation APIs;
- `detDivisor` defines determinantal divisors independently of the algorithm
  and supports uniqueness proofs. Direct evaluation enumerates exponentially
  many minors; compute values through `invariantFactors` instead.

# Verification

`snfData_isSNF` proves the inverse identities, transformed-input identity,
rank bounds, positivity, and divisibility chain. Determinantal divisors prove
the rank and invariant factors unique. `snfCert_sound` turns acceptance by the
direct Boolean checker into the same logical contract.

The committed conformance corpus checks canonical diagonal data independently
with FLINT and checks non-unique transforms and their inverses in Lean. The
benchmark suite records scientific dimension ladders, coefficient growth,
diagonal routing, transform overhead, FLINT/PARI comparisons, and profiles.
The executable path is native Lean and has no runtime oracle dependency.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in the published mirror. Contributions are welcome as pull
requests to the monorepo.
