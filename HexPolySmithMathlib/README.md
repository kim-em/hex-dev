# hex-poly-smith-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. `hex-poly-smith-mathlib` is the Mathlib bridge for
[`hex-poly-smith`](https://github.com/leanprover/hex-poly-smith). It transports
the executable Smith data to `Polynomial F`, builds Mathlib's Smith-basis
structure, decomposes the presented quotient module, and identifies the rank
over `F(x)`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-poly-smith-mathlib"
git = "https://github.com/leanprover/hex-poly-smith-mathlib.git"
rev = "main"
```

```lean
import HexPolySmithMathlib

open Hex Hex.PolyMatrix HexPolySmithMathlib

#check @polyMatrixEquiv
#check @smithNormalForm
#check @smithNormalForm_chain
#check @quotientEquiv
#check @rank_eq_ratFunc_rank
```

# Functionality

- `polyMatrixEquiv` maps executable dense polynomial matrices entrywise to
  Mathlib matrices over `Polynomial F` and commutes with addition and
  multiplication;
- `monicize_eq_normalize` identifies Hex's monic representative with
  Mathlib's normalization;
- `smithNormalForm` realizes the row-span presentation using
  `Module.Basis.SmithNormalForm`;
- `smithNormalForm_chain` restores the canonical divisibility order not stored
  in Mathlib's simultaneous-basis structure;
- `quotientEquiv` gives the free-plus-cyclic-torsion decomposition;
- `rank_eq_ratFunc_rank` equates `snfRank` with matrix rank after extension to
  `RatFunc F`.

# Verification

This library is correspondence-only. Every declaration is a proof or a
noncomputable equivalence built from the verified output of `hex-poly-smith`.
Executable conformance and performance evidence therefore remain owned by the
Mathlib-free package.

The headline rank theorem is:

```lean
theorem rank_eq_ratFunc_rank (A : Hex.Matrix (DensePoly F) n m) :
    snfRank A =
      ((polyMatrixEquiv A).map
        (algebraMap (Polynomial F) (RatFunc F))).rank
```

# Reference manual

The Mathlib correspondence section of the hex reference manual covers this
library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-poly-smith-mathlib>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in the published mirror. Contributions are welcome as pull
requests to the monorepo.
