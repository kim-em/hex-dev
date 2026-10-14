# hex-berlekamp-zassenhaus-theory

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4.

This package proves the mathematical specification of
[`hex-berlekamp-zassenhaus`](https://github.com/leanprover/hex-berlekamp-zassenhaus).
It relates `Hex.ZPoly` to `Polynomial ℤ`, proves that executable
factorizations reconstruct their inputs, and proves irreducibility,
normalization, and uniqueness of the returned factors.

# Quickstart

```toml
[[require]]
name = "hex-berlekamp-zassenhaus-theory"
git = "https://github.com/leanprover/hex-berlekamp-zassenhaus-theory.git"
rev = "main"
```

```lean
import HexBerlekampZassenhausTheory

#check HexBerlekampZassenhausTheory.factorize_product
#check HexBerlekampZassenhausTheory.factorize_normalized
#check HexBerlekampZassenhausTheory.factorize_unique
#check Hex.ZPoly.Irreducible_iff_polynomialIrreducible
```

# Functionality

For nonzero `f`, `factorize_normalized f hf` proves that the result has the
prescribed signed content, positive multiplicities, primitive irreducible
factors with positive leading coefficients, no associated duplicates, and
product equal to `f`.

The ordinary umbrella supplies `factor_poly` and `irreducibility` for
`Polynomial ℤ` as well as `Hex.ZPoly`. The usual forms use compiled search and
emit certificates. The explicitly expensive `factor_poly!` and
`irreducibility!` forms replay the factorizer in the kernel for small
polynomials outside the ordinary certificate languages.

```lean
import HexBerlekampZassenhausTheory

open Polynomial

noncomputable def fac :=
  factor_poly ((X - 1) ^ 2 * (X ^ 2 + 1) : Polynomial ℤ)

example : Irreducible (X ^ 4 + 8 * X + 12 : Polynomial ℤ) := by
  irreducibility
```

Import `HexBerlekampZassenhausTheory.All` only when developing the detailed
modular, Hensel, lattice, and recombination proofs.

# Verification

The principal proof surface is `FactorSoundness.lean`. The detailed modules
relate modular factors to unique Hensel lifts, use logarithmic derivatives to
recover support partitions, prove both classical and lattice recombination
complete under their stated hypotheses, and prove the exact trial
factorization irreducible.

See the [SPEC](SPEC/hex-berlekamp-zassenhaus-theory.md) for the theorem map,
certificate languages, and trust assumptions.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
