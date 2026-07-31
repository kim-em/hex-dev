# hex-berlekamp-zassenhaus

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4.

This package factors dense univariate polynomials over `ℤ` without depending
on Mathlib. It combines modular Berlekamp factorization, multifactor Hensel
lifting, classical or lattice recombination, and exact trial division. The
result records the signed scalar separately from primitive factors and their
multiplicities.

# Quickstart

```toml
[[require]]
name = "hex-berlekamp-zassenhaus"
git = "https://github.com/leanprover/hex-berlekamp-zassenhaus.git"
rev = "main"
```

```lean
import HexBerlekampZassenhaus

open Hex

#check ZPoly.factorize
#check ZPoly.factors
#check Factorization.product
#check factorClassical
#check factorLattice
#check factorTrial
```

# Functionality

`ZPoly.factorize` is the total user operation. It normalizes content, sign,
powers of `X`, and repeated factors before factoring the primitive square-free
part. Small modular factorizations use classical subset recombination. Larger
ones use a lattice generated from coefficient vectors and logarithmic
derivatives. Exact trial division proves totality when modular methods do not
return an answer.

The ordinary umbrella also supplies `factor_poly` and `irreducibility` for
`Hex.ZPoly`. Search runs in compiled elaborator code and emits product and
irreducibility certificates checked by the kernel:

```lean
import HexBerlekampZassenhaus

open Hex

def f : ZPoly := DensePoly.ofCoeffs #[1, 0, 1]

noncomputable def fFactored := factor_poly f
theorem fIrreducible : ZPoly.Irreducible f := irreducibility f
```

Import `HexBerlekampZassenhaus.All` only when developing the algorithms and
their internal certificates.

# Verification

The computational package defines a Mathlib-free irreducibility predicate and
the executable checks needed by the proof library.
[`hex-berlekamp-zassenhaus-mathlib`](https://github.com/leanprover/hex-berlekamp-zassenhaus-mathlib)
proves product reconstruction, factor irreducibility, normalization, and
uniqueness.

The lattice method uses coefficient vectors of logarithmic derivatives in the
sense of van Hoeij. The exact trial method is independent of finding a
suitable prime, so the public factorization operation is total. See the
[SPEC](SPEC/hex-berlekamp-zassenhaus.md) for the algorithms, contracts, and
test protocol.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
