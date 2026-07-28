# hex-berlekamp-zassenhaus-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib correspondence theorems and proof-facing APIs for
[`hex-berlekamp-zassenhaus`](https://github.com/leanprover/hex-berlekamp-zassenhaus).

This package proves that the executable factorization reconstructs its input,
that every nonconstant returned factor is irreducible, that entries are
primitive, and that normalized factorizations are unique. It also provides
`factor_poly` and `irreducibility` for `Polynomial ℤ` and the stronger
certificate coverage available when Mathlib is present.

# Quickstart

```toml
[[require]]
name = "hex-berlekamp-zassenhaus-mathlib"
git = "https://github.com/leanprover/hex-berlekamp-zassenhaus-mathlib.git"
rev = "main"
```

```lean
import HexBerlekampZassenhausMathlib
```

# Functionality

For nonzero `f : Hex.ZPoly`,
`HexBerlekampZassenhausMathlib.factorize_headline f hf` packages the
release-facing result:

- the factorization product is exactly `f`;
- its scalar is the signed content prescribed by the normalization convention;
- every entry has positive multiplicity;
- every entry is primitive and irreducible; and
- distinct entries are not associates.

The sibling theorem
`HexBerlekampZassenhausMathlib.factorize_headline_contract_core_with_posLeading`
adds the positive-leading convention. Lower-level theorems such as
`HexBerlekampZassenhausMathlib.factorize_product`,
`HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit`, and
`HexBerlekampZassenhausMathlib.factorize_unique` are available when a client
wants only one part of the contract.

# Tactics for `Polynomial ℤ`

```lean
open Hex Polynomial

noncomputable def fac :=
  factor_poly ((X - 1) ^ 2 * (X ^ 2 + 1) : Polynomial ℤ)

example : Irreducible (X ^ 4 + 8 * X + 12 : Polynomial ℤ) := by
  irreducibility
```

The ordinary forms use untrusted compiled search and emit kernel-checked
product and irreducibility certificates. They cover single-prime Rabin,
Eisenstein-after-shift, and multi-prime degree-obstruction witnesses.

`factor_poly!` and `irreducibility!` are explicit fallbacks for small balanced
inputs outside those certificate languages. They make the kernel replay the
factorizer, have a strict degree budget, and require the executable closure to
be visible in module-based clients. Prefer the ordinary forms whenever they
apply; the bang forms are intentionally expensive and loudly named.

# Verification

The computational package is Mathlib-free. This bridge owns all statements in
terms of Mathlib's `Polynomial`, unique factorization, Gauss's lemma, and
correspondence with modular/Hensel data. Keeping that boundary explicit lets
runtime-only users avoid the Mathlib dependency while proof clients get the
full semantic contract.

See the [SPEC](SPEC/hex-berlekamp-zassenhaus-mathlib.md) and the Hex manual's
factor-tactics chapter for theorem maps, certificate coverage, examples, and
the trust model.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
