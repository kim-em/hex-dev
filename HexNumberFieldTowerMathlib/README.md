# hex-number-field-tower-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib companion for
[`hex-number-field-tower`](https://github.com/leanprover/hex-number-field-tower).
It interprets every validated tower as a finite extension of `ℚ` with a
fixed embedding into `ℂ` and proves the coordinate field operations,
Trager factorization, adjoining, splitting fields, and primitive-element
flattening correct. It depends on `hex-number-field-tower`,
[`hex-number-field-mathlib`](https://github.com/leanprover/hex-number-field-mathlib),
[`hex-resultant-mathlib`](https://github.com/leanprover/hex-resultant-mathlib),
[`hex-berlekamp-zassenhaus-mathlib`](https://github.com/leanprover/hex-berlekamp-zassenhaus-mathlib),
and
[`hex-row-reduce-mathlib`](https://github.com/leanprover/hex-row-reduce-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-number-field-tower-mathlib"
git = "https://github.com/leanprover/hex-number-field-tower-mathlib.git"
rev = "main"
```

```lean
import HexNumberFieldTowerMathlib

open Hex

example (T : NumberTower) : Function.Injective T.toComplex :=
  NumberTower.toComplex_injective T

example (T : NumberTower) (a b : NumberTower.Elem T) :
    T.toComplex (a + b) = T.toComplex a + T.toComplex b :=
  NumberTower.map_add T a b
```

# Functionality

The proof-facing API fixes one injective complex interpretation per tower
and transports the executable operations across it:

- `Hex.NumberTower.toComplex` with `Hex.NumberTower.toComplex_injective`:
  the fixed complex interpretation of tower elements.
- `Hex.NumberTower.map_add`, `map_mul`, and `map_inv`: coordinate
  arithmetic, including recursive extended-gcd inversion and the
  convention `0⁻¹ = 0`, computes the complex operations.
- The level invariant: each defining polynomial is irreducible over the
  semantic lower field, vanishes at its stored generator, and presents the
  coordinate quotient as adjoining exactly that generator.
- Correctness and completeness for the tower operations: `factor?` returns
  a genuine irreducible factorization, `adjoin?` selects the factor
  compatible with the fixed embedding, `split?` really splits, and
  `flatten?` produces a primitive element of full degree with mutually
  inverse coordinate maps.
- Total forms `Hex.NumberTower.adjoin`, `factor`, `split` and `flatten`:
  each unwraps the `Option`-valued operation with its completeness theorem,
  so `adjoin T a` is definitionally the extension `adjoin? T a` returns, and
  `adjoin?_eq_some` and its siblings rewrite one to the other.

# Verification

Everything in this package is proved; it adds no executable operations.
The sealed constructors of the computational package mean the level
invariant follows by induction over the smart constructors, so the
theorems cover every tower a client can build. The computational library
stays Mathlib-free; field structure and complex semantics live here. See
the [SPEC](SPEC/hex-number-field-tower-mathlib.md) for the theorem chain.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
