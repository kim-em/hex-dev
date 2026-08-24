# hex-number-field-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib companion for
[`hex-number-field`](https://github.com/leanprover/hex-number-field). It
interprets the executable algebraic-number types in `ℂ` and proves
fixed-field correspondence, canonicalization, lazy-arithmetic completeness,
semantic equality, and root-API completeness. It depends on
`hex-number-field` and the Mathlib companions of its inputs:
[`hex-resultant-mathlib`](https://github.com/leanprover/hex-resultant-mathlib),
[`hex-berlekamp-zassenhaus-mathlib`](https://github.com/leanprover/hex-berlekamp-zassenhaus-mathlib),
[`hex-roots-mathlib`](https://github.com/leanprover/hex-roots-mathlib), and
[`hex-poly-z-mathlib`](https://github.com/leanprover/hex-poly-z-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-number-field-mathlib"
git = "https://github.com/leanprover/hex-number-field-mathlib.git"
rev = "main"
```

```lean
import HexNumberFieldMathlib

open Hex

example : Function.Injective AlgebraicNumber.toComplex :=
  AlgebraicNumber.toComplex_injective

-- The Field instance's data fields are the executable operations.
example (a b : AlgebraicNumber) : a + b = AlgebraicNumber.add a b := rfl
```

# Functionality

The proof-facing API interprets each executable representation in `ℂ`:

- `Hex.AlgebraicRoot.toComplex` and `Hex.AlgebraicNumber.toComplex` select
  the semantic root; `Hex.AlgebraicNumber.p_eq_minpoly` identifies the
  stored polynomial with the minimal polynomial of that value.
- `Hex.QAdjoin.toComplex`, `Hex.QAdjoin.adjoinRootEquiv`, and
  `Hex.QAdjoin.embedding`: the reduced coordinates are ring-equivalent to
  the monic rational `AdjoinRoot` quotient, and the complex interpretation
  is a ring embedding. An opt-in scoped `Field` instance preserves the
  computational operations and rational scalar action.
- Completeness theorems (`add?_isSome`, `mul?_isSome`, `inv?_isSome`,
  `div?_isSome`, `exact?_isSome` and relatives) prove that the bounded
  certificate searches of the lazy layer always succeed, so the total
  wrappers compute the corresponding complex operations.
- `Hex.AlgebraicNumber.toComplex_injective`, `LawfulBEq`, and
  `DecidableEq`: Boolean equality decides equality of complex values.
- Root-API correctness for the fixed-field and algebraic-coefficient
  `roots?` functions.

# Verification

Everything in this package is proved; it adds no executable operations. The
lawful `Field AlgebraicNumber` instance is built over the unchanged
executable data, so proofs about the Mathlib structure are proofs about the
code that runs. The computational library stays Mathlib-free; complex
semantics live here. See the [SPEC](SPEC/hex-number-field-mathlib.md) and
the Hex manual's number-field chapter for the theorem chain.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
