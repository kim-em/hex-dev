# hex-poly-fp-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence layer for
[`hex-poly-fp`](https://github.com/leanprover/hex-poly-fp). It relates the
executable prime-field polynomials `Hex.FpPoly p` to Mathlib's
`Polynomial (ZMod p)` through a ring equivalence, and transports
coefficients, monicity, arithmetic, derivatives, and divisibility across
it. It builds on
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib) and
[`hex-mod-arith-mathlib`](https://github.com/leanprover/hex-mod-arith-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-poly-fp-mathlib"
git = "https://github.com/leanprover/hex-poly-fp-mathlib.git"
rev = "main"
```

```lean
import HexPolyFpMathlib

noncomputable example {p : Nat} [Hex.ZMod64.Bounds p] :
    Hex.FpPoly p ≃+* Polynomial (ZMod p) :=
  HexPolyFpMathlib.fpPolyEquiv
```

# Functionality

The package exposes the correspondence between the executable prime-field
polynomials and Mathlib's:

- `fpPolyEquiv : Hex.FpPoly p ≃+* Polynomial (ZMod p)`, with
  `toMathlibPolynomial` as the forward map named for use in statements.
- Coefficient and monicity transport (`coeff_toMathlibPolynomial`,
  `toMathlibPolynomial_monic`).
- Transport lemmas for addition, multiplication, subtraction, derivatives,
  constants, `X`, monomials, and divisibility.
- A `CommRing (Hex.FpPoly p)` instance whose operations are the executable
  ones, proved from the ring laws `HexPolyFp` establishes.

# Verification

The headline result is the ring equivalence:

```lean
def fpPolyEquiv : Hex.FpPoly p ≃+* Polynomial (ZMod p)
```

The equivalence and transport lemmas are stated under the executable bounds
hypothesis `Hex.ZMod64.Bounds p`; lemmas that need `p` prime say so in their
own hypotheses, and `primeModulus_of_fact` derives the executable
prime-modulus witness from `Fact (Nat.Prime p)`. Runtime-only clients should
depend on
[`hex-poly-fp`](https://github.com/leanprover/hex-poly-fp); this package is
for theorem statements and interoperability involving Mathlib. See the
[SPEC](SPEC/hex-poly-fp-mathlib.md) for the correspondence contract and
ownership boundaries.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
