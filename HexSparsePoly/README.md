# hex-sparse-poly

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-sparse-poly` provides canonical sparse univariate polynomials: sorted
term arrays whose costs scale with the number of stored terms rather than
the degree. It depends on
[`hex-basic`](https://github.com/leanprover/hex-basic) and
[`hex-poly`](https://github.com/leanprover/hex-poly), with explicit
conversions to and from the dense representation. See
[`hex-sparse-poly-mathlib`](https://github.com/leanprover/hex-sparse-poly-mathlib)
for the correspondence with Mathlib's `Polynomial`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-sparse-poly"
git = "https://github.com/leanprover/hex-sparse-poly.git"
rev = "main"
```

```lean
import HexSparsePoly

open Hex Hex.SparsePoly

def p : SparsePoly Int := #sp[(0, 3), (1, -2), (1000000, 1)]
def q : SparsePoly Int := #sp[(1, 2), (1000000, -1)]

#eval (p + q).numTerms                 -- 1: two cancellations
#eval (p * q).coeff 2000000            -- -1
#eval (p.substPow 3).degree?           -- some 3000000
#eval #sp[(0, 1), (2, 3)].eval (5 : Int)  -- 76
#eval (p.derivative).coeff 999999      -- 1000000
```

# Functionality

- Canonical construction from arbitrary term arrays (`ofTerms`, `addTerm`,
  `monomial`, `C`, `X`, the `#sp[...]` literal), with structural decidable
  equality.
- Term-count-scaled arithmetic: `add` as a linear merge, `mul` with a
  measured `Std.ExtTreeMap` accumulation implementation, `mulMonomial`,
  `scale`, `pow`, `neg`, `sub`.
- Gap-Horner evaluation (`eval`), `derivative`, exponent substitution
  `substPow`, argument scaling `substScale`, and full composition
  (`compose`).
- Explicit dense conversions (`toDense`, `ofDense`) and a Euclidean layer
  routed through them (`divModMonic`, `divMod`, `gcd`, `divExactMonic?`),
  plus the one division that stays sparse, `divMonomial?`.

# Verification

Every operation carries a kernel-facing specification whose compiled
implementation is selected by a proved `@[csimp]` equality, and every
public operation has a coefficient lemma; equalities reduce to
coefficient extensionality:

```lean recall Hex.SparsePoly.ext_coeff
theorem ext_coeff {R : Type u} [Zero R] [DecidableEq R]
    {s t : SparsePoly R}
    (h : ∀ e : Nat, s.coeff e = t.coeff e) : s = t
```

The ring laws are proved under the `Lean.Grind` algebra classes, the
multiplicative laws by transport through the proved dense conversion
homomorphism. The division and gcd laws transport from `hex-poly`'s
`DivModLaws`/`GcdLaws` packages. The identification with Mathlib's
`Polynomial` (including the support characterisation that makes the
representation "sparse") lives in
[`hex-sparse-poly-mathlib`](https://github.com/leanprover/hex-sparse-poly-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this
published mirror. Contributions are welcome as pull requests to the
`SPEC/` directory there: describe the behaviour you want and leave the
implementation to the maintainer.
