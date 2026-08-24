# hex-sparse-poly-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-sparse-poly-mathlib` is the Mathlib correspondence layer for
[`hex-sparse-poly`](https://github.com/leanprover/hex-sparse-poly). It
identifies the executable canonical sparse representation with Mathlib's
`Polynomial R` and transports one correspondence lemma per public
operation. It depends on Mathlib,
[`hex-sparse-poly`](https://github.com/leanprover/hex-sparse-poly), and
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-sparse-poly-mathlib"
git = "https://github.com/leanprover/hex-sparse-poly-mathlib.git"
rev = "main"
```

```lean
import HexSparsePolyMathlib

open Hex HexSparsePolyMathlib

#check (equiv : SparsePoly Int ≃+* Polynomial Int)

example (p q : SparsePoly Int) : equiv (p * q) = equiv p * equiv q :=
  map_mul equiv p q

example (p : SparsePoly Int) (x : Int) : (equiv p).eval x = p.eval x := by
  simp
```

# Functionality

- The ring equivalences `denseEquiv` (with the executable dense
  representation) and `equiv` (with Mathlib's `Polynomial R`), both at
  `[CommRing R] [DecidableEq R]`.
- The coefficientwise identification `coeff_equiv` and the support
  characterisation `equiv_support`.
- Operation correspondence: `equiv_eval`, `equiv_derivative`,
  `equiv_compose`, `equiv_substPow`, `equiv_substScale`, and the
  constructor and observer images `equiv_monomial`, `equiv_C`,
  `equiv_X`, `equiv_natDegree`, `equiv_leadingCoeff`, `equiv_monic`.

# Verification

Everything is proved; there is no axiom and no `sorry`. The headline is
the exact identification and its two semantic clauses:

```lean
theorem coeff_equiv (s : Hex.SparsePoly R) (e : Nat) :
    (equiv s).coeff e = s.coeff e
theorem equiv_support (s : Hex.SparsePoly R) :
    (equiv s).support = s.support.toList.toFinset
```

The executable operations, their kernel-facing specifications, and the
Mathlib-free algebra live in
[`hex-sparse-poly`](https://github.com/leanprover/hex-sparse-poly); the
dense-side equivalence this layer composes with lives in
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this
published mirror. Contributions are welcome as pull requests to the
`SPEC/` directory there: describe the behaviour you want and leave the
implementation to the maintainer.
