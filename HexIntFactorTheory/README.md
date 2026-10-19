# hex-int-factor-theory

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence layer for
[`hex-int-factor`](https://github.com/leanprover/hex-int-factor). It identifies
checked executable factorizations with `Nat.factorization`, divisor functions,
squarefree decomposition, and Mathlib's multiplicative order. It also uses
[`hex-primality-theory`](https://github.com/leanprover/hex-primality-theory)
to transport the primality evidence carried by factor entries.

# Quickstart

```toml
[[require]]
name = "hex-int-factor-theory"
git = "https://github.com/leanprover/hex-int-factor-theory.git"
rev = "main"
```

```lean
import HexIntFactorTheory
open Hex
set_option maxRecDepth 100000

def twelve : Hex.Nat.CheckedFactorization 12 :=
  ⟨⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩, rfl, by decide⟩

example : Hex.Nat.totient twelve = Nat.totient 12 :=
  Hex.Nat.totient_eq twelve

example : (Hex.Nat.divisors twelve).toList.toFinset = Nat.divisors 12 :=
  Hex.Nat.divisors_eq twelve
```

# Functionality

- `factorization_entry`, `factorization_eq`, and
  `CheckedFactorization.factorization_eq` identify checked multiplicities with
  Mathlib's `Nat.factorization`.
- `factors_eq` and `CheckedFactorization.primeFactorsList_eq` identify the
  canonical expanded prime list.
- `divisors_eq`, `divisors_list_eq`, `numDivisors_eq_card`, `totient_eq`,
  `sigma_eq`, `primeFactors_eq`, and `radical_eq` transport executable divisor
  data and arithmetic functions.
- `isSquarefree_iff_squarefree`, `squarefreePart_mathlib`, and
  `squareDivisor_mathlib` connect the executable square decomposition to
  Mathlib's predicates and order-theoretic characterization.
- `orderOf_unitOfCoprime`, `orderOf_natCast`, and `orderOf_eq` identify the
  Mathlib-free natural order with Mathlib's `orderOf` on `ZMod` and its units.

# Optional mixed correspondence

Explicitly import `HexIntFactorTheory.Mixed` for `Hex.Nat.Mixed` soundness.
It uses `Hex.ECPP.natPrime_of_checkAt` from `HexECPPTheory.Soundness`
and existing legacy primality soundness. Checked complete data has exact
`Nat.factorization` multiplicities and complete prime support. Checked partial
data satisfies `n.factorization p = listedExponent p + residual.factorization p`;
a residual can overlap the listed support. The companion proves primality,
prime-support, exponent lower bounds, and exact multiplicity when the base does
not divide the residual.

Legacy umbrellas and theorems keep their existing replay closure. Existing
divisor, arithmetic-function, order and square-decomposition correspondence
accepts legacy checked data. Mixed data must pass checked `toLegacy`, which
rejects ECPP entries, or use a separately implemented consumer extension.
See the [mixed capability report](https://github.com/kim-em/hex-dev/blob/main/reports/intfactor/mixed/README.md).

# Verification

This library performs no factor search, certificate
replay, reification, or tactic execution; all transported values are computed
by `hex-int-factor`.

```lean
theorem CheckedFactorization.factorization_eq {n : Nat}
    (F : CheckedFactorization n) (p : Nat) :
    n.factorization p =
      (F.raw.factors.find? fun e => e.prime == p).elim 0 (·.exponent)

theorem orderOf_eq {c : OrderCert} (h : checkOrder c = true) :
    _root_.orderOf
        (ZMod.unitOfCoprime c.base (coprime_of_checkOrder h)) = c.order
```

Use [`hex-int-factor`](https://github.com/leanprover/hex-int-factor) alone for
computation. This package is for theorem statements and interoperability with
Mathlib. See the [SPEC](SPEC/hex-int-factor-theory.md) for the complete
correspondence boundary.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
