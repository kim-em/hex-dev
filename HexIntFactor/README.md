# hex-int-factor

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified natural-number factorization, divisor functions, multiplicative
orders, and primitive roots for Lean 4, without Mathlib. It builds on
[`hex-primality`](https://github.com/leanprover/hex-primality),
[`hex-arith`](https://github.com/leanprover/hex-arith), and
[`hex-basic`](https://github.com/leanprover/hex-basic). Correspondence with
Mathlib's factorization and order APIs lives in
[`hex-int-factor-mathlib`](https://github.com/leanprover/hex-int-factor-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-int-factor"
git = "https://github.com/leanprover/hex-int-factor.git"
rev = "main"
```

```lean
import HexIntFactor
open Hex Hex.Nat
set_option maxRecDepth 100000

def twelve : CheckedFactorization 12 :=
  ⟨⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩, rfl, by decide⟩

#guard checkFactorization twelve.raw
#guard divisors twelve == #[1, 2, 3, 4, 6, 12]
#guard totient twelve == 4
#guard squarefreePart twelve == 3
#guard squareDivisor twelve == 2
```

# Functionality

- `factor?` searches for a complete checked factorization with explicit
  randomness and a finite fuel budget. `factorPartial?` retains a checked
  residual when complete search exhausts its budget.
- `checkFactorization` and `checkPartial` replay untrusted factorization data.
  Prime entries carry `hex-primality` certificates, and bounded products reject
  oversized powers before constructing them.
- `divisors`, `numDivisors`, `sigma`, `totient`, `radical`, `squarefreePart`,
  `squareDivisor`, and `isSquarefree` compute from a `CheckedFactorization`.
- `checkOrder`, `isPrimitiveRoot`, and `primitiveRoot?` use a complete
  factorization of the proposed order. `carmichael` computes the Carmichael
  exponent from a complete factorization.
- `rhoSplit?`, `pMinusOneFactor`, and `ecmStage1` expose the individual split
  routes. `factorPower?` adds a cyclotomic pre-split for `b ^ n ± 1`.

# Verification

Every accepted complete certificate has positive subject, canonical positive
prime-power entries, exact product, complete prime support, and exact
multiplicities:

```lean
theorem checkFactorization_prod {F : Factorization}
    (h : checkFactorization F = true) :
    (F.factors.map (fun e => e.prime ^ e.exponent)).prod = F.subject

theorem checkFactorization_primeSupport {F : Factorization}
    (h : checkFactorization F = true) {q : Nat} (hq : Prime q) :
    q ∣ F.subject ↔ ∃ e ∈ F.factors, e.prime = q
```

Factor search is deliberately partial: zero, exhausted search, and internal
checker rejection are distinct `FactorStop` cases, with the advanced random
state and checked partial snapshot retained where available. Split algorithms
are untrusted producers; only Lean-checked certificates cross the public
correctness boundary. See the [SPEC](SPEC/hex-int-factor.md) for the route and
fuel contracts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
