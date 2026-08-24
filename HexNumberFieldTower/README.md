# hex-number-field-tower

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Executable successive algebraic extensions of `ℚ`, implemented in Lean 4
without Mathlib. A tower is a field with a fixed embedding into `ℂ`: every
level records an irreducible defining polynomial over the preceding tower
and the absolute certified root chosen as its generator. The package builds
on [`hex-number-field`](https://github.com/leanprover/hex-number-field),
[`hex-resultant`](https://github.com/leanprover/hex-resultant), and
[`hex-berlekamp-zassenhaus`](https://github.com/leanprover/hex-berlekamp-zassenhaus);
its Mathlib counterpart is
[`hex-number-field-tower-mathlib`](https://github.com/leanprover/hex-number-field-tower-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-number-field-tower"
git = "https://github.com/leanprover/hex-number-field-tower.git"
rev = "main"
```

```lean
import HexNumberFieldTower

open Hex NumberTower

def a : Elem rat := rat.ofRat (3/2)

#guard a * rat.ofRat 3 = rat.ofRat (9/2)
#guard a⁻¹ * a = rat.ofRat 1
```

# Functionality

`Hex.NumberTower` is a sealed validated tower; `Hex.NumberTower.Elem T`
carries exact mixed-radix rational coordinates with decidable equality and
full field arithmetic, totalized by `0⁻¹ = 0`. Only smart constructors can
admit a level:

- `Hex.NumberTower.rat`: the rational base tower.
- `Hex.NumberTower.ofQAdjoin`: a one-level tower for an irreducible
  presentation `ℚ(x)`.
- `Hex.NumberTower.adjoin?`: adjoin a selected absolute algebraic root.
- `Hex.NumberTower.factor?`: complete irreducible Trager factorization of a
  `Poly T` with multiplicity.
- `Hex.NumberTower.split?`: an extension in which a given polynomial splits
  into linear factors.
- `Hex.NumberTower.flatten?`: replace the tower by one canonical
  primitive-element field, with coordinate maps in both directions.

The `Option` results carry new dependent carrier indices and certificates,
so there is no junk fallback value; the Mathlib companion proves every
valid input succeeds.

# Verification

Every level stores a successful executable factorization check and a
consistent chosen complex embedding by construction; the sealed
representation means no other route can build a tower. This package does
not itself turn those Boolean checks into semantic irreducibility or claim
a law-bearing field instance. The companion
[`hex-number-field-tower-mathlib`](https://github.com/leanprover/hex-number-field-tower-mathlib)
interprets every validated tower as a finite extension of `ℚ` with a fixed
complex embedding, proves the coordinate arithmetic computes the complex
operations, and verifies Trager factorization, adjoining, splitting fields,
and flattening. See the [SPEC](SPEC/hex-number-field-tower.md) for the
representation and contracts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
