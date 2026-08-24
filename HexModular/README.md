# hex-modular

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-modular` provides symmetric integer residues, incremental scalar and
vector CRT, rational reconstruction, and fuel-bounded multimodular loops. It
depends on [`hex-arith`](https://github.com/leanprover/hex-arith). The
Mathlib correspondence belongs in
[`hex-modular-mathlib`](https://github.com/leanprover/hex-modular-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-modular"
git = "https://github.com/leanprover/hex-modular.git"
rev = "main"
```

```lean
import HexModular

open Hex.Modular

def combined : Option (Nat × Int) := do
  let first ← Crt.init.push 1 3
  let second ← first.push 0 2
  pure (second.modulus, second.value)

#eval combined
#eval symMod 17 10
#eval ratRecon? 68 101 8 8
```

# Functionality

- Symmetric integer reduction with `symMod`.
- Incremental scalar CRT with `Crt.init` and `Crt.push`.
- Common-modulus vector CRT with `CrtVec.init` and `CrtVec.push`.
- Bounded, wide, vector, and maximal-quotient rational reconstruction with
  `ratRecon?`, `ratReconWide?`, `ratReconVec?`, and `ratReconMaxQuot?`.
- Fuel-bounded modular image accumulation with `crtLoop` and `CrtTrace`.

# Verification

Successful CRT pushes preserve old congruences, record every new residue,
and maintain a canonical half-modulus representative. Bounded rational
reconstruction proves congruence, bounds, denominator coprimality,
uniqueness, and completeness under the standard strict bound. The
maximal-quotient heuristic promises congruence only.

```lean
theorem ratRecon?_complete {a P Q : Int} {m : Nat} {y : Rat}
    (hm : 2 * P * Q < (m : Int))
    (hy : (Int.ofNat y.den * a - y.num) % (m : Int) = 0)
    (hb : (y.num.natAbs : Int) ≤ P ∧ (y.den : Int) ≤ Q) :
    ratRecon? a m P Q = some y
```

The executable library is Mathlib-free. Correspondence with `ZMod`,
Mathlib's Chinese remainder API, and `ℚ` belongs in
[`hex-modular-mathlib`](https://github.com/leanprover/hex-modular-mathlib).

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
