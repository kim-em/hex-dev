# hex-mv-gcd

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-mv-gcd` provides checked exact division, content, greatest common
divisors, and square-free decomposition for sparse multivariate polynomials.
It supports integer, rational, and bounded prime-field coefficients. Its
computational core is Mathlib-free.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-mv-gcd"
git = "https://github.com/leanprover/hex-mv-gcd.git"
rev = "main"
```

```lean
import HexMvGcd

open Hex Hex.MvPoly

abbrev P := MvPoly 2 Int Mono.lex

def x : P := X 0
def y : P := X 1

#eval gcd ((x + 1) * (y + 1)) ((x + 1) * (y + 2))
#eval divExact? ((x + 1) * (y + 1)) (x + 1)
#eval sqfDecomp ((x + 1) ^ 2 * (y + 1))
```

# Functionality

- Sparse multivariate division with `MvPoly.divMod` and `MvPoly.divExact?`.
- Canonical content and primitive parts over gcd domains.
- Replayable `MvPoly.GcdCert` certificates and the small `checkGcd` checker.
- Deterministic PRS fallback plus heuristic and Brown modular producers.
- Named-variable content through `contentIn` and `primPartIn`.
- Square-free decomposition, radical, and square-freeness tests.

# Verification

Candidate producers never establish correctness by themselves. Every public
gcd is extracted from a certificate accepted by `checkGcd`; replay proves the
two exact cofactor identities and the greatest-common-divisor property.

```lean
theorem gcd_dvd_left (f g : P) : gcd f g ∣ f

theorem dvd_gcd (d f g : P) (hf : d ∣ f) (hg : d ∣ g) :
    d ∣ gcd f g
```

The executable library does not import Mathlib. Correspondence with
Mathlib's `MvPolynomial` belongs in the sibling Mathlib bridge package.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
