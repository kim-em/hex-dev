# hex-berlekamp

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified polynomial factorization and irreducibility testing over the prime
field `F_p`, without Mathlib. The package supplies Rabin's irreducibility
test, distinct-degree factorization, the Berlekamp Frobenius matrix with its
fixed-space kernel, split-step factorization, and the `factor_poly` and
`irreducibility` elaborators that turn a compiled search into a kernel-checked
proof term. It builds on
[`hex-poly-fp`](https://github.com/leanprover/hex-poly-fp) for the dense
`F_p[x]` arithmetic, [`hex-matrix`](https://github.com/leanprover/hex-matrix)
and [`hex-row-reduce`](https://github.com/leanprover/hex-row-reduce) for the
kernel computation, and
[`hex-gfq-ring`](https://github.com/leanprover/hex-gfq-ring) for the quotient
ring. Statements over Mathlib's `Polynomial (ZMod p)` live in
[`hex-berlekamp-mathlib`](https://github.com/leanprover/hex-berlekamp-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-berlekamp"
git = "https://github.com/leanprover/hex-berlekamp.git"
rev = "main"
```

```lean
import HexBerlekamp
open Hex Hex.Berlekamp

local instance : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
local instance : ZMod64.PrimeModulus 5 := ⟨by decide⟩

-- `3 * (x + 1)^2 * (x^2 + 2)` over `F_5`, expanded.
def f : FpPoly 5 := #p[1, 2, 4, 1, 3]

-- A kernel-checked irreducible factorization, found by compiled search.
example : True := by
  obtain ⟨scalar, factors, factors_mul, factors_irred⟩ := factor_poly f
  trivial

-- Rabin's test; the elaborator emits a certificate the kernel replays.
theorem irred : FpPoly.Irreducible (#p[2, 0, 1] : FpPoly 5) :=
  irreducibility (#p[2, 0, 1] : FpPoly 5)

def g : FpPoly 5 := #p[1, 0, 0, 1]
#eval (berlekampFactor g (by rfl)).factors.length  -- 2
```

# Functionality

- `Berlekamp.rabinTest f hmonic` is Rabin's irreducibility test: `f` must be
  nonconstant, divide `X^(p^n) - X`, and be coprime to `X^(p^d) - X` for every
  maximal proper divisor `d` of `n = deg f`.
- `Berlekamp.berlekampMatrix` builds the Frobenius matrix `Q_f` column by
  column from `powModMonic`, and `Berlekamp.fixedSpaceKernel` returns a basis
  of the kernel of `Q_f - I`. `Berlekamp.Packed` reimplements the whole
  reduction over `UInt32` words and connects to the generic development by a
  `@[csimp]` bridge, so compiled code runs the packed loop while proofs stay
  on ordinary matrices.
- `Berlekamp.berlekampFactor f hmonic` returns the complete factorization of a
  monic input as a `Berlekamp.Factorization`. It takes a root-extraction
  shortcut when `f` splits completely, and otherwise splits recursively on
  kernel representatives.
- `Berlekamp.distinctDegreeFactor f hmonic` separates a monic square-free
  input into one product per irreducible-factor degree, without building any
  matrix. `Berlekamp.scoutDegreePattern` answers the cheaper question "how
  many irreducible factors are there, and of which degrees" and abandons the
  loop as soon as a caller-supplied factor budget is exceeded.
- `factor_poly f` elaborates to a `Hex.FpPoly.Factored f`, destructured as
  `obtain ⟨scalar, factors, factors_mul, factors_irred⟩ := factor_poly f`, and
  also exists as a tactic. `irreducibility f` elaborates to
  `Hex.FpPoly.Irreducible f`. Both run the search in compiled elaborator code
  and emit a certificate that the kernel replays; neither uses
  `native_decide`.
- `Berlekamp.IrreducibilityCertificate` is the self-describing certificate
  data those elaborators emit, checked by
  `Berlekamp.checkIrreducibilityCertificate`.

The public umbrella contains production APIs only; the tactic regression
modules are built by the package's dedicated test target.

# Verification

Everything is proved in Lean without Mathlib, and the trust surface contains
no `axiom`, no `sorry`, and no `native_decide`. Factorization is total and
product-correct for any monic input:

```lean
theorem prod_berlekampFactor
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [ZMod64.PrimeModulus p] :
    (berlekampFactor f hmonic).product = f
```

Distinct-degree factorization has the matching product law
`prod_distinctDegreeFactor`, together with `distinctDegreeFactor_bucket_degree_pos`
and `distinctDegreeFactor_bucket_matchesFrobeniusDegree`, which say that each
recorded bucket carries a positive degree and divides the corresponding
Frobenius difference. Rabin's test is sound against the project-side
irreducibility predicate,

```lean
theorem rabinTest_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hrabin : rabinTest f hmonic = true) :
    FpPoly.Irreducible f
```

with `rabinTest_eq_true_iff` restating the Boolean test in theorem-facing
terms, and `checkIrreducibilityCertificate_rabinTest` tying the certificate
checker back to it. That chain is what makes an emitted certificate mean
irreducibility rather than merely "the checker returned `true`".

Irreducibility of the returned factors is stated over Mathlib's `Irreducible`
predicate in
[`hex-berlekamp-mathlib`](https://github.com/leanprover/hex-berlekamp-mathlib),
whose `rabin_irreducible` proves both directions of Rabin's criterion for a
monic input and whose `fpIsIrreducible_iff` extends it to arbitrary input.

Exact conformance against python-flint is a required release check. FLINT
timings are informational optimization evidence. The required performance
checks are the absolute Rabin and distinct-degree budgets stated in the
[SPEC](SPEC/hex-berlekamp.md).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
