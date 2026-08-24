# hex-gfq-field

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Executable finite fields `F_p[x] / (f)` for Lean 4, without Mathlib. The
modulus is any polynomial you can prove irreducible, so the package is not tied
to a particular choice of modulus. It adds inversion, division, exponentiation
and Frobenius to the canonical quotient-ring representation from
[`hex-gfq-ring`](https://github.com/leanprover/hex-gfq-ring), which it reuses
unchanged; the committed example field additionally cites
[`hex-berlekamp`](https://github.com/leanprover/hex-berlekamp)'s certificate
checker. Finiteness, cardinality, and the correspondence with Mathlib's
abstract finite fields live in
[`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib); for a
canonical modulus chosen for you, see
[`hex-gfq`](https://github.com/leanprover/hex-gfq).

# Quickstart

```toml
[[require]]
name = "hex-gfq-field"
git = "https://github.com/leanprover/hex-gfq-field.git"
rev = "main"
```

```lean
import HexGFqField
open Hex Hex.GFqField

-- `GF(5^4) = F_5[x] / (x^4 + 2)`, from the committed example modulus.
abbrev F : Type := Example.F

def α : F := Example.ofPoly #p[0, 1]
def β : F := α ^ 4 + α + 1
def γ : F := β / α

example (h : β ≠ 0) : β * β⁻¹ = 1 := mul_inv_cancel h
example : frob α = α ^ 5 := frob_eq_pow α

-- Any modulus works: supply positive degree, primality, and irreducibility.
#check @FiniteField
```

# Functionality

- `FiniteField f hf hp hirr` is the field, indexed by the modulus `f`, its
  positive degree `hf`, the primality witness `hp` for the characteristic, and
  the irreducibility proof `hirr`. It wraps `GFqRing.PolyQuotient f hf`, so
  there is one representation and one equality story across the ring and field
  layers. `ofQuotient`, `toQuotient`, `ofPoly` and `repr` move between the
  three views, and equality is decidable by comparing representatives.
- Ring operations delegate to the quotient: `add`, `mul`, `neg`, `sub`,
  `natCast`, `intCast`, `nsmul` and `zsmul`, each with its instance and a
  `repr_*` and `toQuotient_*` lemma.
- `pow` is square-and-multiply, so a Frobenius-sized exponent costs `O(log n)`
  field multiplications rather than `n` of them. `zpow` extends it to `Int`.
- `inv` is extended GCD in `F_p[x]` through `invPoly`, normalized by the
  constant unit factor of the gcd, with the usual junk value at zero. `div` is
  multiplication by `inv`.
- `frob x` is `x ^ p`.
- `GFqField.Example` commits one small field, `GF(5^4)` presented as
  `F_5[x] / (x^4 + 2)`, with its Rabin certificate and
  `Example.modulus_irreducible`, so that examples and conformance drivers do
  not each rebuild a certificate.

# Verification

The field laws are proved, not asserted. Inverse cancellation is the result the
rest rests on:

```lean recall Hex.GFqField.mul_inv_cancel
theorem mul_inv_cancel
    {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] {hp : Hex.Nat.Prime p}
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ 0) :
    x * x⁻¹ = 1
```

with `inv_mul_cancel` on the other side, `div_eq_mul_inv` connecting division,
and `zero_ne_one` giving nontriviality. Those assemble into the bundled
instances, which hold for every modulus the type admits, because the type
already carries both the irreducibility proof and the positive-degree
hypothesis:

```lean
import HexGFqField

open Hex Hex.GFqField

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Field (FiniteField f hf hp hirr)

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.IsCharP (FiniteField f hf hp hirr) p
```

`frob_eq_pow` holds by `rfl`, so a statement about Frobenius and a statement
about the `p`-th power are the same statement. Both hypotheses are load-bearing:
irreducibility alone would admit a nonzero constant modulus, whose quotient is
trivial, and the field laws would be false there.

`Fintype` and cardinality are deliberately absent, and belong to
[`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib). See the
[SPEC](SPEC/hex-gfq-field.md) for the layering rule against
[`hex-gfq-ring`](https://github.com/leanprover/hex-gfq-ring) and the comparator
scope.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
