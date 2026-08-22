# hex-gf2

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Packed polynomials over `F_2`, and the finite fields `GF(2^n)` they present,
implemented without Mathlib. Coefficients are the bits of a `UInt64` array, so
addition is a word-wise XOR and multiplication runs on carry-less word products
rather than on per-coefficient modular arithmetic. The only dependency is
[`hex-basic`](https://github.com/leanprover/hex-basic). The ring equivalence
with Mathlib's `Polynomial (ZMod 2)`, along with finiteness and cardinality,
lives in [`hex-gf2-mathlib`](https://github.com/leanprover/hex-gf2-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-gf2"
git = "https://github.com/leanprover/hex-gf2.git"
rev = "main"
```

```lean
import HexGF2
open Hex

-- `GF(2^8)` on AES's modulus `x^8 + x^4 + x^3 + x + 1`, packed into one word.
abbrev AES : Type :=
  GF2n 8 0x1B (by decide) (by decide) GF2Poly.aes_modulus_irreducible

def a : AES := GF2n.reduce 0x53
def b : AES := GF2n.reduce 0xCA
def c : AES := a * b⁻¹

#eval (a + b).val                             -- 153: addition is XOR
#eval (GF2Poly.ofUInt64Monic 0x1B 8).degree   -- 8

example (h : a ≠ 0) : a * a⁻¹ = 1 := GF2n.mul_inv_cancel a h
```

# Functionality

- `GF2Poly` is a normalized `Array UInt64` of coefficient bits. Degree is
  derived by `GF2Poly.degree?` and `GF2Poly.degree` rather than cached, so
  equality of elements is equality of word arrays (`GF2Poly.ext_words`).
- Arithmetic: XOR addition, `GF2Poly.mul` as a schoolbook convolution of
  carry-less word products, and `GF2Poly.shiftLeft` and `GF2Poly.shiftRight`
  for multiplication and division by `x^k`.
- Euclidean operations: `GF2Poly.divMod`, `div`, `mod`, `gcd` and `xgcd`, with
  the `Div`, `Mod` and `Dvd` instances they back.
- `Hex.clmul` is the 64-by-64 carry-less multiply. It is `@[extern]`, and the C
  wrapper picks `_mm_clmulepi64_si128` on x86-64, `vmull_p64` on aarch64, or a
  portable shift-and-XOR, by compile-time feature detection. `Hex.pureClmul` is
  the Lean reference semantics that the proofs use.
- `GF2n n irr hn hn64 hirr` holds `GF(2^n)` for `n < 64` in one word;
  `GF2nPoly f hirr` covers any degree over `GF2Poly`. Both supply reduction,
  inversion, division, and a square-and-multiply `pow`.
- `GF2Poly.rabinTest` decides irreducibility, and
  `checkIrreducibilityCertificate` replays a supplied certificate instead;
  `checkIrreducibilityCertificateLinear` is the kernel-reducible variant.
- The moduli cryptography uses are committed with their certificates and
  irreducibility proofs: `gf16Modulus`, `aesModulus`, `gf65kModulus`, and
  `ghashModulus`.

# Verification

Irreducibility is proved rather than tabulated. The Rabin test is sound, and so
is certificate replay, which is what lets a committed modulus be checked by the
kernel without `native_decide`:

```lean
theorem rabinTest_imp_irreducible (f : GF2Poly) (hrabin : rabinTest f = true) :
    GF2Poly.Irreducible f

theorem checkIrreducibilityCertificate_imp_irreducible
    (f : GF2Poly) (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificate f cert = true) :
    GF2Poly.Irreducible f
```

The packed quotient carries `Lean.Grind.Semiring`, `Lean.Grind.Ring` and
`Lean.Grind.CommRing` instances for every modulus the type admits. The field
laws need more: `GF2Poly.Irreducible` is satisfied by the constant `1`, and the
quotient by a constant is trivial, so nonconstancy is a separate hypothesis and
the field laws are functions rather than instances.

```lean
def fieldOfDegreePos (hdeg : 0 < f.degree) : Lean.Grind.Field (GF2nPoly f hirr)

theorem isCharPOfDegreePos (hdeg : 0 < f.degree) :
    Lean.Grind.IsCharP (GF2nPoly f hirr) 2
```

For the single-word representation, `GF2n.mul_inv_cancel` gives inverse
cancellation directly. Division, gcd and extended gcd have proved
specifications: `GF2Poly.div_mul_add_mod`, `mod_degree_lt`, `gcd_dvd_left`,
`dvd_gcd`, and `xgcd_bezout`.

Correctness of the compiled `clmul` is trusted, as the GMP externs in
`hex-arith` are. `clmul_eq_pureClmul` is the equation the proofs rely on, and
the compiled wrapper is cross-checked against `Hex.pureClmul` by a conformance
driver and by a C self-test that compiles both wrapper paths. See the
[SPEC](SPEC/hex-gf2.md) for the representation invariant, the extern contract,
and the committed-modulus table.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
