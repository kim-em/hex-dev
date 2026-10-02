# hex-reflect-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-reflect-mathlib` is the Mathlib companion to
[`hex-reflect`](https://github.com/leanprover/hex-reflect). It records the
coefficient interpretation of a reflected batch as a Mathlib ring
homomorphism, translates Mathlib characteristic evidence into the Grind form
used by characteristic-aware normalization, and states the `MvPolynomial`
form of the conversion theorem through `HexMvPolyMathlib.equiv`. It depends
on Mathlib, `hex-reflect`, and
[`hex-mv-poly-mathlib`](https://github.com/leanprover/hex-mv-poly-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-reflect-mathlib"
git = "https://github.com/leanprover/hex-reflect-mathlib.git"
rev = "main"
```

```lean
import HexReflectMathlib

open Hex Hex.Reflect HexReflectMathlib

example {R : Type} [CommRing R] {n : Nat} (ctx : Lean.RArray R)
    {e : RingExpr} {ts : List (Mono n × Int)}
    (h : convertTerms? n none e = some ts) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ctxValuation ctx n)
        (HexMvPolyMathlib.equiv (ofIntTerms (cmp := Mono.grevlex) id ts)) =
      e.denote ctx :=
  eval₂_equiv_ofIntTerms ctx h
```

# Functionality

- `coeffLaws_ofRingHom` and `coeffLaws_intCastRingHom` supply the
  `CoeffLaws` record of `hex-reflect` from a Mathlib ring homomorphism.
- `isCharP_of_charP` turns Mathlib `CharP R p` evidence into
  `Lean.Grind.IsCharP R p`.
- `eval₂_equiv_ofIntTerms`, `eval₂_equiv_ofIntTermsC`, and
  `aeval_algEquiv_ofIntTerms` state the conversion theorem for
  `MvPolynomial (Fin n) R`.

# Verification

Every theorem is proved by composing the Mathlib-free soundness theorem of
`hex-reflect` with the existing `HexMvPolyMathlib` evaluation
correspondence. This library defines no second conversion between the
polynomial types, no parser, and no algorithm.

```lean
theorem eval₂_equiv_ofIntTerms (ctx : Lean.RArray R) {e : RingExpr}
    {ts : List (Mono n × Int)} (h : convertTerms? n none e = some ts) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ctxValuation ctx n)
        (HexMvPolyMathlib.equiv (ofIntTerms (cmp := cmp) id ts)) =
      e.denote ctx
```

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want and leave
the implementation to the maintainer.
