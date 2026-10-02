# hex-reflect

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-reflect` turns a batch of commutative-ring expressions into `Hex.MvPoly`
values over one sealed variable environment and proves that the conversion
preserves interpretation. It is the only Hex library that imports
`Lean.Meta.Sym.Arith`, and it defines the provider outcomes, conditions,
result records, budgets, and decline reasons shared by symbolic Hex
frontends. It depends on
[`hex-mv-poly`](https://github.com/leanprover/hex-mv-poly) and
[`hex-basic`](https://github.com/leanprover/hex-basic). See
[`hex-reflect-mathlib`](https://github.com/leanprover/hex-reflect-mathlib)
for the `MvPolynomial` form of the conversion theorem.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-reflect"
git = "https://github.com/leanprover/hex-reflect.git"
rev = "main"
```

```lean
import HexReflect

open Lean Meta Hex Hex.Reflect

-- reflect a batch of expressions over one sealed atom environment
run_meta withLocalDeclD `x (mkConst ``Int) fun x => do
  withLocalDeclD `y (mkConst ``Int) fun y => do
    let s ← mkAppM ``HAdd.hAdd #[x, y]
    let p ← mkAppM ``HMul.hMul #[s, s]
    let .success batch _ ← reflectRingBatch #[s, p] .grevlex
      | throwError "declined"
    -- two atoms; (x + y) * (x + y) expands to three terms
    logInfo m!"{batch.sealed.n} atoms"
    for entry in batch.entries do
      -- every entry carries a proof of `eval₂ Int.cast atoms poly = source`
      logInfo m!"{entry.conversion.terms.length} terms: {← inferType entry.result.proof}"
```

# Functionality

- `reflectRingBatch` reifies every input with `Lean.Meta.Sym.Arith.reifyRing?`
  inside one `SymM.run`, seals the atom environment once at size `n`,
  converts every reflected expression to a term list over `Hex.Mono n`
  through `Expr.toPoly` (or `Expr.toPolyC` when Lean supplies characteristic
  evidence), and reconstructs an interpretation proof for each entry.
- `reifyCommRing`, `reifyCommSemiring`, `sealAtoms`, `convert`, and
  `Conversion.mkProof` expose the same steps to a session over any monad that
  lifts `SymM`, with `MonadMkVar` and `MonadGetVar` supplied for the batch.
- `convertTerms?`, `convert?`, and `ofIntTerms` are the pure conversion
  functions; the polynomial is built with `Hex.MvPoly.ofTerms` under an
  explicitly requested comparator.
- `Budget`, `BudgetState`, `Decline`, `Failure`, `ProviderOutcome`,
  `Condition`, `ConditionalResult`, `EqualityResult`, and `PropertyResult`
  are the shared frontend vocabulary; `Registration` with the
  `hex_reflect_provider` attribute registers coefficient providers.

# Verification

The Mathlib-free soundness theorem states that conversion commutes with
interpretation, for any lawful coefficient interpretation:

```lean
theorem eval₂_convertTerms [Lean.Grind.CommRing α] (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) (x : Fin n → α) (hx : ∀ i : Fin n, x i = ctx.get i.val)
    {e : RingExpr} {ts : List (Mono n × Int)} (h : convertTerms? n none e = some ts) :
    MvPoly.eval₂ interp x (ofIntTerms (cmp := cmp) ofInt ts) = e.denote ctx
```

`eval₂_convertTermsC` is the characteristic-aware arm. The Meta proof returned
to a caller applies these theorems to the quoted reflected syntax, sealed
context, and term list; the equality between the pure conversion and the
quoted term list is a kernel reduction of concrete reflected data, and the
result is related to the caller's source by definitional equality. No kernel
decision of symbolic evaluation is involved.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want and leave
the implementation to the maintainer.
