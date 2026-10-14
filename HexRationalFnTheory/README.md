# HexRationalFnTheory

The proved correspondence between `Hex.RationalFn K` and Mathlib's `RatFunc K`.
Import `HexRationalFnTheory` for `equiv`, `algEquiv`, compatible `Field` and
`Algebra` instances, canonical component agreement, and operation correspondence.

`normalize_spec` identifies the represented fraction and both canonical
polynomials. `check_sound` obtains the same contract from a checked certificate,
without reducing normalization in the kernel. The partial evaluation theorems
explicitly distinguish failure at a canonical pole from Mathlib's total evaluator
returning zero there.

`coeffMap` is executable coefficient transport, and `mapHom` packages the same
function as a field-embedding ring homomorphism. It maps each canonical pair
directly, without gcd. `toRatFunc_mapHom` proves agreement with Mathlib's
rational-function map; `mapHom_C` and `mapHom_X` identify constants and the
indeterminate. `mapHom_id` and `mapHom_comp` support successive base changes.

Coefficients use the `Lean.Grind.Field` induced by the same Mathlib `Field`.
For concrete coefficient types with another lightweight instance, make that choice
explicit using `attribute [local instance 2000] Field.toGrindField`.
Executable arithmetic remains the computational implementation; the inverse
of the mathematical equivalence is noncomputable.

See the [SPEC](SPEC/hex-rational-fn-theory.md) and
[kernel replay examples](Tests.lean). The build audits the headline theorem,
algebra equivalence, and nontrivial certificate replay for axiom dependencies.
