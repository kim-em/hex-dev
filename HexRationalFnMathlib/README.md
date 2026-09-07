# HexRationalFnMathlib

The proved correspondence between `Hex.RationalFn K` and Mathlib's `RatFunc K`.
Import `HexRationalFnMathlib` for `equiv`, `algEquiv`, compatible `Field` and
`Algebra` instances, canonical component agreement, and operation correspondence.

`normalize_spec` identifies the represented fraction and both canonical
polynomials. `check_sound` obtains the same contract from a checked certificate,
without reducing normalization in the kernel. The partial evaluation theorems
explicitly distinguish failure at a canonical pole from Mathlib's total evaluator
returning zero there.

Coefficients use the `Lean.Grind.Field` induced by the same Mathlib `Field`.
For concrete coefficient types with another lightweight instance, make that choice
explicit using `attribute [local instance 2000] Field.toGrindField`.
Executable arithmetic remains the computational implementation; the inverse
of the mathematical equivalence is noncomputable.

See the [SPEC](SPEC/hex-rational-fn-mathlib.md) and
[kernel replay examples](Tests.lean). The build audits the headline theorem,
algebra equivalence, and nontrivial certificate replay for axiom dependencies.
