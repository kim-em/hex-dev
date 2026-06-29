# hex-bareiss-mathlib (depends on hex-bareiss + hex-determinant-mathlib + Mathlib)

Mathlib bridge for `hex-bareiss`: proves the row-pivoted Bareiss determinant
correct against both Mathlib's determinant and our executable Leibniz
determinant, via the no-pivot bordered-minor invariant and the determinant
correspondence from `hex-determinant-mathlib`.

**No-pivot invariant and core correctness:**
```lean
structure NonzeroBareissPivots (M : Hex.Matrix Int n n) : Prop
def BareissNoPivotInvariant ...
theorem bareissNoPivot_eq_det ...          -- under NonzeroBareissPivots
theorem bareiss_eq_mathlib_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)
```

**Headline correspondence theorems** (the preferred surface for downstream
Mathlib-side callers):
```lean
theorem bareissDet_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)

theorem bareiss_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Hex.Matrix.det M
```

`bareiss_eq_det` is proven Mathlib-side by composing `bareiss_eq_mathlib_det`
with `det_eq` (from `hex-determinant-mathlib`), so it holds outright. These are
the theorems on the forbidden list in the Mathlib-free `hex-bareiss` SPEC: they
must live here, never restated or reproven in the executable layer.
