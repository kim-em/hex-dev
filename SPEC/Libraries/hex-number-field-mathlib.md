# hex-number-field-mathlib (depends on hex-number-field + hex-resultant-mathlib + hex-berlekamp-zassenhaus-mathlib + hex-roots-mathlib + hex-poly-z-mathlib)

Mathlib bridge for `hex-number-field`. Proves correctness of the
algebraic-number arithmetic against Mathlib's standard
`Polynomial.AdjoinRoot`, `IsAlgebraic`, and field-extension
infrastructure.

## What we cite from Mathlib (no work)

- `Polynomial.AdjoinRoot`, the natural map `Polynomial R → AdjoinRoot p`,
  and the field structure on `AdjoinRoot p` when `p` is irreducible.
- `IntermediateField`, `IsAlgebraic`, `Algebra ℚ ℂ`,
  `MinpolyOver` and the `minpoly` definition.
- `Field.exists_primitive_element` for finite separable extensions
  (which covers `ℚ ⊂ ℚ(α, β)` for distinct algebraic α, β).
- `Polynomial.eval`, `Polynomial.aeval`, `Polynomial.IsRoot`.

## Bridging theorems

### `NumberField p x` semantics

```lean
/-- When `p` is irreducible, `NumberField p x` is the field `AdjoinRoot p`,
    with embedding into ℂ given by evaluation at the simple root
    identified by `x`. -/
theorem NumberField.equiv_adjoinRoot {p : ZPoly} (hp : Hex.ZPoly.Irreducible p)
    (x : SimpleRoot p) :
    NumberField p x ≃+* AdjoinRoot (toPolynomial p)

/-- The complex-valued embedding of `NumberField p x`. -/
def NumberField.toComplex {p : ZPoly} (x : SimpleRoot p) :
    NumberField p x →+* ℂ
  -- defined as: `aeval (root corresponding to x)` post-composed with
  -- AdjoinRoot's universal property

theorem NumberField.toComplex_eq_eval {p : ZPoly} (x : SimpleRoot p)
    (a : NumberField p x) :
    NumberField.toComplex x a = (toPolynomial a.coeffs).eval (rootOf x)
  -- where `rootOf x : ℂ` is the complex root identified by `x`
  -- (defined via the SimpleRoot semantics in hex-roots-mathlib)
```

### `NumberField.approx` correctness

```lean
theorem NumberField.approx_contains (a : NumberField p x) (prec : Nat) :
    NumberField.toComplex x a ∈ (a.approx prec).2.ball
  -- the returned ball contains the true complex value
```

The first component of `approx` (the refreshed `NumberField p x`) is
propositionally equal to the input via `SimpleRoot.refine_eq`; this
is reflected as a separate theorem:

```lean
theorem NumberField.approx_first_eq (a : NumberField p x) (prec : Nat) :
    (a.approx prec).1 = a    -- propositionally
```

### `AlgebraicNumber` semantics

```lean
/-- The complex-number value of an `AlgebraicNumber`, given by the
    SimpleRoot. -/
def AlgebraicNumber.toComplex (a : AlgebraicNumber) : ℂ :=
  rootOf a.x

/-- An `AlgebraicNumber`'s value is a root of its declared minimal
    polynomial. -/
theorem AlgebraicNumber.toComplex_isRoot (a : AlgebraicNumber) :
    (toPolynomial a.p).IsRoot a.toComplex

/-- The polynomial declared by `AlgebraicNumber.p` is in fact the
    minimal polynomial. -/
theorem AlgebraicNumber.p_eq_minpoly (a : AlgebraicNumber) :
    toPolynomial a.p = (minpoly ℚ a.toComplex).primitivePart -- (up to leading-coefficient sign)

/-- AlgebraicNumber values are in bijection with `ℂ_alg`
    (algebraic complex numbers). -/
theorem AlgebraicNumber.bijective_to_ℂ_alg :
    Function.Bijective AlgebraicNumber.toComplex.toFun ∧
    ∀ z : ℂ, IsAlgebraic ℚ z ↔ ∃ a : AlgebraicNumber, a.toComplex = z
```

### `commonField` correctness

```lean
theorem AlgebraicNumber.commonField_correct (α β : AlgebraicNumber) :
    let ⟨r, γ, hr, αIn, βIn⟩ := α.commonField β
    Hex.ZPoly.Irreducible r ∧
    NumberField.toComplex γ αIn = α.toComplex ∧
    NumberField.toComplex γ βIn = β.toComplex
```

Uses the primitive-element theorem
(`Field.exists_primitive_element`) plus our resultant-zero-iff-common-root
result from `hex-resultant-mathlib` to certify that the chosen factor
`r` of the resultant is indeed the minimal polynomial of α + c·β over
ℚ. Numerical disambiguation correctness uses `HexRoots`'s
`SimpleRoot` semantics.

### Arithmetic correctness

```lean
theorem AlgebraicNumber.add_toComplex (α β : AlgebraicNumber) :
    (α.add β).toComplex = α.toComplex + β.toComplex

theorem AlgebraicNumber.mul_toComplex (α β : AlgebraicNumber) :
    (α.mul β).toComplex = α.toComplex * β.toComplex

theorem AlgebraicNumber.inv_toComplex (α : AlgebraicNumber) (h : ¬ α.isZero) :
    (α.inv h).toComplex = α.toComplex⁻¹

-- and similarly for sub, neg, isZero
```

Each follows from `commonField_correct` plus the corresponding
`NumberField p x` ring axiom plus `toAlgebraicNumber`'s correctness
(below).

### `toNumberField` and `toAlgebraicNumber` correctness

```lean
theorem AlgebraicNumber.toNumberField_toComplex (a : AlgebraicNumber) :
    NumberField.toComplex a.x a.toNumberField = a.toComplex

theorem NumberField.toAlgebraicNumber_toComplex (a : NumberField p x) :
    a.toAlgebraicNumber.toComplex = NumberField.toComplex x a
```

The latter is the substantive theorem — it says that the minimal
polynomial computation via `NumberField.toAlgebraicNumber` correctly
identifies the value's minimal polynomial and matches the right
SimpleRoot.

## Mathlib gap analysis

To verify when drafting; first-cut estimate from the bridging
theorems above:

**Cite directly (no work expected):**
- `Polynomial.AdjoinRoot` and the field instance under irreducibility
  hypothesis.
- `IsAlgebraic`, `Algebra ℚ ℂ`, `IsAlgClosed ℂ`.
- `Field.exists_primitive_element` (finite separable; ℚ has char 0,
  every field extension is separable, and `[ℚ(α, β) : ℚ] < ∞`).
- `Polynomial.minpoly`.

**Possibly build (verify status at Phase 6 start):**

- A clean equivalence `Polynomial R / minpoly α →+* AdjoinRoot
  (minpoly α)` for the `α ∈ ℂ_alg` case. Mathlib likely has the
  pieces; assembly may be needed.
- A canonical "primitive part with positive leading coefficient" form
  for minimal polynomials over `ℤ`. This is straightforward but the
  exact lemma may not be packaged.

## Layered file organisation

```
HexNumberFieldMathlib/
  Basic.lean            — bridge definitions, `toComplex` constructors
  AdjoinRoot.lean       — NumberField ≃+* AdjoinRoot, field structure bridge
  Approx.lean           — `approx` correctness
  Convert.lean          — toNumberField/toAlgebraicNumber correctness
  CommonField.lean      — primitive-element theorem application
  AlgOps.lean           — arithmetic correctness theorems
  Algebraic.lean        — bijection with ℂ_alg
  Conformance.lean      — fixture-based checks
```

## References

- Cohen, *A Course in Computational Algebraic Number Theory* (1993),
  for the algorithmic side; the same algorithms our `hex-number-field`
  implements.
- Lang, *Algebra* (Springer, 3rd ed.), for the abstract field-extension
  results being bridged (primitive element theorem,
  irreducibility-implies-field for `K[X]/(p)`).
