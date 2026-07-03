# hex-number-field-mathlib (depends on hex-number-field + hex-resultant-mathlib + hex-berlekamp-zassenhaus-mathlib + hex-roots-mathlib + hex-poly-z-mathlib)

Mathlib companion for `hex-number-field`. Proves that the
algebraic-number arithmetic computes what it claims, against Mathlib's
`AdjoinRoot`, `minpoly`, and field-extension API.

Throughout, write `pℚ := (toPolynomial p).map (algebraMap ℤ ℚ)` for
the ℚ-coefficient form of `p : ZPoly`. The passage between `p`
(primitive, positive leading coefficient, irreducible over ℤ) and the
monic `minpoly ℚ α` goes through `pℚ` and Gauss's lemma. Getting this
boundary right is most of the definitional work.

## What we cite from Mathlib (no work)

All names checked against the Mathlib revision this repository pins.
Module names are given without line numbers, which rot.

- `AdjoinRoot`, `AdjoinRoot.lift`, and the `Field (AdjoinRoot f)`
  instance under `[Fact (Irreducible f)]`
  (`Mathlib.RingTheory.AdjoinRoot`).
- Gauss's lemma in the form
  `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`
  (`Mathlib.RingTheory.Polynomial.GaussLemma`): `p` irreducible over ℤ
  iff `pℚ` irreducible over ℚ, for primitive `p`.
- `Field.exists_primitive_element` for finite separable extensions
  (`Mathlib.FieldTheory.PrimitiveElement`); applies to `ℚ ⊆ ℚ(α, β)`
  since ℚ has characteristic zero.
- `IntermediateField` with the `F⟮α⟯` notation and its lattice API
  (`Mathlib.FieldTheory.IntermediateField.Basic`,
  `….Adjoin.Defs`).
- `IsAlgebraic` (`Mathlib.RingTheory.Algebraic.Defs`).
- `IntermediateField.algebraicClosure F E`
  (`Mathlib.FieldTheory.AlgebraicClosure`): the relative algebraic
  closure; `IntermediateField.algebraicClosure ℚ ℂ` is the subfield of
  algebraic complex numbers, with the membership lemma
  `x ∈ … ↔ IsAlgebraic ℚ x`.
- `minpoly` and its API (`Mathlib.FieldTheory.Minpoly.Basic`); monic
  by Mathlib convention, in `ℚ[X]` for our case.
- `minpoly.equivAdjoin : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R {x}`
  for `x` integral
  (`Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed`): the equivalence
  between the abstract quotient and the concrete subfield.
- `Polynomial.IsPrimitive`, `Polynomial.content`,
  `Polynomial.primPart` (`Mathlib.RingTheory.Polynomial.Content`).
- From the other companions: the `DensePoly Int ≃+* Polynomial ℤ`
  ring equivalence (`hex-poly-z-mathlib`),
  `resultant_eq_zero_iff_common_root` (`hex-resultant-mathlib`),
  `RefinedIsolation.root` / `rootOf` and the `sameRoot` semantics
  (`hex-roots-mathlib`), and
  `Hex.ZPoly.IsIrreducible f ↔ Irreducible (toPolynomial f)`
  (`hex-berlekamp-zassenhaus-mathlib`).

## Correspondence theorems

### `QAdjoin p x` semantics

```lean
/-- `QAdjoin p x` is the quotient `ℚ[X]/(pℚ)`. A ring equivalence for
    any `p` of positive degree; when `p` is irreducible it is an
    equivalence of fields (both sides then carry field structures). -/
def QAdjoin.equivAdjoinRoot {p : ZPoly} (x : SimpleRoot p) :
    QAdjoin p x ≃+* AdjoinRoot pℚ

/-- Evaluation at the root: the embedding of `QAdjoin p x` into ℂ. -/
def QAdjoin.toComplex {p : ZPoly} (x : SimpleRoot p) :
    QAdjoin p x →+* ℂ
  -- AdjoinRoot.lift at `rootOf x`, composed with equivAdjoinRoot

theorem QAdjoin.toComplex_eq_eval {p : ZPoly} (x : SimpleRoot p)
    (a : QAdjoin p x) :
    QAdjoin.toComplex x a = (toPolynomial a.coeffs).aeval (rootOf x)
```

Note `AdjoinRoot (toPolynomial p)` (over ℤ) would be the wrong target:
that is `ℤ[X]/(p)`, an order, not the field `ℚ(α)`. The map to ℚ
coefficients is what makes `equivAdjoinRoot` and the field structure
correct, and Gauss's lemma is what transfers `p`'s irreducibility over
ℤ to `pℚ`'s over ℚ.

### `QAdjoin.approx` correctness

```lean
theorem QAdjoin.approx_sound (a : QAdjoin p x) (rep h prec) :
    QAdjoin.toComplex x a ∈ (a.approx rep h prec).2.set ∧
    SimpleRoot.mk (a.approx rep h prec).1 = x

theorem QAdjoin.approx_radius (a : QAdjoin p x) (rep h prec) :
    (a.approx rep h prec).2.radius ≤ 2^(−prec)
```

`approx` is total with a sound fallback, so `approx_sound` is
unconditional: the ball always contains the true value, and the
returned isolation always identifies the same root. Only the
precision claim `approx_radius` depends on refinement succeeding,
which is part of the bound-sufficiency work below.

### `AlgebraicNumber` semantics

```lean
def AlgebraicNumber.toComplex (a : AlgebraicNumber) : ℂ :=
  rootOf a.x

theorem AlgebraicNumber.toComplex_isRoot (a : AlgebraicNumber) :
    (toPolynomial a.p).aeval a.toComplex = 0

/-- The stored polynomial is the minimal polynomial: its ℚ-coefficient
    form is the monic minimal polynomial scaled by the leading
    coefficient. -/
theorem AlgebraicNumber.p_eq_minpoly (a : AlgebraicNumber) :
    (a.p.leadingCoeff : ℚ)⁻¹ • (toPolynomial a.p).map (algebraMap ℤ ℚ)
      = minpoly ℚ a.toComplex

/-- Canonicity: `toComplex` is injective (per `BEq`, below), and its
    range is exactly the algebraic numbers. -/
theorem AlgebraicNumber.range_toComplex :
    Set.range AlgebraicNumber.toComplex = {z : ℂ | IsAlgebraic ℚ z}

/-- `==` decides equality of values. -/
theorem AlgebraicNumber.beq_iff (a b : AlgebraicNumber) :
    a == b ↔ a.toComplex = b.toComplex
```

(`toComplex` is not injective as a function on the raw structure,
since two values may differ only in `rep`. `beq_iff` is the right
statement, and injectivity holds on the `BEq`-quotient.)

### `commonField` correctness

```lean
theorem AlgebraicNumber.commonField?_sound (α β : AlgebraicNumber)
    {cf} (h : α.commonField? β = some cf) :
    QAdjoin.toComplex cf.γ cf.αIn = α.toComplex ∧
    QAdjoin.toComplex cf.γ cf.βIn = β.toComplex

theorem AlgebraicNumber.commonField?_isSome (α β : AlgebraicNumber) :
    (α.commonField? β).isSome
```

The proof certifies the algorithm's own checks rather than citing
abstract existence: `resultant_eq_zero_iff_common_root`
(hex-resultant-mathlib) shows `α + c·β` is a root of the resultant;
the numerical disambiguation (hex-roots-mathlib `sameRoot` semantics
plus ball arithmetic bounds) shows the chosen factor is the one
vanishing at `α + c·β`; the multiplicity-1 check plus the classical
primitive-element argument shows `γ` generates, so the linear system
of step 5 is solvable and its solution unique.
`Field.exists_primitive_element` is used only as a guide. The
correctness proof is about the computed `γ`, not an abstract one.

### Arithmetic correctness

The proofs are staged to match the `?`-form / total-form split in
hex-number-field.md:

```lean
-- Stage 1 (soundness): a computed certificate is correct.
theorem AlgebraicNumber.add?_sound (α β : AlgebraicNumber)
    {γ} (h : α.add? β = some γ) :
    γ.toComplex = α.toComplex + β.toComplex

-- Stage 2 (bound sufficiency): the certificate always appears.
theorem AlgebraicNumber.add?_isSome (α β : AlgebraicNumber) :
    (α.add? β).isSome

-- Headline: unconditional, by composing the two; the `panicWith`
-- branch of the total wrapper is dead by stage 2.
theorem AlgebraicNumber.add_toComplex (α β : AlgebraicNumber) :
    (α.add β).toComplex = α.toComplex + β.toComplex

-- likewise for mul, sub, inv (with hypothesis ¬ α.isZero), the
-- always-total neg, and isZero_iff
```

Stage 1 follows from `commonField?_sound`, the `QAdjoin` ring laws,
and `toAlgebraicNumber?_sound` below; it is provable without any
completeness input, because the algorithm checks its own
certificates. Stage 2 is where the analysis lives (item 6 below).

### Conversion correctness

```lean
theorem AlgebraicNumber.toQAdjoin_toComplex (a : AlgebraicNumber) :
    QAdjoin.toComplex a.x a.toQAdjoin = a.toComplex

theorem QAdjoin.toAlgebraicNumber?_sound [Hex.ZPoly.IsIrreducible p]
    (a : QAdjoin p x) (rep h) {b}
    (hsome : a.toAlgebraicNumber? rep h = some b) :
    b.toComplex = QAdjoin.toComplex x a
```

`toAlgebraicNumber?_sound` is the substantive theorem: the
minimal-polynomial computation (that the first linear dependence among
the powers of the multiplication operator gives `minpoly ℚ` of the
value, using that `ℚ[t]/(pℚ)` is a field) and the root identification
(that the isolation selected by the ball test is the root equal to the
value) both need real proofs.

## New theorems this library must build

1. **Monic-ℚ to primitive-positive-ℤ** (~50 lines):
   ```lean
   theorem exists_unique_primitive_int_minpoly (α : ℂ) (hα : IsAlgebraic ℚ α) :
       ∃! p : ℤ[X], p.IsPrimitive ∧ 0 < p.leadingCoeff ∧
         (p.leadingCoeff : ℚ)⁻¹ • p.map (algebraMap ℤ ℚ) = minpoly ℚ α
   ```
   Denominator clearing plus the primitive part, over the monic
   ℚ-minimal polynomial.
2. **Canonicity of `AlgebraicNumber`** (~100 lines): wrap item 1 into
   the structure and prove `range_toComplex` and `beq_iff` (the
   latter also uses the `sameRoot` semantics from hex-roots-mathlib).
3. **`QAdjoin.equivAdjoinRoot`** (~100 lines): compose the
   `hex-poly-z-mathlib` ring equivalence with the quotient
   presentation of `AdjoinRoot pℚ`; transfer the field structure
   through Gauss's lemma and `[Fact (Irreducible pℚ)]`.
4. **`toAlgebraicNumber?_sound`**: the minimal-polynomial-of-the-
   multiplication-operator argument and the root identification.
5. **`commonField?_sound`**: certification of the resultant, factor
   choice, non-degeneracy, and change of basis, as described above.
6. **Bound sufficiency** (the `_isSome` theorems, retiring every
   `panicWith` branch): the `disambiguationPrec` estimate (a
   classical lower bound on `|g(γ)|` for the wrong factors `g`, via
   heights and resultants), the `maxShift` collision count, and the
   root-refinement pieces imported from hex-roots-mathlib's
   completeness development.

Items 1-3 are bounded and small. Items 4 and 5 are the substantive
soundness obligations, comparable in size to items 1-3 combined
several times over, and there is no shortcut through abstract
existence theorems. Item 6 can be deferred along with
hex-roots-mathlib's completeness development: the stage-1 soundness
theorems stand on their own, and the unconditional headline theorems
land when item 6 does.

## File organisation

```
HexNumberFieldMathlib/
  Basic.lean            : pℚ notation, toComplex definitions
  AdjoinRoot.lean       : equivAdjoinRoot and the field transfer (item 3)
  Minpoly.lean          : items 1 and 2
  Approx.lean           : approx_sound, approx_radius
  Convert.lean          : toQAdjoin_toComplex, toAlgebraicNumber?_sound (item 4)
  CommonField.lean      : commonField?_sound (item 5)
  AlgOps.lean           : arithmetic correctness, staged (?_sound,
                          ?_isSome, unconditional headlines)
```

The library is verified by building it. Conformance fixtures live
with `hex-number-field`.

## References

- Cohen, *A Course in Computational Algebraic Number Theory* (1993):
  the algorithms whose correctness is being proved.
- Lang, *Algebra* (Springer, 3rd ed.): the field-extension facts
  (primitive element, `K[X]/(p)` is a field for irreducible `p`).
