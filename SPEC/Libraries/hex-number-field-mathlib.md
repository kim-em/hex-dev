# hex-number-field-mathlib (depends on hex-number-field + hex-resultant-mathlib + hex-berlekamp-zassenhaus-mathlib + hex-roots-mathlib + hex-poly-z-mathlib)

Mathlib companion for `hex-number-field`. It interprets the executable types in
`ℂ` and proves fixed-field correspondence, canonicalization, factorization-lazy
arithmetic, semantic equality, and completeness of the polynomial root APIs.

Write `pℚ` for `(toPolynomial p).map (algebraMap ℤ ℚ)`.

## Imported foundations

- `AdjoinRoot`, its lift API, and its field instance under irreducibility.
- Gauss's lemma between primitive irreducibility over `ℤ` and `ℚ`.
- `minpoly`, `IntermediateField`, algebraic closure, and primitive elements.
- Polynomial roots with multiplicity and finite-dimensional norm.
- Dense polynomial correspondence from `hex-poly-z-mathlib`.
- Full resultant correspondence and specialization from
  `hex-resultant-mathlib`.
- Root interpretation, refinement completeness, and `sameRoot` semantics from
  `hex-roots-mathlib`.
- Integer factorization soundness from
  `hex-berlekamp-zassenhaus-mathlib`.

## Semantic maps

```lean
def QAdjoin.equivAdjoinRoot {p : ZPoly} (x : SimpleRoot p) :
    QAdjoin p x ≃+* AdjoinRoot pℚ

def QAdjoin.toComplex {p : ZPoly} (x : SimpleRoot p) :
    QAdjoin p x →+* ℂ

def AlgebraicRoot.toComplex (a : AlgebraicRoot) : ℂ := rootOf a.x
def AlgebraicNumber.toComplex (a : AlgebraicNumber) : ℂ := rootOf a.x

theorem AlgebraicRoot.toComplex_isRoot (a : AlgebraicRoot) :
    (toPolynomial a.p).aeval a.toComplex = 0

theorem AlgebraicNumber.p_eq_minpoly (a : AlgebraicNumber) :
    (a.p.leadingCoeff : ℚ)⁻¹ •
      (toPolynomial a.p).map (algebraMap ℤ ℚ) =
        minpoly ℚ a.toComplex
```

`QAdjoin.toComplex` evaluates reduced coordinates at the selected root. Under
`[ZPoly.IsIrreducible p]` it is an embedding of fields.

## Equality, zero, and approximation

```lean
theorem AlgebraicNumber.beq_iff (a b : AlgebraicNumber) :
    a == b ↔ a.toComplex = b.toComplex

theorem AlgebraicRoot.beq_iff (a b : AlgebraicRoot) :
    a == b ↔ a.toComplex = b.toComplex

theorem AlgebraicRoot.isZero_iff (a : AlgebraicRoot) :
    a.isZero ↔ a.toComplex = 0

theorem QAdjoin.approx_sound (...) :
    QAdjoin.toComplex x a ∈ (a.approx rep h prec).2.set

theorem QAdjoin.approx_radius (...) :
    (a.approx rep h prec).2.radius ≤ 2 ^ (-prec)
```

The `AlgebraicRoot.beq_iff` proof uses `sameRoot` on the fast path and
exactification on the general path. No structural `DecidableEq` is exposed for
either algebraic-number record.

## Canonicalization

```lean
theorem AlgebraicNumber.toRoot_toComplex (a : AlgebraicNumber) :
    a.toRoot.toComplex = a.toComplex

theorem AlgebraicRoot.exact?_sound (a : AlgebraicRoot) {b}
    (h : a.exact? = some b) :
    b.toComplex = a.toComplex

theorem AlgebraicRoot.exact?_isSome (a : AlgebraicRoot) :
    a.exact?.isSome

theorem AlgebraicRoot.exact_toComplex (a : AlgebraicRoot) :
    a.exact.toComplex = a.toComplex

theorem QAdjoin.toAlgebraicNumber?_sound
    [ZPoly.IsIrreducible p] (...) {b} (h : ... = some b) :
    b.toComplex = QAdjoin.toComplex x a
```

Exactification completeness follows because the squarefree enclosing polynomial
factors into distinct irreducibles and exactly one factor contains the selected
root. Factor soundness supplies the product identity; resultant common-root facts
and disjoint refined isolations supply uniqueness.

## Lazy arithmetic

For every checked operation, prove certificate soundness first, bound sufficiency
second, and the total headline last:

```lean
theorem AlgebraicRoot.add?_sound (a b : AlgebraicRoot) {c}
    (h : a.add? b = some c) :
    c.toComplex = a.toComplex + b.toComplex

theorem AlgebraicRoot.add?_isSome (a b : AlgebraicRoot) :
    (a.add? b).isSome

theorem AlgebraicRoot.add_toComplex (a b : AlgebraicRoot) :
    (a.add b).toComplex = a.toComplex + b.toComplex
```

Provide the same theorem family for subtraction, multiplication, inversion, and
division, plus unconditional negation. Inversion follows Mathlib's convention
`0⁻¹ = 0`, so its headline needs no nonzero hypothesis.

Operation soundness uses the Stage 1 specialization-vanishing theorem from
`hex-resultant-mathlib`. `_isSome` uses squarefree normalization, root-isolation
completeness, and the Stage 2 root-product lower bound behind
`rootDisambiguationPrec`. Canonical `AlgebraicNumber` arithmetic follows by
`toRoot`, the lazy headline, and `exact_toComplex`.

## Algebraic coefficient polynomials

Interpret `AlgebraicPoly` as a Mathlib `Polynomial ℂ` using
`AlgebraicNumber.toComplex` coefficientwise.

```lean
def AlgebraicPoly.toPolynomial (f : AlgebraicPoly) : Polynomial ℂ

theorem AlgebraicPoly.isZero_iff (f : AlgebraicPoly) :
    f.isZero ↔ f.toPolynomial = 0
```

This theorem justifies semantic trailing-zero trimming and is the reason the
computational library does not use `DensePoly AlgebraicNumber`.

## Root API correctness

```lean
theorem QAdjoin.roots?_isSome [ZPoly.IsIrreducible p] (...) :
    (QAdjoin.roots? f rep h).isSome

theorem AlgebraicPoly.roots?_isSome (f : AlgebraicPoly) :
    f.roots?.isSome

theorem AlgebraicPoly.roots_all_iff (f : AlgebraicPoly) :
    f.roots = .all ↔ f.toPolynomial = 0

theorem AlgebraicPoly.mem_roots_iff (f : AlgebraicPoly) (a : AlgebraicRoot) :
    a ∈ f.roots ↔ Polynomial.eval a.toComplex f.toPolynomial = 0

theorem AlgebraicPoly.multiplicity_eq (f : AlgebraicPoly)
    (a : AlgebraicRoot) :
    multiplicityOf a f.roots =
      Polynomial.rootMultiplicity a.toComplex f.toPolynomial
```

State corresponding fixed-field theorems through `QAdjoin.toComplex`. For finite
outputs also prove no duplicates, positive multiplicities, deterministic order,
and that the sum of multiplicities is the polynomial degree.

The proof follows the executable stages:

1. Yun decomposition gives the multiplicity index for each squarefree component.
2. Full resultant agreement identifies the norm eliminant and proves candidate
   completeness.
3. The selected field embedding makes evaluation of the original polynomial the
   acceptance criterion; the disambiguation lower bound refutes candidates from
   other embeddings.
4. The internal common-field construction preserves every canonical coefficient,
   reducing `AlgebraicPoly.roots` to the fixed-field theorem.

## Required new developments

1. Canonical primitive-positive integer representatives of rational minimal
   polynomials and canonicity of `AlgebraicNumber`.
2. `QAdjoin.equivAdjoinRoot`, field-law transfer, and approximation semantics.
3. Minimal polynomial of the multiplication operator for
   `toAlgebraicNumber?`.
4. Exactification factor selection and completeness.
5. Lazy eliminant soundness and the candidate-refutation bound.
6. Many-coefficient primitive-field construction for `AlgebraicPoly`.
7. Yun multiplicity transfer, norm candidate completeness, and embedding
   filtering for both root APIs.

Items 1 through 4 do not depend on tower support. Items 5 and 7 require the
staged resultant theorems specified by `hex-resultant-mathlib`.

## File organisation

```text
HexNumberFieldMathlib/
  Basic.lean          : semantic maps and canonical forms
  AdjoinRoot.lean     : fixed-field correspondence
  Approx.lean         : ball semantics
  Exact.lean          : canonicalization and exactification
  Lazy.lean           : arithmetic soundness and completeness
  AlgebraicPoly.lean  : semantic coefficient polynomials
  Roots.lean          : root completeness and multiplicity
```

The library is verified by building it. Executable conformance belongs to
`hex-number-field`.

## References

- Cohen, H. *A Course in Computational Algebraic Number Theory.* Springer,
  1993.
- Lang, S. *Algebra.* Springer, 3rd ed., for finite separable extensions,
  primitive elements, and quotient-field semantics.
