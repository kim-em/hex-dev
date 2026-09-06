# hex-number-field-mathlib (depends on hex-number-field + hex-resultant-mathlib + hex-berlekamp-zassenhaus-mathlib + hex-roots-mathlib + hex-poly-z-mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owners: `HexNumberField`, `HexRoots`, `HexResultant`, `HexBerlekampZassenhaus`, `HexPolyZ`, `HexPoly`, `HexRowReduce`, `HexMatrix`
Computational performance owners: `HexNumberField`, `HexRoots`, `HexResultant`, `HexBerlekampZassenhaus`, `HexPolyZ`, `HexPoly`, `HexRowReduce`, `HexMatrix`

The complete public surface is correspondence-only. The library declares no
`meta`, `partial`, `unsafe`, `IO`, syntax, macro, elaborator, tactic, reifier,
or certificate-checker entry point. Its semantic maps, polynomial views, ring
maps, equivalences, and field dictionaries are noncomputable. The
field dictionaries pin every data field definitionally to the existing
executable operations. `RootSet.totalMultiplicity` is the only
bridge-originated ordinary definition with a data result: it is the linear
structural fold used to state the root-result multiplicity theorem, not an
advertised algebraic operation. The `LawfulBEq` and `DecidableEq` instances
package the executable `AlgebraicNumber.beq` from `HexNumberField`. These
result observers and law dictionaries introduce no independent algebraic
algorithm, checker, reifier, proof generator, or kernel-cost surface.

The transported operations and their computational owners are:

| Transported surface | Computational owner | Owner evidence |
| --- | --- | --- |
| `QAdjoin` reduction, arithmetic, scalar actions, powers, inversion, approximation, and checked/total canonical conversion | `HexNumberField` | `conformance/HexNumberField/Conformance.lean`, `hexnumberfield_bench`, and `reports/hex-number-field-performance.md` |
| Lazy and canonical algebraic-number equality, zero recognition, arithmetic, exactification, and field operations | `HexNumberField` | The same conformance target covers checked and total lazy operations, semantic equality, rational construction, casts, scalar actions, and powers; the same benchmark target registers the corresponding compiled surfaces. |
| Yun decomposition, candidate disambiguation and merging, fixed-field roots, algebraic-coefficient roots, and common-field presentation (`rational?`, arithmetic and shifts, primitive search, powers, traces, coordinates, and `presentation?`) | `HexNumberField` | The root and algebraic-polynomial sections of the owner conformance target exercise the public pipelines, including common presentation transitively; the owner benchmark registers their components and end-to-end paths. |
| Selected-root isolation and `RefinedIsolation.refineTo?`; dyadic-ball construction and arithmetic; radius, extent, membership, and square-intersection semantics | `HexRoots` | `conformance/HexRoots/Conformance.lean`, `hexroots_bench`, and `reports/hex-roots-performance.md` |
| Executable bivariate resultants used by lazy eliminants and fixed-field norm/evaluation eliminants | `HexResultant` | `conformance/HexResultant/Conformance.lean`, `hexresultant_bench`, and `reports/hex-resultant-performance.md` |
| Checked irreducibility and integer-polynomial factorization used by canonicalization and exactification | `HexBerlekampZassenhaus` | `conformance/HexBerlekampZassenhaus/Conformance.lean`, `hexbz_bench`, and `reports/hex-berlekamp-zassenhaus-performance.md` |
| Integer-polynomial representation, normalization, and conversion transported into Mathlib polynomials throughout the bridge | `HexPolyZ` | `conformance/HexPolyZ/Conformance.lean`, `hexpolyz_bench`, and `reports/hex-poly-z-performance.md` |
| Dense-polynomial Euclidean operations, composition, scaling, and coefficient transforms used by Yun, resultants, and presentation proofs | `HexPoly` | `conformance/HexPoly/Conformance.lean`, `hexpoly_bench`, and `reports/hex-poly-performance.md` |
| `Matrix.spanCoeffs` used by common-field coordinate recovery | `HexRowReduce` | `conformance/HexRowReduce/Conformance.lean`, `hexrowreduce_bench`, and `reports/hex-row-reduce-performance.md` |
| Matrix/vector construction, row access, multiplication, and conversion used by exactification and coordinate recovery | `HexMatrix` | `conformance/HexMatrix/Conformance.lean`, `hexmatrix_bench`, and `reports/hex-matrix-performance.md` |

There is deliberately no `conformance/HexNumberFieldMathlib` or
`bench/HexNumberFieldMathlib` source tree, no dedicated Lake conformance or
benchmark target, no `proof_probes` registry root, and no
`reports/hex-number-field-mathlib-performance.md`. Building the library checks
its correspondence theorems and axiom-regression guards; those guards are not
timed proof probes.

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
- Root interpretation, refinement preservation, and `sameRoot` semantics from
  `hex-roots-mathlib`, including mixed-strategy completeness for the raw local
  refinement budget. This companion lifts that result through the refined
  wrapper and uses it to prove the requested approximation radius.
- Integer factorization soundness from
  `hex-berlekamp-zassenhaus-mathlib`.

## Semantic maps

```lean
noncomputable def QAdjoin.toComplex (a : QAdjoin p x)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) : ℂ

def AlgebraicRoot.toComplex (a : AlgebraicRoot) : ℂ := rootOf a.x
def AlgebraicNumber.toComplex (a : AlgebraicNumber) : ℂ := rootOf a.x

theorem AlgebraicRoot.toComplex_isRoot (a : AlgebraicRoot) :
    (toPolynomial a.p).aeval a.toComplex = 0

theorem AlgebraicNumber.p_eq_minpoly (a : AlgebraicNumber) :
    (a.p.leadingCoeff : ℚ)⁻¹ •
      (toPolynomial a.p).map (algebraMap ℤ ℚ) =
        minpoly ℚ a.toComplex

theorem AlgebraicNumber.toComplex_injective :
    Function.Injective AlgebraicNumber.toComplex

instance : LawfulBEq AlgebraicNumber
instance : DecidableEq AlgebraicNumber
```

`QAdjoin.toComplex` evaluates reduced coordinates at an explicit refined
representative of the selected root. Addition, multiplication, and scalar laws
therefore do not depend on irreducibility or on the quotient-level `rootOf`
construction. Under `[ZPoly.CheckedIrreducible p]`, semantic irreducibility
makes this map injective and validates inversion. `QAdjoin.toAdjoinRoot` is an
actual map to the quotient by the monic rational associate and is proved
bijective before law-bearing structures are installed. After the operation laws
are proved, package that bijection as a ring equivalence and `toComplex` as a
ring embedding without changing any computational operation.

When constructing the `Field (QAdjoin p x)` instance, set its rational scalar
action explicitly to the computational `SMul Rat` instance shipped by
HexNumberField. This keeps Mathlib's generated `qsmul` path definitionally
identical and avoids a second, diamond-forming rational action.

## Equality, zero, and approximation

```lean
theorem AlgebraicNumber.beq_iff (a b : AlgebraicNumber) :
    a == b ↔ a.toComplex = b.toComplex

theorem AlgebraicPoly.beq_iff (f g : AlgebraicPoly) :
    f == g ↔ f.toPolynomial = g.toPolynomial

theorem AlgebraicRoot.isZero_iff (a : AlgebraicRoot) :
    a.isZero ↔ a.toComplex = 0

theorem AlgebraicNumber.isZero_iff (a : AlgebraicNumber) :
    a.isZero ↔ a.toComplex = 0

theorem RefinedIsolation.refineTo?_isSome (rep) (target) :
    (rep.refineTo? target .nkThenPellet).isSome

theorem QAdjoin.approx_sound (...) :
    QAdjoin.toComplex a rep h ∈ (a.approx rep h prec).2.set

theorem QAdjoin.approx_radius (...) :
    (a.approx rep h prec).2.realRadius ≤ 2 ^ (-prec)
```

The totality theorem is deliberately for the default mixed strategy: its NK
prefix is complete around the represented locally simple root even when the
ambient polynomial has repeated roots elsewhere. No pure-Pellet totality
claim is needed for `QAdjoin.approx`.

`AlgebraicRoot` deliberately exposes no Boolean or structural equality:
comparison first exactifies to canonical `AlgebraicNumber`. No structural
`DecidableEq` is exposed for either algebraic-number record.

## Canonicalization

First derive `ZPoly.Irreducible p` from every stored
`ZPoly.CheckedIrreducible p` using the factorization companion's Boolean
equivalence. Together with the stored squarefreeness proof, this justifies both
the canonical minimal-polynomial theorem and `AlgebraicNumber.toRoot` without a
cross-layer proof gap.

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
    [ZPoly.CheckedIrreducible p] (...) {b} (h : ... = some b) :
    b.toComplex = QAdjoin.toComplex a rep hrep

theorem QAdjoin.toAlgebraicNumber?_isSome
    [ZPoly.CheckedIrreducible p] (...) :
    (a.toAlgebraicNumber? rep hrep).isSome

theorem QAdjoin.toAlgebraicNumber_toComplex
    [ZPoly.CheckedIrreducible p] (...) :
    (a.toAlgebraicNumber rep hrep).toComplex =
      QAdjoin.toComplex a rep hrep
```

Exactification completeness follows because the squarefree enclosing polynomial
factors into distinct irreducibles and exactly one factor contains the selected
root. Factor soundness supplies the product identity; resultant common-root facts
and disjoint refined isolations supply uniqueness.

Fixed-presentation completeness instead uses the first Krylov dependence of the
represented element. Finite dimensionality supplies a dependence at the Mathlib
minimal-polynomial degree, first-success minimality proves that the executable
relation has exactly that degree, and Gauss normalization supplies its primitive,
positive-leading, irreducible, and simple-root certificates. Isolation completeness
finds its represented complex root; the guarded approximation ball and the
candidate disc share that root, so the executable intersection test succeeds and
canonical normalization is total.

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
`hex-resultant-mathlib`. `_isSome` uses squarefree normalization,
root-isolation completeness, and HexRoots separation at
`resultIsolationPrec`; it does not require the Stage 2 resultant value theorem.
Addition's fixed four-bit refinement bound follows directly from ball addition.
Multiplication uses root-size bounds for both operands, while inversion uses the
reciprocal Cauchy lower bound for a nonzero root and a doubled coefficient-height
guard for reciprocal distortion. The resulting ball is two bits smaller than
`resultIsolationPrec` for addition and four bits smaller for multiplication and
inversion; each bound is sufficient for singleton selection. The checked
multiplication and inversion zero branches are handled before eliminant
construction and agree with `0⁻¹ = 0`.
Canonical `AlgebraicNumber` arithmetic follows by `toRoot`, the lazy headline,
and `exact_toComplex`.

The total rational constructor satisfies

```lean
theorem AlgebraicNumber.ofRat_toComplex (q : Rat) :
    (AlgebraicNumber.ofRat q).toComplex = (q : ℂ)
```

Together with `toComplex_injective` and the arithmetic correspondence
theorems, this transports the field laws from `ℂ` onto the existing executable
zero, one, casts, scalar actions, powers, and arithmetic operations. The
installed `Field AlgebraicNumber` therefore changes no computational data
field; it only supplies the law-bearing dictionary. The instance is
computable: its data fields are the executable operations written out and
its laws are taken one by one from the transported proof, so code that
reaches an operation through the field structure, such as `a ^ n` under
Mathlib's monoid power, compiles and runs the executable operation.

## Exact primitives

```lean
theorem AlgebraicNumber.I_toComplex : AlgebraicNumber.I.toComplex = Complex.I
theorem AlgebraicNumber.conj_toComplex (a : AlgebraicNumber) :
    a.conj.toComplex = starRingEnd ℂ a.toComplex
theorem AlgebraicNumber.realCompare_eq (a b : AlgebraicNumber)
    (ha : a.isReal = true) (hb : b.isReal = true) :
    a.realCompare b = compare a.toComplex.re b.toComplex.re
```

Each rests on `mahlerPrec_separates` and `approx_mem`: at `separationPrec`
the balls of distinct roots of one polynomial are disjoint, so the root whose
ball meets a given point's ball is unique, and the order of ball centres is
the order of real roots.

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
theorem QAdjoin.roots?_isSome [ZPoly.CheckedIrreducible p] (...) :
    (QAdjoin.roots? f rep h).isSome

theorem AlgebraicPoly.roots?_isSome (f : AlgebraicPoly) :
    f.roots?.isSome

theorem AlgebraicPoly.roots_all_iff (f : AlgebraicPoly) :
    f.roots = .all ↔ f.toPolynomial = 0

theorem AlgebraicPoly.contains_roots_iff (f : AlgebraicPoly) (z : ℂ) :
    RootSet.Contains f.roots z ↔ Polynomial.eval z f.toPolynomial = 0

theorem AlgebraicPoly.multiplicity_roots (f : AlgebraicPoly) (z : ℂ) :
    f.roots.multiplicityOf z =
      Polynomial.rootMultiplicity z f.toPolynomial
```

The semantic `RootSet.Contains` interface is deliberate: lazy roots have no
structural or Boolean equality, while callers may ask about any complex root.
The internal `QAdjoin.Roots.sameValue?` operation has separate soundness and
completeness contracts because root merging depends on it even though no public
`BEq AlgebraicRoot` instance exists.

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

## Developments

1. Canonical primitive-positive integer representatives of rational minimal
   polynomials and canonicity of `AlgebraicNumber`.
2. `QAdjoin.toAdjoinRoot_bijective`, field-law transfer, and approximation
   semantics.
3. Minimal polynomial of the multiplication operator for
   `toAlgebraicNumber?`.
4. Exactification factor selection and completeness.
5. Lazy eliminant soundness, same-eliminant separation, and the independent
   evaluation-refutation bound used by root filtering.
6. Many-coefficient primitive-field construction for `AlgebraicPoly`.
7. Yun multiplicity transfer, norm candidate completeness, and embedding
   filtering for both root APIs.

Items 1 through 4 do not depend on tower support. Items 5 and 7 rest on the
resultant correspondence of `hex-resultant-mathlib`
(`resultant_eq_zero_iff_common_root` and
`resultant_eq_leadingCoeff_mul_prod_roots`).

## File organisation

```text
HexNumberFieldMathlib/
  Basic.lean                 : semantic maps and canonical forms
  AdjoinRoot.lean            : fixed-field correspondence
  Approx.lean                : ball semantics
  Exact.lean                 : canonicalization and exactification
  Lazy.lean                  : arithmetic soundness and completeness
  Field.lean                 : the Field instances pinned to executable data
  Nearest.lean               : imaginary unit, conjugation, exact real order
  AlgebraicPoly.lean         : semantic coefficient polynomials
  Roots.lean                 : root completeness and multiplicity
  AlgebraicRoots.lean        : finite-output root-set obligations
  ComponentRoots.lean        : per-component root soundness
  RootDisambiguation.lean    : candidate rejection soundness
  Yun.lean                   : Yun multiplicity correspondence
  Primitive.lean             : bounded primitive-element search soundness
  Presentation.lean          : checked common-field arithmetic totality
  PresentationSemantics.lean : assembly of total primitive presentations
  Coordinates.lean           : trace-pairing coordinate recovery
```

The last four verify the `Hex.AlgebraicPoly.Common` surface (see the
hex-number-field SPEC §Common-field construction), which the tower
libraries consume.

The library is verified by building it. Executable conformance belongs to
`hex-number-field`.

## External comparators

No external comparator is required.

**Justification:** `correspondence-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The library introduces no
number-field arithmetic algorithm; it verifies operations implemented by the
computational performance owners enumerated in the correspondence-only table
above. Their own Phase-4 targets and reports carry the measurements and
comparator decisions. In particular, `hex-number-field` measures the
high-level arithmetic and root ladders and its PARI/GP comparator.

## References

- Cohen, H. *A Course in Computational Algebraic Number Theory.* Springer,
  1993.
- Lang, S. *Algebra.* Springer, 3rd ed., for finite separable extensions,
  primitive elements, and quotient-field semantics.
