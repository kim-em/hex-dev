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
| `PolyQuot` reduction, arithmetic, scalar actions, powers, inversion, approximation, and checked/total canonical conversion | `HexNumberField` | `conformance/HexNumberField/Conformance.lean`, `hexnumberfield_bench`, and `reports/hex-number-field-performance.md` |
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
noncomputable def PolyQuot.toComplex (a : PolyQuot p x)
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

`PolyQuot.toComplex` evaluates reduced coordinates at an explicit refined
representative of the selected root. Addition, multiplication, and scalar laws
therefore do not depend on irreducibility or on the quotient-level `rootOf`
construction. Under `[ZPoly.CheckedIrreducible p]`, semantic irreducibility
makes this map injective and validates inversion. `PolyQuot.toAdjoinRoot` is an
actual map to the quotient by the monic rational associate and is proved
bijective before law-bearing structures are installed. After the operation laws
are proved, package that bijection as a ring equivalence and `toComplex` as a
ring embedding without changing any computational operation.

When constructing the `Field (PolyQuot p x)` instance, set its rational scalar
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

theorem PolyQuot.approx_sound (...) :
    PolyQuot.toComplex a rep h ∈ (a.approx rep h prec).2.set

theorem PolyQuot.approx_radius (...) :
    (a.approx rep h prec).2.realRadius ≤ 2 ^ (-prec)
```

The totality theorem is deliberately for the default mixed strategy: its NK
prefix is complete around the represented locally simple root even when the
ambient polynomial has repeated roots elsewhere. No pure-Pellet totality
claim is needed for `PolyQuot.approx`.

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

theorem PolyQuot.toAlgebraicNumber?_sound
    [ZPoly.CheckedIrreducible p] (...) {b} (h : ... = some b) :
    b.toComplex = PolyQuot.toComplex a rep hrep

theorem PolyQuot.toAlgebraicNumber?_isSome
    [ZPoly.CheckedIrreducible p] (...) :
    (a.toAlgebraicNumber? rep hrep).isSome

theorem PolyQuot.toAlgebraicNumber_toComplex
    [ZPoly.CheckedIrreducible p] (...) :
    (a.toAlgebraicNumber rep hrep).toComplex =
      PolyQuot.toComplex a rep hrep

theorem QAdjoin.toAlgebraicNumber_toComplex {a : AlgebraicNumber} (c : QAdjoin a) :
    c.toAlgebraicNumber.toComplex = PolyQuot.toComplex c a.rep a.rep_mk
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

`conj_toComplex` follows from orientation and certificate transport. `I` is
selected by its exact upper tag. `realCompare_eq` uses `mahlerPrec_separates`
and `approx_mem` for the product polynomial: its separated ball centres have
the order of the two real values. The public mirror-ball geometry helpers
remain available for compatibility independently of the tag implementation.

## The nearest root

```lean
theorem AlgebraicNumber.ofPoint_toComplex (re im : Rat) :
    (AlgebraicNumber.ofPoint re im).toComplex = (re : ℂ) + (im : ℂ) * Complex.I
theorem AlgebraicNumber.distSqTo_toComplex (a : AlgebraicNumber) (re im : Rat) :
    (a.distSqTo re im).toComplex = ‖a.toComplex - ((re : ℂ) + (im : ℂ) * Complex.I)‖ ^ 2
theorem ZPoly.rootNear_mem (p : ZPoly) (hp : 0 < p.natDegree) (re im : Rat) :
    p.rootNear re im ∈ p.algebraicRoots
theorem ZPoly.rootNear_nearest (p : ZPoly) (re im : Rat) (b : AlgebraicNumber)
    (hb : b ∈ p.algebraicRoots) :
    ‖(p.rootNear re im).toComplex - ((re : ℂ) + (im : ℂ) * Complex.I)‖ ≤
      ‖b.toComplex - ((re : ℂ) + (im : ℂ) * Complex.I)‖
theorem ZPoly.rootNear_of_close (a : AlgebraicNumber) (re im : Rat)
    (h : ‖((re : ℂ) + (im : ℂ) * Complex.I) - a.toComplex‖ <
      2 * ((2 : ℝ) ^ (-(mahlerPrec a.p : ℤ)) * (1449 / 1024))) :
    a.p.rootNear re im = a
```

The fast path is sound because every point of a ball is within the radius
of the centre and `‖w‖ ≤ |w.re| + |w.im|`, so the bounds bracket the true
distances; the exact path is sound because `distSqTo` is the squared distance
by `conj_toComplex`, and `realCompare_eq` orders it. A point closer to a
root than half the separation `mahlerPrec_separates` guarantees is nearer to
it than to any other root, so the nearest root is that number.

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
theorem PolyQuot.roots?_isSome [ZPoly.CheckedIrreducible p] (...) :
    (PolyQuot.roots? f rep h).isSome

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
The internal `PolyQuot.Roots.sameValue?` operation has separate soundness and
completeness contracts because root merging depends on it even though no public
`BEq AlgebraicRoot` instance exists.

State corresponding fixed-field theorems through `PolyQuot.toComplex`. For finite
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
2. `PolyQuot.toAdjoinRoot_bijective`, field-law transfer, and approximation
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
  Nearest.lean               : imaginary unit, conjugation, real order, nearest root
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

## Complex API and algebraic closure

The canonical representation is interpreted through `OrientedIsolation`:
`sign`, `real_iff`, and `conj_root` justify the orientation tag and reflected
certificate. Injectivity combines uniqueness of the raw canonical base with
uniqueness of the orientation. `conj_toComplex` uses certificate transport;
`StarRing` and `conjRingEquiv` expose its algebraic laws.

`partialCompare_eq`, `le_iff`, and `lt_iff` characterize the global complex
partial order, with a `PartialOrder`, `IsStrictOrderedRing`, and
`toComplexOrder`. These retain the core executable comparison data. They do
not provide a total order on complex algebraic values.

`Radical.select_value` proves the candidate selector succeeds and chooses
Mathlib's principal power. `PrincipalRoot.eq_of_max` characterizes that branch
by maximal real part and the nonnegative imaginary side on ties.
`nthRoot_toComplex`, `nthRoot_pow`, `sqrt_toComplex`, and `sqrt_sq` provide
the public contracts. `nthRoot_conj` requires exclusion of the negative real
branch cut. The real companion proves agreement with the nonnegative real
square root and the typed real/imaginary projection identities.

`QAdjoin.ofAlgebraic?_isSome_iff` is an exact field-membership decision;
`ofAlgebraic?_sound`, `common_size`, and `common_get` prove coordinate recovery.
`AlgebraicPoly.ofPolynomial` bridges arbitrary Mathlib polynomials to the
existing complete algebraic-coefficient solver. This supplies `IsAlgClosed`;
the minimal-polynomial theorem supplies `Algebra.IsAlgebraic ℚ`, and together
they give `IsAlgClosure ℚ AlgebraicNumber`. Axiom audits include the principal
radical and algebraic-closedness instances.

### Enumeration order

`AlgebraicNumber.rootKey` maps to a lexicographic centre key;
`rootLe_iff`, `rootLe_trans`, and `rootLe_total` prove the computational
comparator's total-preorder laws. `ZPoly.algebraicRoots_sorted` proves the
actual output is sorted by that comparator. `rootLe_conj` places the lower
member before the upper one, and `between_conjugates` proves any value
between them equals one of the endpoints. Together with
`ZPoly.conj_mem_algebraicRoots` and `algebraicRoots_nodup`, these give adjacent
nonreal conjugate pairs. The key is injective on nonreal canonical values
(`eq_of_rootKey`); no cross-factor real-value ordering is inferred from
centre ordering.

`nthRoot_conj_of_not_lt` restates the branch-cut condition using the executable
complex partial order: `¬ a < 0` excludes exactly the negative real axis.

## Isolation fast paths

Coordinate interval tests have soundness theorems for all enclosed complex
values. The bounded pair-refinement search preserves those theorems by
`RefinedIsolation.refineTo_root`. `realCompare_eq`, `partialCompare_eq`,
`lt_iff`, and `le_iff` retain their statements; failed probes invoke the exact
reference algorithms. The real search has a product-separation cap; complex
probes have two fixed rounds. Neither establishes equality from overlap.

Lazy principal-root filtering preserves the principal root. On each retained
half circle, distinct candidates have distinct real coordinates; positive real
inputs retain their real roots and choose the largest. Interval selection is
sound independently of its refinement budget. A failed fast selection invokes
the existing exact selector, preserving `nthRoot_toComplex` and `sqrt_toComplex`.
The roots-of-unity constructor agrees with `Complex.exp (2 * π * I * q)` and
`Complex.isPrimitiveRoot_exp_rat` gives its exact order. Its selector uses the
least positive argument among integer roots of unity, equivalently the largest
real part on the upper half circle.

`Unity.generator?_value` proves the integer-binomial selector total.
`rootOfUnity_toComplex` states its exponential value; `rootOfUnity_primitive`,
`rootOfUnity_add`, and `rootOfUnity_neg` expose exact order and rational-angle
laws. `RootSelection.integerRoots?_mem` derives completeness of the lazy
integer isolations from the canonical solver, while `maximum?_spec` covers
both interval selection and the exact fallback.

## Direct radical proof obligations

The [direct radical design](../../HexNumberField/SPEC/hex-number-field.md#direct-certified-radicals-and-cyclotomic-embeddings) is a
future replacement for the general solver route. The following inventory is
against Lean `v4.34.0-rc2` and Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0` from `lake-manifest.json`.
Names in the missing-obligation table are proposed declarations, not existing
infrastructure. A proof of an approximate residual or of `b^n = a` alone does
not establish the public principal-root contract.

### Available bridges and their limits

- [HexNumberFieldMathlib/PrincipalRoot.lean](../PrincipalRoot.lean) contains
  `PrincipalRoot.arg_root`, `sector`, and `eq_of_max`. They characterize the
  branch and selector, but do not give executable interval bounds or iteration
  counts. `Radical.lean` already proves `nthRoot_toComplex`, `nthRoot_pow`,
  `sqrt_toComplex`, and `sqrt_sq`; those statements remain unchanged.
- [HexRootsMathlib/MahlerPrec.lean](../../HexRootsMathlib/MahlerPrec.lean)
  supplies `mahlerPrec_separates` and `root_eq_of_discsMeet`.
  [Refinement.lean](../../HexRootsMathlib/Refinement.lean) supplies
  `RefinedIsolation.refineTo_root`; the completeness proof supplies
  `RefinedIsolation.refineTo?_isSome_mixed`. These justify refinement of an
  existing selected root, but do not certify a new principal enclosure or
  define its canonical representative.
- [HexNumberField/Basic.lean](../../HexNumberField/Basic.lean) defines
  `IsCanonical` by a deterministic all-roots run. `rawRep?`,
  `canonicalRep?`, and `AlgebraicRoot.exactFactor?` still enumerate isolations.
  [Basic.lean](../Basic.lean)'s private `RefinedIsolation.eq_of_canonical`
  and public `AlgebraicNumber.toComplex_injective` depend on that provenance.
  They must be replaced, not applied to arbitrary new certificates.
- [FactorSoundness.lean](../../HexBerlekampZassenhausMathlib/FactorSoundness.lean)
  supplies `factorize_irreducible_of_nonUnit` and `ZPoly.isIrreducible_iff`.
  `CheckedIrreducible.irreducibleRat` currently consumes the Boolean field;
  it needs cases for retained-factor and cyclotomic evidence after migration.
- [Unity.lean](../Unity.lean) has `Unity.generator?_value`,
  `rootOfUnity_toComplex`, and `rootOfUnity_primitive`. It uses integer
  binomials and `QAdjoin` powers. It does not recognize arbitrary roots of
  unity or reuse a minimal polynomial for arbitrary coprime powers.
- The pinned Mathlib
  [complex powers](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean)
  provide `Complex.cpow_nat_inv_pow` and `Complex.cpow_mul`; the latter has
  argument hypotheses. The
  [cyclotomic root API](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean)
  provides `Polynomial.isRoot_cyclotomic_iff_charZero`,
  `Polynomial.cyclotomic.irreducible_rat`, and
  `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`.
  `IsPrimitiveRoot.pow_of_coprime` is in `RingTheory/RootsOfUnity/PrimitiveRoots`.
  These do not manufacture Hex runtime certificates.
- Dense `substPow` and `toPolynomial_substPow`, `HexCyclotomic`, and its
  companion are still prerequisites specified by the
  [cyclotomic SPEC](../../SPEC/Libraries/hex-cyclotomic.md). Their existence
  must not be inferred from Mathlib's `Polynomial.expand` or Hex's separate
  sparse substitution API. `Hex.Nat.factor?` is explicitly partial.
  `Hex.Nat.PrimeCert` offers `small`, `pock`, and `pock3`, not a general
  trial-division certificate constructor. The total rational-angle constructor
  therefore uses a direct integer-binomial fallback if checked index search
  fails; it does not assume complete prime-certificate generation.
  The recognition bound `N ≤ 2*φ(N)^2` also needs a
  new proof; no such bridge is supplied by the existing unity implementation.

### Missing lemmas and ownership

Every budget below is computed by the executable definition in the design,
including the final full-precision attempt. `_isSome` must use those actual
budgets and strategies, not a larger existential amount of fuel.

| Owner / proposed declaration | Required statement and proof inputs |
| --- | --- |
| HexPolyMathlib: `toPolynomial_substPow` | Coefficient spread maps to `Polynomial.expand`, including index zero; derive evaluation at `z` as evaluation at `z^n` |
| HexNumberFieldMathlib.Radical: `annihilator_root`, `annihilator_squarefree` | For `a ≠ 0`, `n > 0`, substitution vanishes at the principal root and is primitive, positive-leading, degree `n*degree(a.p)`, and squarefree; use the derivative and nonzero constant coefficient |
| HexRootsMathlib: `root_bounds` | Cauchy and reciprocal-Cauchy rational bounds for nonzero roots; no reciprocal of `p[0]=0` |
| HexNumberFieldMathlib.Radical: `enclose_contains`, `enclose_radius` | Tagged `atan2`, bisection, series remainders and outward rounding contain `cpow` with radius `≤ 2^-bits` at the stated computed precision; handle every convention and the closed one-sided cut |
| HexNumberFieldMathlib.Radical: `sqrt_enclose` | Stable component formulas, safe-denominator coverage after the computed refinement, division soundness, and the same radius bound; agreement with `Complex.sqrt` |
| HexRootsMathlib: `certifyNear_sound`, `certifyNear_isSome` | Three-radius linear Pellet soundness plus quantitative success for centre error `≤ s/32`, half-width `s`, and the stated separation slack; use the owning design's Taylor bounds with the `1-η` derivative correction and executable `lo`/`hi` estimates; connect the certified root to the supplied enclosure |
| HexNumberFieldMathlib.Radical: `factorRoot_sound`, `factorRoot_isSome` | Product and irreducibility evidence imply precisely one factor passes the shared-centre test; its root equals the principal root; at most the number of factors is tested |
| HexNumberFieldMathlib: `IrreducibleEvidence.sound` | Each Boolean, retained factor-output, and checked-positive-index cyclotomic evidence constructor yields rational irreducibility; transport primitive normalization and positive degree |
| HexNumberFieldMathlib: `Canonical.exists`, `Canonical.unique` | Fixed fine-grid successful certificates form a finite nonempty set for the selected root; local enumeration contains exactly all relevant successes; equal roots yield the same square and deterministic certificate data |
| HexNumberFieldMathlib: `ofCertified_isSome`, `ofCertified_toComplex` | Normalized irreducible input plus selected certified root produces the local canonical form at computed refinement budget and preserves its value |
| HexNumberFieldMathlib: injectivity, equality and orientation migration | Reprove `toComplex_injective`, lawful Boolean/structural equality, orientation, constant-time `conj`, `conj_conj`, and root enumeration/nearest ties for the new base; input refinement histories cannot affect equality |
| HexNumberFieldMathlib.Radical: `rational_root`, `reduce_binomial` | Exact integer-power witnesses justify rational and partial-power routes; a negative rational retains principal turn `1/(2*n)` |
| HexNumberFieldMathlib.Radical: `nthRoot_mul` | For positive `r,s`, iterated principal roots equal the principal `(r*s)`th root, including zero and the cut; discharge `cpow_mul`'s hypotheses using divided arguments |
| HexCyclotomicMathlib | The existing cyclotomic SPEC's polynomial correspondence, degree/totient, rational irreducibility, and checked-factorization transport; no algebraic-number dependency |
| HexNumberFieldMathlib.Unity: `ofChecked_value`, `power_minpoly` | Rational-angle enclosure selects the primitive embedding; a coprime power retains the exact normalized `Φ_N`; a noncoprime power uses `Φ_(N/gcd(j,N))` |
| Mathlib-facing number theory: `order_le_totient_sq` | Prove `N ≤ 2*φ(N)^2` for positive `N`, from prime-power totient formulas; the factor at prime 2 contributes at most 2 and each odd prime contributes at most 1 to `N/φ(N)^2` |
| HexNumberFieldMathlib.Unity: `unityOrder_spec`, `unity_spec` | For monic `a.p`, prove the bounded integer remainder recurrence satisfies `R_j = 1 ↔ a.toComplex^j = 1`; justify rejecting nonmonic inputs, minimal positive order, and exhaustive failure through `2*d²`. Angle recovery covers all reduced residues and uniquely matches the supplied embedding without canonicalizing candidates |
| HexNumberFieldMathlib.Unity: `binomial_value` | For positive order, `X^N-1` is squarefree; rational-angle enclosure and selected-factor construction give the same canonical value as `ofChecked`, using the degree-`N` computed bounds on index-search failure |
| HexNumberFieldMathlib.Unity: `radical_value` | Normalize the turn to `(-1/2,1/2]` before dividing; the result equals the principal `cpow`, including negative-axis endpoint handling |
| HexNumberFieldMathlib: representation round trips | Generated checked constructors preserve polynomial and selected root and return the identical canonical value; old raw/reflected isolations normalize faithfully; retaining the current `rootNear` printer requires its strict nearest-root margin after `digitsFor` rounding, including nested `QAdjoin.ofCoeffs` expressions |

For factorization, reuse the existing complete integer factorizer and its
bounded `factorTrial` fallback; near-root certification does not assume a
fast modular split always exists. Each specialized route composes its value
lemma with `ofCertified_toComplex` and canonical injectivity, establishing
structural equality with the general route. Budgeted helpers are sound for
any budget and report unknown when incomplete; only exhaustive recognition
may prove a negative answer.

The headline proof remains `AlgebraicNumber.nthRoot_toComplex`, now proved
through the direct annihilator/enclosure/factor/canonical chain and every
specialized dispatch arm. `sqrt_toComplex` follows with its dedicated
component-formula bridge. Complete these proofs and their axiom audit before
replacing the public implementation. Compatibility verification includes the
real-algebraic and number-field-tower companions; broad complex comparison
algorithms remain outside this work.
