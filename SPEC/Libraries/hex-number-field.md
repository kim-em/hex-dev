# hex-number-field (depends on hex-poly-z + hex-roots + hex-resultant + hex-berlekamp-zassenhaus + hex-matrix + hex-row-reduce)

Executable algebraic numbers in `ℂ`, fixed number fields, and roots of
polynomials with algebraic coefficients. The library provides three related
representations:

- `QAdjoin p x` is the canonical coordinate representation in the fixed field
  `ℚ(x)`, with `x : SimpleRoot p` and rational coefficients reduced modulo `p`.
- `AlgebraicRoot` identifies a root of a primitive, positive-leading,
  squarefree integer polynomial. The polynomial need not be irreducible or
  minimal. This is the factorization-lazy representation used by arithmetic.
- `AlgebraicNumber` identifies a root of its canonical irreducible minimal
  polynomial. This is the exact canonical representation.

“Lazy” refers only to factorization. Every stored root has a
`RefinedIsolation`, so identity and approximation remain certified eagerly.

## Executable irreducibility

`Hex.ZPoly.IsIrreducible p` remains the Mathlib-free certificate used by
`QAdjoin` field operations and canonical `AlgebraicNumber` values. Its decision
procedure uses the existing ladder: canonical degree-one recognition, rational
root checks in degrees two and three, small-prime Rabin certificates, then
Berlekamp-Zassenhaus factorization. The companion proves equivalence with
Mathlib irreducibility over `ℤ` and, after Gauss's lemma, over `ℚ`.

## Core types

```lean
namespace Hex

structure QAdjoin (p : ZPoly) (x : SimpleRoot p) where
  coeffs    : DensePoly Rat
  degree_lt : coeffs.degree? < p.degree?

/-- A factorization-lazy algebraic number. -/
structure AlgebraicRoot where
  p          : ZPoly
  prim       : ZPoly.Primitive p
  pos_lc     : 0 < p.leadingCoeff
  squarefree : HasOnlySimpleRoots p
  x          : SimpleRoot p
  rep        : RefinedIsolation p
  rep_mk     : SimpleRoot.mk rep = x

/-- A canonical algebraic number. -/
structure AlgebraicNumber where
  p      : ZPoly
  prim   : ZPoly.Primitive p
  pos_lc : 0 < p.leadingCoeff
  irred  : ZPoly.IsIrreducible p
  x      : SimpleRoot p
  rep    : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x

structure RootCount where
  root : AlgebraicRoot
  multiplicity : Nat
  multiplicity_pos : 0 < multiplicity

/-- `.all` is the root set of the zero polynomial. -/
inductive RootSet where
  | all
  | finite (roots : Array RootCount)

/-- A polynomial with canonical algebraic coefficients. The constructor trims
    trailing coefficients using semantic `AlgebraicNumber.isZero`. -/
opaque AlgebraicPoly
def AlgebraicPoly.ofArray (coeffs : Array AlgebraicNumber) : AlgebraicPoly
def AlgebraicPoly.coeffs (f : AlgebraicPoly) : Array AlgebraicNumber
def AlgebraicPoly.degree? (f : AlgebraicPoly) : Option Nat
def AlgebraicPoly.isZero (f : AlgebraicPoly) : Bool

end Hex
```

Do not instantiate `DensePoly AlgebraicNumber`. `DensePoly` requires
`DecidableEq` on coefficients so that trailing-zero normalization is semantic,
but structural equality on `AlgebraicNumber` is finer than equality of the
represented complex values. `AlgebraicPoly` owns the required semantic trimming
without exporting an incorrect `DecidableEq`.

## Equality and zero

`AlgebraicNumber` keeps its canonical `BEq`: compare minimal polynomials, then
compare refined isolations with `sameRoot`.

`AlgebraicRoot` uses two paths:

1. If the stored polynomials agree, compare the refined isolations directly.
2. Otherwise exactify both roots and use canonical `AlgebraicNumber` equality.

The second path can factor twice and is not a fast arithmetic primitive. A future
optimization may compare `gcd a.p b.p` and the two isolations without computing
minimal polynomials, but it does not change the v1 semantics.

```lean
def AlgebraicNumber.isZero (a : AlgebraicNumber) : Bool := a.p == X

/-- True exactly when the selected root is zero. Squarefreeness makes the
    constant-coefficient and isolation test decisive. -/
def AlgebraicRoot.isZero (a : AlgebraicRoot) : Bool :=
  a.p.coeff 0 == 0 && a.rep.containsZero
```

## Fixed-field operations

`QAdjoin p x` retains canonical reduced rational coordinates. Addition,
subtraction, negation, multiplication modulo `p`, and rational scalar actions do
not require irreducibility. Inversion and the `Field` instance require
`[ZPoly.IsIrreducible p]` and use polynomial extended gcd over `ℚ`.

```lean
def QAdjoin.approx (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    RefinedIsolation p × DyadicComplexBall
```

Approximation refines once, returns the refined representative for threading,
and always returns a sound ball. The requested radius is guaranteed by the
companion's refinement-completeness theorem.

## Canonicalization and exactification

```lean
def AlgebraicNumber.toQAdjoin (a : AlgebraicNumber) : QAdjoin a.p a.x
def AlgebraicNumber.toRoot (a : AlgebraicNumber) : AlgebraicRoot

def QAdjoin.toAlgebraicNumber? [ZPoly.IsIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option AlgebraicNumber
def QAdjoin.toAlgebraicNumber [ZPoly.IsIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : AlgebraicNumber

/-- Checked implementation layer. -/
def AlgebraicRoot.exact? (a : AlgebraicRoot) : Option AlgebraicNumber
/-- Primary total API. -/
def AlgebraicRoot.exact (a : AlgebraicRoot) : AlgebraicNumber :=
  a.exact?.getD (panicWith 0 "AlgebraicRoot.exact: certification failed")
```

`QAdjoin.toAlgebraicNumber?` computes the minimal polynomial of the
multiplication operator by row reduction, clears denominators, normalizes the
primitive part, and identifies the matching isolated root.

`AlgebraicRoot.exact?` factors `a.p`, selects the unique irreducible factor whose
isolated root agrees with `a.rep`, and returns that factor in canonical form.
`exact` is the primary interface. It uses `panicWith` only on the checked
implementation's `none` branch; `exact?_isSome` proves that branch unreachable.

## Factorization-lazy arithmetic

Each operation has a checked `Option` form and a primary total wrapper. The
checked form returns `none` only if a certificate fails to appear within its
input-computable bound. Companion `_isSome` theorems retire every such branch.

```lean
def AlgebraicRoot.add? (a b : AlgebraicRoot) : Option AlgebraicRoot
def AlgebraicRoot.add  (a b : AlgebraicRoot) : AlgebraicRoot
-- likewise sub, mul, div, and inv; neg is certificate-free

def AlgebraicNumber.add (a b : AlgebraicNumber) : AlgebraicNumber :=
  (a.toRoot.add b.toRoot).exact
-- likewise sub, mul, neg, inv, and div
```

- `neg` substitutes `-X` and reflects the isolation.
- `add?` takes the primitive positive-leading squarefree part of
  `resultant_y(a.p(y), b.p(t-y))`.
- `sub?` composes addition and negation.
- `mul?` handles zero first, then uses
  `resultant_y(a.p(y), y^deg(b.p) * b.p(t/y))`. It removes any
  introduced `X` factor before squarefree normalization.
- `inv? 0 = some 0`. Otherwise it reverses the coefficients of `a.p`, removes
  any `X` factor, maps the isolation through inversion, and re-certifies it.
- `div?` composes multiplication and inversion.

For a binary eliminant, the desired result may coincide with values from other
pairs of conjugates. Refine the operation ball and candidate isolations to
`rootDisambiguationPrec`, computed from one further eliminant and a
resultant/root-product lower bound. At that precision exactly one candidate
isolation meets the operation ball. Do not use unbounded refinement.

Canonical `AlgebraicNumber` arithmetic converts inputs with `toRoot`, performs
the lazy operation, then calls `exact`. A many-input common-field routine is used
internally only for polynomials with canonical algebraic coefficients.
Canonical `AlgebraicNumber` exposes the corresponding `Field` instance, with
`inv 0 = 0`. `AlgebraicRoot` exposes named operations but no `Field` instance:
two semantically equal lazy results can have different enclosing polynomials, so
the field laws do not hold for structural equality on that record.

## Polynomial roots

```lean
def QAdjoin.roots? [ZPoly.IsIrreducible p]
    (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Option RootSet
def QAdjoin.roots [ZPoly.IsIrreducible p] (...) : RootSet

def AlgebraicPoly.roots? (f : AlgebraicPoly) : Option RootSet
def AlgebraicPoly.roots  (f : AlgebraicPoly) : RootSet
```

The zero polynomial returns `some .all`; `none` is reserved for certification
failure. Finite output is normalized, duplicate-free, sorted by polynomial then
isolation coordinates, and carries positive multiplicities.

For `QAdjoin.roots?`:

1. Run Yun decomposition over the coefficient field. Process each squarefree
   component separately; a root from the component indexed by `e` receives
   multiplicity `e`.
2. Clear coefficient denominators and form the norm eliminant over `ℚ` by a
   resultant with `p`. It is nonzero because coefficients are reduced modulo the
   irreducible `p`.
3. Normalize and isolate the eliminant's roots.
4. Reject candidates belonging only to other embeddings of `QAdjoin p x` by
   evaluating the original component at the candidate and the selected `x`.
   Refute wrong candidates at `rootDisambiguationPrec`.
5. Return the surviving `AlgebraicRoot` values with the Yun multiplicity.

`AlgebraicPoly.roots?` first embeds all nonzero coefficients into one computed
primitive `QAdjoin`, then invokes the fixed-field algorithm. This internal
common-field construction is deterministic and bounded but is not used for
binary arithmetic.

## Totalization

`panicWith fallback message` prints in compiled code and is definitionally the
fallback for proofs. Total algebraic operations use it only around checked forms
whose `_isSome` theorem is part of the companion contract. `exact`, arithmetic,
and both `roots` functions are the primary user APIs; the `?` forms remain public
for diagnostics and staged proofs.

`AlgebraicNumber` has canonical zero `p = X`, so it supplies the `Inhabited`
fallback used by exactification. `RootSet.all` is the loud fallback for the two
total root wrappers; their `_isSome` theorems make it unreachable.

## File organisation

```text
HexNumberField/
  Basic.lean          : core types, equality, zero, panicWith
  QAdjoin.lean        : fixed-field operations and approximation
  Convert.lean        : canonicalization and exactification
  Lazy.lean           : eliminants and lazy arithmetic
  Disambiguate.lean   : candidate bounds and certified selection
  AlgebraicPoly.lean  : semantic coefficient-polynomial representation
  Roots.lean          : fixed-field and algebraic-coefficient root APIs
```

Conformance and benchmark drivers live in the shared `conformance/` and
`bench/` sub-projects.

## Conformance

- *core*: at least three cases per public operation, including `√2 + √2`,
  `√2 * √2`, `√2 + (-√2)`, inversion of zero, equal values represented by
  different nonminimal polynomials, an enclosing polynomial with irrelevant
  factors, repeated input roots, and a conjugate-embedding impostor.
- *ci*: deterministic small-degree fixtures checked by cypari2. Use
  python-flint independently for integer resultants, factorization, and certified
  complex-root balls.
- *local*: degree-product stress cases and optional Nemo/Hecke comparisons.

Sage is not an oracle. Root comparisons use multiplicity buckets and compare the
oracle's independently computed decomposition with Lean's finite output.

## Complexity and Phase 4 budgets

- Fixed-field arithmetic has the existing dense-polynomial costs; a compiled
  degree-10 field operation remains capped at 100 ms on the reference host.
- A lazy binary operation has eliminant degree at most
  `deg(a.p) * deg(b.p)`. Its ceiling is the measured resultant cost plus the
  existing HexRoots ceiling at that eliminant degree. Do not promise a faster
  end-to-end time than root isolation itself.
- Degree-product at most 20 is the largest merge-facing lazy arithmetic class.
  Larger cases are local until new measurements justify promotion.
- Exactification adds one Berlekamp-Zassenhaus factorization and factor-root
  selection. Root APIs add Yun decomposition and one norm eliminant per
  squarefree component.

Phase 4 records separate timings for eliminant construction, isolation,
disambiguation, and exactification so regressions are attributable.

## References

- Cohen, H. *A Course in Computational Algebraic Number Theory.* Springer,
  1993, sections 4.1, 4.2, and 4.5.
- Belabas, K. *Topics in computational algebraic number theory.* J. Théorie
  des Nombres de Bordeaux 16 (2004), 19-63.
- Bostan, A.; Flajolet, P.; Salvy, B.; Schost, É. *Fast computation of
  special resultants.* JSC 41 (2006), 1-29.
