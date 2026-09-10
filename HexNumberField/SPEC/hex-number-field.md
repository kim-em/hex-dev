# hex-number-field (depends on hex-poly-z + hex-roots + hex-resultant + hex-berlekamp-zassenhaus + hex-matrix + hex-row-reduce)

Executable algebraic numbers in `ℂ`, fixed number fields, and roots of
polynomials with algebraic coefficients. The library provides three related
representations:

- `PolyQuot p x` is the canonical coordinate representation in the presentation
  `ℚ[X]/(p)`, with `x : SimpleRoot p` fixing the embedding and rational
  coefficients reduced modulo `p`. `QAdjoin a`, the fixed field `ℚ(a)` of a
  canonical number, is `PolyQuot a.p a.x`.
- `AlgebraicRoot` identifies a root of a primitive, positive-leading,
  squarefree integer polynomial. The polynomial need not be irreducible or
  minimal. This is the factorization-lazy representation used by arithmetic.
- `AlgebraicNumber` identifies a root of its canonical irreducible minimal
  polynomial. This is the exact canonical representation.

“Lazy” refers only to factorization. Every stored root has a
`RefinedIsolation`, so identity and approximation remain certified eagerly.

## Executable irreducibility

The shipped Mathlib-free API separates the semantic class
`Hex.ZPoly.Irreducible p` from the factorization-backed Boolean
`Hex.ZPoly.isIrreducible p`. This library adds the runtime-constructible wrapper

```lean
class ZPoly.CheckedIrreducible (p : ZPoly) : Prop where
  is_true : ZPoly.isIrreducible p = true
  pos_degree : 0 < p.natDegree
```

Checked constructors branch on the Boolean and can therefore return this
evidence without importing factorization correctness. The positive-degree
field is essential because the integer irreducibility checker also accepts
prime constants, whose rational quotients are not number fields. The Mathlib
companion uses `ZPoly.isIrreducible_iff` to turn `CheckedIrreducible` into the
shipped semantic `ZPoly.Irreducible` class and then into irreducibility over `ℚ`.
The computational library exposes the operations needed by its algorithms; it
does not claim a law-bearing field instance from the Boolean alone.

## Core types

```lean
namespace Hex

structure PolyQuot (p : ZPoly) (x : SimpleRoot p) where
  coeffs    : DensePoly Rat
  degree_lt : coeffs.natDegree < p.natDegree

@[ext] theorem PolyQuot.ext (h : a.coeffs = b.coeffs) : a = b
instance : DecidableEq (PolyQuot p x)

/-- The fixed field `ℚ(a)` of a canonical number. -/
def QAdjoin (a : AlgebraicNumber) : Type := PolyQuot a.p a.x  -- implicit_reducible

/-- A factorization-lazy algebraic number. -/
structure AlgebraicRoot where
  p          : ZPoly
  prim       : ZPoly.Primitive p
  pos_lc     : 0 < p.leadingCoeff
  pos_degree : 0 < p.natDegree
  squarefree : HasOnlySimpleRoots p
  x          : SimpleRoot p
  rep        : RefinedIsolation p
  rep_mk     : SimpleRoot.mk rep = x

/-- A canonical algebraic number. Its constructor is private. -/
opaque AlgebraicNumber
def AlgebraicNumber.p (a : AlgebraicNumber) : ZPoly
def AlgebraicNumber.prim (a : AlgebraicNumber) : ZPoly.Primitive a.p
def AlgebraicNumber.pos_lc (a : AlgebraicNumber) : 0 < a.p.leadingCoeff
def AlgebraicNumber.pos_degree (a : AlgebraicNumber) :
    0 < a.p.natDegree
def AlgebraicNumber.checked (a : AlgebraicNumber) :
    ZPoly.CheckedIrreducible a.p
def AlgebraicNumber.squarefree (a : AlgebraicNumber) :
    HasOnlySimpleRoots a.p
def AlgebraicNumber.rep (a : AlgebraicNumber) : RefinedIsolation a.p
def AlgebraicNumber.IsCanonical (p : ZPoly)
    (squarefree : HasOnlySimpleRoots p) (rep : RefinedIsolation p) : Prop
def AlgebraicNumber.canonical (a : AlgebraicNumber) :
    AlgebraicNumber.IsCanonical a.p a.squarefree a.isolation.base
def AlgebraicNumber.x (a : AlgebraicNumber) : SimpleRoot a.p
def AlgebraicNumber.rep_mk (a : AlgebraicNumber) :
    SimpleRoot.mk a.rep = a.x
def AlgebraicNumber.zeroRep : RefinedIsolation ZPoly.X
def AlgebraicNumber.canonicalRep? (p : ZPoly)
    (squarefree : HasOnlySimpleRoots p) (rep : RefinedIsolation p)
    (hzero : p ≠ ZPoly.X) :
    Option {r : AlgebraicNumber.OrientedIsolation p //
      AlgebraicNumber.IsCanonical p squarefree r.base ∧ r.rep.sameRoot rep = true}
theorem AlgebraicNumber.ext (a b : AlgebraicNumber) (hp : a.p = b.p)
    (hrep : HEq a.isolation b.isolation) : a = b
def AlgebraicNumber.zero : AlgebraicNumber
instance : Zero AlgebraicNumber
instance : Inhabited AlgebraicNumber

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
def AlgebraicPolyNormalized (coeffs : Array AlgebraicNumber) : Prop
def AlgebraicPoly.data (f : AlgebraicPoly) : Array AlgebraicNumber
def AlgebraicPoly.normalized (f : AlgebraicPoly) :
    AlgebraicPolyNormalized f.data
def AlgebraicPoly.ofArray (coeffs : Array AlgebraicNumber) : AlgebraicPoly
def AlgebraicPoly.coeffs (f : AlgebraicPoly) : Array AlgebraicNumber
def AlgebraicPoly.coeff (f : AlgebraicPoly) (n : Nat) : AlgebraicNumber
def AlgebraicPoly.size (f : AlgebraicPoly) : Nat
def AlgebraicPoly.degree? (f : AlgebraicPoly) : Option Nat
abbrev AlgebraicPoly.natDegree (f : AlgebraicPoly) : Nat
def AlgebraicPoly.isZero (f : AlgebraicPoly) : Bool
def AlgebraicPoly.beq (f g : AlgebraicPoly) : Bool
instance : BEq AlgebraicPoly

end Hex
```

Here and in the tower SPEC, `opaque` marks a public abstraction boundary, not a
requirement that the implementation literally use an `opaque` Lean declaration.
Implementations use representation-private structures where constructors or
recursors are needed internally.

The shipped representation is described here; the required
[direct radical design](hex-number-field.md#local-canonicalization-and-representation-migration)
replaces all-roots provenance with a deterministic local normal form in a
coordinated constructor migration. Every smart constructor normalizes the primitive polynomial. Zero uses the
fixed certified `zeroRep`. Other values use `rawRep?` to re-isolate the
polynomial with the fixed strategy at `separationDepth`. The private record
stores an `OrientedIsolation`: a canonical real or upper-half-plane `base`,
and a `RootSide` tag (`real`, `upper`, or `lower`). The `valid` field proves
that the base meets the real axis for `real`, or that its centre is above
`radiusHi` for either nonreal tag. `rep` returns the base except for `lower`,
where it returns `base.conj`.

`canonicalRep?` reflects a lower input before selecting the unique raw base,
checks its orientation, and checks that the selected oriented representative
matches the original input. The companion proves these checks succeed.
Canonical provenance belongs to the **base**, and together with the side
makes equal complex values have identical hidden data. An arbitrary
proof-relevant certificate cannot be inserted as a new canonical base.

`conj` fixes real values and flips the two nonreal tags, sharing the base,
polynomial and certificates. Repeated conjugation does not grow a certificate
chain. Accessing a lower `rep` transports the base certificate through the
`AtomCertificate.conj` constructor, whose soundness follows by reflection;
it does not rerun an NK or Pellet checker. `PolyQuot` display must preserve
such transported certificates with `ofIsolation`, rather than printing an
`ofSquare` term whose fresh checker need not succeed.

Do not instantiate `DensePoly AlgebraicNumber` in the Mathlib-free layer.
`DensePoly` requires a kernel `DecidableEq` on coefficients so trailing-zero
normalization is semantic, while canonical algebraic-number equality is exposed
here as a Boolean operation whose correctness is proved only in the companion.
Structural equality on factorization-lazy `AlgebraicRoot` is finer than equality
of represented complex values. `AlgebraicPoly` owns the required semantic
trimming without exporting an unjustified `DecidableEq`. That Boolean
operation is `AlgebraicPoly.beq` (with its `BEq` instance): coefficientwise
canonical equality over the trimmed data. Its faithfulness on canonical
coefficients is the companion theorem `AlgebraicPoly.beq_iff`, which equates
Boolean equality with equality of the semantic polynomial interpretations and
is derived from `LawfulBEq AlgebraicNumber` plus trimming. `coeff n` is the
canonical coefficient (`0` beyond the degree) and `size` is the trimmed length
backing `degree?`; all three are exercised by the module's compiled regressions.

## Equality and zero

`AlgebraicNumber` keeps its canonical `BEq`: compare minimal polynomials, then
compare refined isolations with `sameRoot`.

`AlgebraicRoot` uses two paths:

1. If the stored polynomials agree, compare the refined isolations directly.
2. Otherwise compute `gcd a.p b.p` over `ℚ`. If it is constant, the roots
   cannot agree and comparison returns false without exactifying. If it is
   nonconstant, exactify both roots and use canonical `AlgebraicNumber`
   equality.

The nonconstant-gcd fallback can factor twice and is not a fast arithmetic
primitive. The gcd guard prevents repeated factorization for coprime
enclosing polynomials during cross-component root merging without changing
the semantics. It is a discriminator, not a constant-time operation:
computing a rational gcd between two high-degree enclosing polynomials can
itself incur coefficient growth.

```lean
def AlgebraicNumber.isZero (a : AlgebraicNumber) : Bool := a.p == X

/-- True exactly when the selected root is zero. The refined separation bound
    makes the constant-coefficient and closed-disc test decisive. -/
def AlgebraicRoot.isZero (a : AlgebraicRoot) : Bool :=
  a.p.coeff 0 == 0 && RefinedIsolation.containsZero a.rep
```

`RefinedIsolation.containsZero` is introduced here. It tests membership of zero
in the isolation's closed circumscribed disc, including boundary contact, by
delegating to the generic exact `DyadicSquare.discContains` geometry primitive.

## Fixed-field operations

`PolyQuot p x` retains canonical reduced rational coordinates. Addition,
subtraction, negation, multiplication modulo `p`, and rational scalar actions do
not require irreducibility, and neither do the constants:

```lean
def PolyQuot.ofRat (q : Rat) : PolyQuot p x
instance : NatCast (PolyQuot p x)
instance : IntCast (PolyQuot p x)
instance (n : Nat) : OfNat (PolyQuot p x) (n + 2)
```

so numerals such as `2 : PolyQuot p x` denote `(2 : Rat) • 1`, and the
companion's field structure reuses these casts rather than defining its own.
`instance : Coe (DensePoly Rat) (PolyQuot p x)` reduces a rational polynomial,
so `#p[0, 0, 2]` denotes `2x²` at that type, and
`instance : Repr (PolyQuot p x)` prints an element as the expression that
rebuilds it, `PolyQuot.ofSquare p s f`: the reduced coordinates `f`, together
with the polynomial and the isolating square that name the field and select
the root.

```lean
def PolyQuot.ofSquare (p : ZPoly) (s : DyadicSquare) (f : DensePoly Rat)
    (hw : atomWitness p s := by decide)
    (hp : (mahlerPrec p : Int) ≤ s.prec := by decide) :
    PolyQuot p (SimpleRoot.ofSquare p s hw hp)
```

Pasting the output back reproduces the element and prints identically; the two
side conditions on the square are decidable and discharged by the auto-params.
The instance is `unsafe` and takes the square from the `Quot` with `unquot`, as
Mathlib's `Multiset` and `Finset` instances do. Which representative it finds
is invisible in the result, because `Intersects` compares stored squares, so
every representative of the root rebuilds the same element. The resulting type
is propositionally, not definitionally, the original: a pasted value is an
element of `PolyQuot p (SimpleRoot.ofSquare …)`, so comparing it with the
original spelling needs a transport. Inversion requires
`[ZPoly.CheckedIrreducible p]` and uses a monic-normalized polynomial extended
gcd over `ℚ` to control rational coefficient growth. For the presentation a
canonical number induces, that evidence is an instance:

```lean
instance (a : AlgebraicNumber) : ZPoly.CheckedIrreducible a.p
```

`QAdjoin` is `implicit_reducible` rather than an abbreviation, so it keeps its
own head symbol for instance search while still unfolding to `PolyQuot a.p a.x`
everywhere else. That buys it one instance `PolyQuot` cannot have:

```lean
def QAdjoin.ofCoeffs (a : AlgebraicNumber) (f : DensePoly Rat) : QAdjoin a
instance (a : AlgebraicNumber) : Repr (QAdjoin a)
```

An element of `ℚ(a)` prints as `QAdjoin.ofCoeffs (a) f`, naming the generating
number -- which prints round-trippably itself -- instead of an isolating
square, and so leaves no `decide` side conditions to discharge when it is
pasted back. The presentation-ring instances are re-exported for the new head
symbol, each `inferInstanceAs` of the `PolyQuot` one. The type of a pasted
value is still only propositionally the original.

so `a.toQAdjoin : QAdjoin a` inverts and divides without any evidence
registered by hand. `QAdjoin a` abbreviates `PolyQuot a.p a.x` reducibly, so
every operation, instance and theorem on `PolyQuot` applies to it unchanged;
it exists so that the field of a canonical number is named by the number.
The computational API supplies `Inv` and `Div`, with `0⁻¹ = 0`; the companion
proves their field laws after converting the checked certificate to semantic
irreducibility.

```lean
def PolyQuot.approx (a : PolyQuot p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    RefinedIsolation p × DyadicComplexBall

theorem PolyQuot.approx_root (a : PolyQuot p x)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) (prec : Int) :
    SimpleRoot.mk (a.approx rep h prec).1 = x
```

Approximation refines once, returns the refined representative for threading,
and always returns a sound ball. The requested radius is guaranteed by the
companion's mixed-strategy refinement-completeness theorem. That proof uses
the selected atom's local simplicity and permits repeated roots elsewhere in
its ambient polynomial; it does not rely on a global squarefreeness premise.

For `n := a.coeffs.size`, evaluation uses target precision

```text
prec + 8 + ceilLog2(n + 1) + coeffBits(a.coeffs)
  + n * (rootBits(rep.square) + 3).
```

`coeffBits` bounds rational coefficient magnitudes by numerator bit length;
`rootBits` bounds the selected root using the current square's centre and
circumscribed-disc radius. The per-Horner-step `+3` covers both movement within
the certified refinement region and the dyadic `hi`/circumscribed-disc
overestimates. It is part of the soundness budget, not optional slack.

## Canonicalization and exactification

```lean
def AlgebraicNumber.toQAdjoin (a : AlgebraicNumber) : QAdjoin a
def AlgebraicNumber.toRoot (a : AlgebraicNumber) : AlgebraicRoot

def PolyQuot.toAlgebraicNumber? [ZPoly.CheckedIrreducible p]
    (a : PolyQuot p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option AlgebraicNumber
def PolyQuot.toAlgebraicNumber [ZPoly.CheckedIrreducible p]
    (a : PolyQuot p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : AlgebraicNumber

def QAdjoin.toAlgebraicNumber? {a : AlgebraicNumber} (c : QAdjoin a) :
    Option AlgebraicNumber
def QAdjoin.toAlgebraicNumber {a : AlgebraicNumber} (c : QAdjoin a) :
    AlgebraicNumber

/-- Checked implementation layer. -/
def AlgebraicRoot.exact? (a : AlgebraicRoot) : Option AlgebraicNumber
/-- Primary total API. -/
def AlgebraicRoot.exact (a : AlgebraicRoot) : AlgebraicNumber :=
  a.exact?.getD (panicWith 0 "AlgebraicRoot.exact: certification failed")

def AlgebraicRoot.ofEliminant? (raw : ZPoly)
    (ballAt : Int → Option DyadicComplexBall) : Option AlgebraicRoot
```

`AlgebraicRoot.ofEliminant?` returns `none` unless normalization, root
isolation, and the supplied operation ball identify one unique root.

`a.toQAdjoin` is the generator of `QAdjoin a`, and the argument-free
`QAdjoin.toAlgebraicNumber?` and `QAdjoin.toAlgebraicNumber` are the general
forms applied with the number's own representative `a.rep`.
`PolyQuot.toAlgebraicNumber?` materializes `1, a, a², ...` once with one
fixed-field multiplication per new power, finds the first Krylov dependence by
row reduction, clears denominators, normalizes the primitive part, and
identifies the matching isolated root.

`AlgebraicRoot.exact?` factors `a.p`, selects the unique irreducible factor whose
isolated root agrees with `a.rep`, and returns that factor in canonical form.
It reruns `ZPoly.isIrreducible` and the decidable `HasOnlySimpleRoots` check on
the normalized factor; successful branches carry the resulting equality and
squarefreeness proofs into the private `AlgebraicNumber` constructor.
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
- `inv? 0 = some 0`. Otherwise it reverses the coefficients of `a.p`, trims the
  degree drop caused by an original zero constant coefficient, takes the
  primitive positive-leading part, maps the isolation through inversion, and
  re-certifies it. The reversal has nonzero constant coefficient because it is
  the original leading coefficient, so it cannot acquire an `X` factor.
- `div?` composes multiplication and inversion.

The addition and multiplication eliminants are nonzero. Over an algebraic
closure their resultants are products of `t - (α + β)` or `t - αβ` over the
finite root multisets of the two nonzero input polynomials, so each has the
expected positive degree and nonzero leading coefficient. Stage 1 formalizes
the corresponding common-root statements; Stage 2 identifies the full product
when its value is needed.

For a binary eliminant `e`, the desired result may coincide with values from
other pairs of conjugates, but every candidate is a root of the same squarefree
polynomial. Define

```text
resultIsolationPrec(e) = separationDepth(e).
```

Refine the operation ball and candidate isolations to this precision. The
HexRoots separation theorem makes distinct candidates disjoint, so exactly one
candidate isolation meets the operation ball. This path does not need a second
eliminant or the Stage 2 resultant value theorem.

Candidate isolations use `resultIsolationPrec(e)` itself. The operand balls use
an additional, input-computable guard: four bits for addition,
`8 + rootBits(a) + rootBits(b)` for multiplication, and
`2 * ceilLog2(1 + coeffAbsMax(a.p)) + 16` for inversion. The multiplication
guard pays for operand-magnitude amplification. The reciprocal guard combines
the reciprocal Cauchy lower bound with the quadratic distortion of inversion
and dyadic rounding. The selected operation ball is two bits smaller than the
candidate separation precision for addition and four bits smaller for
multiplication and inversion.

Canonical `AlgebraicNumber` arithmetic converts inputs with `toRoot`, performs
the lazy operation, then calls `exact`. A many-input common-field routine is used
internally only for polynomials with canonical algebraic coefficients.
Canonical `AlgebraicNumber` exposes the ordinary arithmetic operations, with
`inv 0 = 0`; the Mathlib companion installs and proves the law-bearing field
structure. `AlgebraicRoot` exposes named operations but no field structure:
two semantically equal lazy results can have different enclosing polynomials,
so the field laws do not hold for structural equality on that record.

The executable rational and power surface is:

```lean
def AlgebraicNumber.ofRat (q : Rat) : AlgebraicNumber
instance : One AlgebraicNumber
instance : NatCast AlgebraicNumber
instance : IntCast AlgebraicNumber
instance (n : Nat) : OfNat AlgebraicNumber (n + 2)
instance : SMul Rat AlgebraicNumber
instance : SMul Nat AlgebraicNumber
instance : SMul Int AlgebraicNumber
instance : Pow AlgebraicNumber Nat
instance : Pow AlgebraicNumber Int
```

`ofRat` is the total wrapper around the checked linear-polynomial constructor;
its panic fallback is proved unreachable by the companion. Rational scalar
multiplication is multiplication by `ofRat q`, and powers use the existing
executable multiplication and inversion with repeated squaring.

## Polynomial roots

```lean
def PolyQuot.roots? [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Option RootSet
def PolyQuot.roots [ZPoly.CheckedIrreducible p] (...) : RootSet

def AlgebraicPoly.roots? (f : AlgebraicPoly) : Option RootSet
def AlgebraicPoly.roots  (f : AlgebraicPoly) : RootSet
```

The zero polynomial returns `some .all`; `none` is reserved for certification
failure. Finite output is normalized, duplicate-free, sorted by polynomial then
isolation coordinates, and carries positive multiplicities.

For `PolyQuot.roots?`:

1. Run Yun decomposition over the coefficient field. Process each squarefree
   component separately; a root from the component indexed by `e` receives
   multiplicity `e`.
2. Clear coefficient denominators and form the norm eliminant over `ℚ` by a
   resultant with `p`. It is nonzero because coefficients are reduced modulo the
   irreducible `p`.
3. Normalize and isolate the eliminant's roots.
4. For each component, build one shared integer evaluation eliminant
   `q(S) = Res_y(p(y), Res_z(e(z), S - G(y,z)))`, where `e` is the
   squarefree norm eliminant and `G` is the denominator-cleared component.
   Dilate `q` by the common denominator so its roots are the original
   component evaluations. The eliminant is nonzero and contains the true
   evaluation at every candidate. Reject candidates belonging only to other
   embeddings of `PolyQuot p x` by evaluating the original component at the
   candidate and the selected `x`; refute wrong candidates at
   `evalDisambiguationPrec`.
5. Return the surviving `AlgebraicRoot` values with the Yun multiplicity.

`AlgebraicPoly.roots?` first embeds all nonzero coefficients into one computed
primitive `PolyQuot`, then invokes the fixed-field algorithm. This common-field
construction is deterministic and bounded, is not used for binary arithmetic,
and is a public surface in its own right (the tower library builds on it); its
contract is the next section.

For each candidate, reuse the component's shared evaluation eliminant `q`,
remove its maximal `X` power, and take the primitive part. If the evaluation
is nonzero, `q(0) ≠ 0` and the reciprocal Cauchy bound gives
`|value| ≥ 1 / (1 + height(q))`. Let `C` be the explicit Horner error majorant
computed from the input coefficient heights, degrees, and Cauchy root bounds.
The generic cross-library recurrence is public:

```lean
def Disambiguation.evalMajorant {A : Type} [Zero A] [DecidableEq A]
    (f : DensePoly A) (valueBound : A → Nat) (q : ZPoly) : Nat
```

Define `evalDisambiguationPrec` as the least precision in the finite range

```text
0 .. ceilLog2(ceil(2 * (1 + height(q)) * C)) + 2
```

whose Horner enclosure radius is below `1 / (3 * (1 + height(q)))`.
The factor `3` accounts for the shipped zero-exclusion test using the maximum
absolute centre coordinate, which may be a factor `sqrt 2` below the Euclidean
centre norm. The displayed search endpoint still has sufficient slack.
The displayed endpoint proves that the bounded search succeeds. The same
construction, with the eliminant for each generator/factor evaluation, is used
by tower adjoining. No API performs unbounded refinement.

## Roots of integer polynomials

```lean
def AlgebraicRoot.ofRefined (q : ZPoly) (prim : ZPoly.content q = 1)
    (pos_lc : 0 < q.leadingCoeff) (pos_degree : 0 < q.natDegree)
    (squarefree : HasOnlySimpleRoots q) (rep : RefinedIsolation q) :
    AlgebraicRoot
def ZPoly.algebraicRoots? (p : ZPoly) : Option (Array AlgebraicNumber)
def ZPoly.algebraicRoots  (p : ZPoly) : Array AlgebraicNumber

def AlgebraicRoot.isReal (a : AlgebraicRoot) : Bool
def AlgebraicNumber.isReal (a : AlgebraicNumber) : Bool
def AlgebraicNumber.rootLe (a b : AlgebraicNumber) : Bool
def AlgebraicNumber.approx (a : AlgebraicNumber) (prec : Int := 64) :
    DyadicComplexBall
instance : Repr AlgebraicNumber
```

`algebraicRoots p` is every distinct complex root of `p` in canonical form.
It takes the squarefree primitive part of `p`, isolates all of its roots with
the fixed default strategy at `separationDepth`, builds one lazy
`AlgebraicRoot` per isolation with `AlgebraicRoot.ofRefined`, and exactifies
each. Multiplicities are not
returned; `AlgebraicPoly.roots` on the cast polynomial supplies them. A
constant, including zero, returns the empty array, and the correspondence
theorem is stated for nonzero `p`, matching `Polynomial.roots 0 = 0`. `none`
is reserved for certificate failure, and `algebraicRoots?_isSome` retires it.

The array is sorted by `AlgebraicNumber.rootLe`: real roots first by their
canonical dyadic centres, then nonreal conjugate pairs with the lower member
first. Pair keys are the canonical upper base's `(im, re, precision)`, followed
by the integer minimal-polynomial coefficient list to break ties between
factors. This keeps a pair together without exact coordinate extraction.
The companion proves the comparator is a total preorder, the output is
sorted by it, and no other canonical value lies between conjugate endpoints.
It is a deterministic centre order, not exact lexicographic `(abs im, re, im)`.
Use `ZPoly.realAlgebraicRoots` in the real library when exact value ordering
of real roots from different irreducible factors is required.

`meetsRealAxis` tests whether the closed circumscribed disc meets the real
axis, with the disc radius rounded up to the dyadic `radiusHi`: the centre's
imaginary part is at most `radiusHi` in absolute value. At separation
precision this is exact for a stored isolation: a real root lies in the
closed disc, so its centre is within the true radius, which is below
`radiusHi`, of the axis; a nonreal root and its conjugate are distinct roots
of the same integer polynomial, so `radiusHi` itself is less than a quarter
of their distance `2 |im z|` (the separation bound carries the `1449/1024`
slack), and the centre is more than `radiusHi` from the axis. `isReal`
reads the orientation tag established by this test; the companion proves `isReal_iff`.

`approx a prec` is `PolyQuot.approx` applied to `a.toQAdjoin` with the stored
representative; its ball contains `a.toComplex` and has radius at most
`2^(-prec)`. The `Repr` instance is described under `## The nearest root`.

## Exact primitives from stored isolations

```lean
def AlgebraicNumber.separationPrec (p : ZPoly) : Int
def AlgebraicNumber.I : AlgebraicNumber
def AlgebraicNumber.mirrorBall (b : DyadicComplexBall) : DyadicComplexBall
def AlgebraicNumber.realCompare (a b : AlgebraicNumber) : Ordering
```

`separationPrec p` is `mahlerPrec p + 2`. At that precision the approximation
balls of two distinct roots of `p` are disjoint: `mahlerPrec p` separates
distinct roots by more than four ball radii, and the two extra bits absorb the
centre errors. The reference comparison uses that fixed precision. Fast paths use bounded
refinement and certified coordinate intervals; none refines without bound.

`I` selects the upper root of `X² + 1`. Conjugation is the tag operation
specified with the canonical representation below; it uses no approximation
balls. `mirrorBall` remains a public geometric helper for compatibility and
for the retained search-strategy benchmark arm.

`realCompare a b`, for real `a` and `b`, is `.eq` when `a == b` and otherwise
first compares the stored real-coordinate intervals. Only overlap triggers
computation of the product-polynomial separation bound and geometric refinement,
threading the refined representatives. Targets double from the smaller stored
precision (clamped to one), capped at `separationPrec (a.p * b.p) + 1`.
Structural fuel bounds the search; failure or inconclusive final intervals use
the reference centre comparison at `separationPrec (a.p * b.p)`.
The companion proves every successful interval decision and the complete
operation agree with the order of the real parts. Canonical data is unchanged.

## The nearest root

```lean
def AlgebraicNumber.ofPoint (re im : Rat) : AlgebraicNumber
def AlgebraicNumber.distSqTo (a : AlgebraicNumber) (re im : Rat) : AlgebraicNumber
def AlgebraicNumber.ballDistSq (b : DyadicComplexBall) (re im : Rat) : Rat
def AlgebraicNumber.ballDistBound (b : DyadicComplexBall) (re im : Rat) : Rat
def AlgebraicNumber.ballUpper (b : DyadicComplexBall) (re im : Rat) : Rat
def AlgebraicNumber.ballLower (b : DyadicComplexBall) (re im : Rat) : Rat
def AlgebraicNumber.certifiedNearest (roots : Array AlgebraicNumber)
    (a : AlgebraicNumber) (prec : Int) (re im : Rat) : Bool
def AlgebraicNumber.exactNearest (roots : Array AlgebraicNumber) (re im : Rat) :
    Option AlgebraicNumber
def ZPoly.rootNear (p : ZPoly) (re : Rat) (im : Rat := 0) : AlgebraicNumber
instance : Repr AlgebraicNumber
```

`rootNear p re im` is the root of `p` nearest to the point `re + im·i`; among
roots at exactly the same distance it is the first in `algebraicRoots` order,
so for instance `rootNear #p[-2, 0, 1] 0` is `-√2` and, from a real point,
a conjugate pair resolves to the lower-imaginary member in enumeration order.
Scientific literals are rationals, so `rootNear #p[-2, 0, 1] 1.4` and
`rootNear #p[1, 0, 1] 0 0.9` read as written. A constant polynomial has no
roots and yields `0`. Like `algebraicRoots` it is irreducible, so that a type
mentioning it reduces cheaply when `#eval` looks for a printing instance.

The fast path uses the approximation balls at `separationPrec p`.
`ballUpper` bounds the squared distance from the point to every point of a
ball from above by `d + 2rl + r²`, where `d` is the squared distance to the
centre, `r` the radius and `l = |Δre| + |Δim|`, and `ballLower` bounds it
from below by `d − 2rl + r²` when `r² ≤ d`, else by `0`; neither takes a
square root. A root is `certifiedNearest` when its upper bound is below every
other root's lower bound, and the first such root is returned. When no root is
certified, because two are nearly or exactly equidistant, `exactNearest`
compares the exact squared distances `distSqTo`, each the real algebraic
number `(a − z)(ā − z̄)` built from `conj`, with `realCompare`, and keeps the
first minimum. No path refines without bound.

The `Repr` instance prints `ZPoly.rootNear p re` for a real number and
`ZPoly.rootNear p re im` otherwise, with the stored isolation centre
truncated toward zero to `digitsFor (mahlerPrec p)` decimals, chosen so that
`10^-digits ≤ 2^-mahlerPrec`. The centre is within `√2 · 2^-mahlerPrec` of
the root, so the printed point is within `(1 + √2) · 2^-mahlerPrec` of it,
less than half the root separation `mahlerPrec` guarantees, and the
companion's `rootNear_of_close` says the nearest root to it is the number
printed. The print is for display and carries no contract beyond that
theorem.

## Common-field construction

The `Hex.AlgebraicPoly.Common` namespace is the public bounded
primitive-element machinery behind `AlgebraicPoly.roots?`, consumed directly
by hex-number-field-tower (raw evaluation, flattening recovery) and its
Mathlib companion. Everything is option-valued and checked: a `none` records
a failed certification, never a wrong value.

```lean
structure Presentation where
  generator : AlgebraicNumber
  coefficients : Array (QAdjoin generator)

def signedShift : Nat → Int
def rational? (q : Rat) : Option AlgebraicNumber
def add? (a b : AlgebraicNumber) : Option AlgebraicNumber
def mul? (a b : AlgebraicNumber) : Option AlgebraicNumber
def scale? (c : Int) (a : AlgebraicNumber) : Option AlgebraicNumber
def shift? (theta alpha : AlgebraicNumber) (c : Int) : Option AlgebraicNumber
def degree (a : AlgebraicNumber) : Nat

structure ShiftCandidate where
  shift : Int
  value : AlgebraicNumber

def extendShiftStep (theta alpha : AlgebraicNumber) :
    Option ShiftCandidate → Nat → Option (Option ShiftCandidate)
def extendShift? (theta alpha : AlgebraicNumber) : Option ShiftCandidate
def extend? (theta alpha : AlgebraicNumber) : Option AlgebraicNumber
def primitive? (coefficients : Array AlgebraicNumber) : Option AlgebraicNumber
def powers? (gamma : AlgebraicNumber) (last : Nat) :
    Option (Array AlgebraicNumber)
def trace? (ambient : Nat) (a : AlgebraicNumber) : Option Rat
def coordinates? (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber) : Option (QAdjoin gamma)
def presentation? (coefficients : Array AlgebraicNumber) :
    Option Presentation
```

`signedShift` is the deterministic shift order `0, 1, -1, 2, -2, ...`.
`rational?`, `add?`, `mul?`, `scale?`, and `shift?` are the checked canonical
constructions the search composes: `shift? theta alpha c` is the
primitive-element candidate `theta + c * alpha`, with `c = 0` returning
`theta` unchanged.

`extend? theta alpha` is the bounded primitive-element search: it tests
`choose(degree theta * degree alpha, 2) + 1` signed shifts and keeps a
maximum-degree candidate, which generates the compositum even when the two
fields overlap. It is the value projection of `extendShift?`, so both APIs
share one search retaining the producing shift (the form the tower's
flattening recovery needs). `extendShiftStep` is `extendShift?`'s single fold
step, exposed so consumers can interleave the search with their own early
exits. `primitive?` folds `extend?` over the nonzero entries of a coefficient
array.

`powers? gamma last` returns the checked canonical powers
`1, gamma, ..., gamma^last`. `trace? ambient a` is the field trace of `a`
from a known ambient degree: with `m = degree a` it requires `m ∣ ambient`
and returns `(ambient / m)` times the conjugate sum
`-coeff (m-1) / leadingCoeff`. `coordinates? gamma a powers` recovers the
power-basis coordinate of `a` through the nondegenerate trace pairing (Gram
matrix of power traces against the traces of `a * gamma^k`), then validates
the recovered coordinate by canonical algebraic equality before returning it.
`presentation?` composes the above: find a primitive generator, take its
powers up to `2 * degree - 2`, embed every coefficient, and return the
validated fixed-field `Presentation`.

## Totalization

`panicWith fallback message` prints in compiled code and is definitionally the
fallback for proofs. Total algebraic operations use it only around checked forms
whose `_isSome` theorem is part of the companion contract. `exact`, arithmetic,
and both `roots` functions are the primary user APIs; the `?` forms remain public
for diagnostics and staged proofs.

`AlgebraicNumber` has canonical zero `p = X`, so it supplies the `Inhabited`
fallback used by exactification. `RootSet.all` is the loud fallback for the two
total root wrappers; their `_isSome` theorems make it unreachable.
`ZPoly.algebraicRoots` falls back to the empty array, and
`algebraicRoots?_isSome` makes that branch unreachable too.

## File organisation

```text
HexNumberField/
  Basic.lean          : core types, equality, zero, panicWith
  Approx.lean         : dyadic-ball evaluation and precision budgets
  PolyQuot.lean       : presentation-ring operations and threaded approximation
  Convert.lean        : canonicalization and exactification (`QAdjoin` lives here)
  Lazy.lean           : eliminants and lazy arithmetic
  Disambiguate.lean   : candidate bounds and certified selection
  AlgebraicPoly.lean  : semantic coefficient-polynomial representation
  Roots.lean          : fixed-field and algebraic-coefficient root APIs
  IntegerRoots.lean   : roots of integer polynomials, reality test, display
  Nearest.lean        : imaginary unit, conjugation, exact real order, nearest root, display
```

Conformance and benchmark drivers live in the shared `conformance/` and
`bench/` sub-projects.

## Conformance

- *core*: at least three cases per public operation, including `√2 + √2`,
  `√2 * √2`, `√2 + (-√2)`, inversion of zero, equal values represented by
  different nonminimal polynomials, an enclosing polynomial with irrelevant
  factors, repeated input roots, and a conjugate-embedding impostor; for
  `algebraicRoots`, `X² - 2` (order `-√2, √2`), `(X² - 2)² (X + 3)`
  (multiplicity dropped, `-3` first), `X³ - 2` (one real root first, then
  the conjugate pair), and the zero, constant, and `X` polynomials; for
  `isReal`, a real root, a nonreal root, and zero.
- *ci*: deterministic small-degree fixtures checked by cypari2. Use
  python-flint independently for integer resultants, factorization, and certified
  complex-root balls.
- *local*: degree-product stress cases and optional Nemo/Hecke comparisons.

Sage is not an oracle. Root comparisons use multiplicity buckets and compare the
oracle's independently computed decomposition with Lean's finite output.

## Complexity and Phase 4 budgets

All advertised `HexNumberField` operations are Mathlib-free executable
computations and therefore use the compiled Phase-4 evidence track; the
library owns no elaboration, tactic, emitted-proof, or kernel-checking surface.
Grouped constant-time accessors and total wrappers remain on that same track.
The performance report's
[current inventory](https://github.com/kim-em/hex-dev/blob/main/reports/hex-number-field-performance.md#track-assignment-re-audit)
records the measurements implementing this assignment.

- Fixed-field arithmetic has the existing dense-polynomial costs; a compiled
  degree-10 field operation remains capped at 100 ms on the reference host.
- Fixed-field inversion performs `O(n²)` rational coefficient operations.
  Monic remainder normalization keeps numerator and denominator widths within
  the `O(n log n)` subresultant/Hadamard bound, so inversion remains
  `O(n³ log n)` in the conservative linear-bit-cost model. The controlled
  bounded-height benchmark family exhibits linear coefficient widths across
  its registered schedule, giving a cubic aggregate linear-bit proxy; rounding
  coefficient components to machine limbs contributes a quadratic lower-order
  term. That expected-work registration does not weaken this worst-case
  contract.
- A lazy binary operation has eliminant degree at most
  `deg(a.p) * deg(b.p)`. Its ceiling is the measured resultant cost plus the
  existing HexRoots ceiling at that eliminant degree. Do not promise a faster
  end-to-end time than root isolation itself.
- Degree-product 20 is the largest studied merge-facing lazy arithmetic class,
  but the merge-gating end-to-end regression uses the degree-product-12 input
  below. The former sweep through 20 is retained as report evidence: its upper
  rungs are too slow for smoke verification, and no honest one-parameter model
  is available for them. Larger cases remain local until new measurements
  justify promotion.
- Isolation-dominated end-to-end regressions use canonical fixed inputs rather
  than an asymptotic claim. On the reference host, lazy addition of the selected
  roots of `X^6 - 2` and `X^2 - 3` must complete under 12 seconds; its
  square-free sum eliminant has degree 12,
  `coeffAbsMax = 1998`, coefficient bit height 11, and isolation target 186.
  `AlgebraicPoly.roots?` on the controlled dense degree-6 polynomial with one
  `√2` coefficient must complete under 15 seconds; its single square-free norm
  eliminant has degree 12,
  `coeffAbsMax = 366720`, coefficient bit height 19, and isolation target 274.
  `PolyQuot.roots?` on `g² * (X - 1)` over `ℚ(√2)`, with `g` the controlled
  dense degree-6 repeated component, must complete under 20 seconds; its
  square-free norm eliminant has degree 12, `coeffAbsMax = 45480960`,
  coefficient bit height 26, and isolation target 351.
  These project-internal canonical inputs come from the shared `n = 6` rung of
  the former schedules. Full timing runs check the ceilings; merge-gating
  smoke verification checks the result hashes. The measured reference timings
  live in the [performance report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-number-field-performance.md).
  None of the registrations makes a one-parameter scaling claim.
- Exactification adds one Berlekamp-Zassenhaus factorization and factor-root
  selection. Root APIs add Yun decomposition, one norm eliminant, and one
  shared double-resultant evaluation eliminant per squarefree component. The
  latter has degree at most the product of the defining-polynomial and norm-
  eliminant degrees and is not itself root-isolated.

Phase 4 records separate timings for eliminant construction, isolation,
disambiguation, and exactification so regressions are attributable.

The required exactification input families are:

- `exactification-selection`: the fixed enclosing polynomial
  `(X^8 - 2)(X + 3)`, with the chosen root pinned to `X^8 - 2`, records
  multiple-candidate selection and canonical re-isolation without treating
  the easy enclosing factorization as scaling evidence;
- `exactification-certification`: fixed degree-eight certification cases use
  `X^8 - 2` inside `(X^8 - 2)(X + 3)`, pinned to the nonlinear factor, to time
  `AlgebraicRoot.exactFactor?`, and the same candidate in the public
  `AlgebraicNumber.canonicalRep?` phase. The enclosing polynomial has degree 9,
  `coeffAbsMax = 6`, coefficient bit height 3, and certificate precision 77;
  the candidate has degree 8, `coeffAbsMax = 2`, coefficient bit height 2, and
  certificate precision 53. Their zero-grace whole-child budgets are 2 seconds
  and 1.1 seconds respectively; and
- `exactification-factorization`: the fixed end-to-end `exact?` case is the
  first root of `∏ p∈{2,3,5,7,11,13}, (X² - p)`, the top completed rung of
  the archived growing-factor-count sweep. It has degree 12,
  `coeffAbsMax = 40361`, coefficient bit height 16, and certificate precision
  241. Its zero-grace whole-child budget is 200 ms, including a 20 ms timed
  batch after one untimed warmup.

The certification and factorization sweeps are archived diagnostic evidence,
not current parametric registrations. Inclusive profiling attributes the
certification cases to root isolation (more than 95% inclusive) and the
end-to-end case primarily to isolation (about 77%), with factorization only
about 18%. The published BHKS bound therefore does not cover the controlling
end-to-end phase, while the published BSSY bound concerns a different
isolation algorithm. These three registrations are fixed absolute-budget
checks and make no one-parameter scaling claim. Their static certificates are
checked against the archived family shapes in the benchmark source; full
timing runs enforce the budgets and merge-gating verification checks both the
output polynomial and canonical isolating square.

## External comparators

**PARI/GP via cypari2** (https://pari.math.u-bordeaux.fr/, driven through
the cypari2 binding, the same binding the conformance oracles use) —
**informational**, scoped to the fixed-field arithmetic bench targets.
PARI's t_POLMOD arithmetic (`Mod(a, m) * Mod(b, m)` and `Mod(a, m)^(-1)`)
is the callable unit surface computing exactly `PolyQuot` multiplication and
extended-gcd inversion in `ℚ[x]/(m)`. It is wired as a persistent-subprocess
process call (`scripts/oracle/pari_bench_driver.py`,
`Hex/BenchOracle/Pari.lean`) with per-rung fixed Lean/PARI registration
pairs on identical deterministic inputs, joined on the identical reduced
rational coefficient hash. PARI is a mature optimized C library, so the
constant-factor gap is structural rather than algorithmic; the ratio is
recorded for orientation and does not gate Phase 4.

Absence declarations, all with reason
**no-comparable-surface-in-named-comparator**:

- *Factorization-lazy and canonical arithmetic* (`AlgebraicRoot.add?` and
  friends, `AlgebraicNumber` arithmetic): PARI has no certified lazy
  algebraic-number type; its floating `t_COMPLEX`/`algdep` workflow does not
  expose "combine two isolated algebraic numbers into a certified isolated
  result" as a callable unit.
- *Exactification* (`AlgebraicRoot.exact?`): PARI exposes rational
  polynomial factorization (already the BZ dependency's comparator surface)
  but no unit function selecting and certifying the minimal polynomial of a
  root given an isolating region.
- *Root APIs* (`PolyQuot.roots?`, `AlgebraicPoly.roots?`): PARI's
  `nfroots`/`nffactor` return only the roots lying inside the number field,
  and `polroots` returns uncertified floating approximations; no PARI unit
  surface produces the certified complete complex root multiset with
  isolation data that these APIs return.

## References

- Cohen, H. *A Course in Computational Algebraic Number Theory.* Springer,
  1993, sections 4.1, 4.2, and 4.5.
- Belabas, K. *Topics in computational algebraic number theory.* J. Théorie
  des Nombres de Bordeaux 16 (2004), 19-63.
- Bostan, A.; Flajolet, P.; Salvy, B.; Schost, É. *Fast computation of
  special resultants.* JSC 41 (2006), 1-29.

## Complex operations and common fields

```lean
inductive AlgebraicNumber.RootSide where
  | real | upper | lower
  deriving DecidableEq, BEq

structure AlgebraicNumber.OrientedIsolation (p : ZPoly) where
  base : RefinedIsolation p
  side : AlgebraicNumber.RootSide
  valid : match side with
    | .real => base.1.square.meetsRealAxis = true
    | .upper | .lower => base.1.square.radiusHi < base.1.square.im

def AlgebraicNumber.OrientedIsolation.rep {p : ZPoly}
    (r : AlgebraicNumber.OrientedIsolation p) : RefinedIsolation p
def AlgebraicNumber.OrientedIsolation.conj {p : ZPoly}
    (r : AlgebraicNumber.OrientedIsolation p) : AlgebraicNumber.OrientedIsolation p
def AlgebraicNumber.sideOf {p : ZPoly} (r : RefinedIsolation p) : AlgebraicNumber.RootSide
def AlgebraicNumber.orient? {p : ZPoly} (base : RefinedIsolation p)
    (side : AlgebraicNumber.RootSide) : Option (AlgebraicNumber.OrientedIsolation p)
def AlgebraicNumber.rawRep? (p : ZPoly) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) (hzero : p ≠ ZPoly.X) :
    Option {r : RefinedIsolation p //
      AlgebraicNumber.IsCanonical p squarefree r ∧ r.sameRoot rep = true}
def AlgebraicNumber.isolation (a : AlgebraicNumber) : AlgebraicNumber.OrientedIsolation a.p
def AlgebraicNumber.side (a : AlgebraicNumber) : AlgebraicNumber.RootSide
def AlgebraicNumber.conj (a : AlgebraicNumber) : AlgebraicNumber

def PolyQuot.ofIsolation {p : ZPoly} (r : RefinedIsolation p) (f : DensePoly Rat) :
    PolyQuot p (SimpleRoot.mk r)

def AlgebraicNumber.partialCompare (a b : AlgebraicNumber) : Option Ordering
instance : LT AlgebraicNumber
instance : LE AlgebraicNumber
instance (a b : AlgebraicNumber) : Decidable (a < b)
instance (a b : AlgebraicNumber) : Decidable (a ≤ b)
def AlgebraicNumber.nthRoot (a : AlgebraicNumber) (n : Nat) : AlgebraicNumber
def AlgebraicNumber.sqrt (a : AlgebraicNumber) : AlgebraicNumber

namespace AlgebraicNumber.Radical
structure Candidate where
  value : AlgebraicNumber
  twiceRe : AlgebraicNumber
  correct : twiceRe = value + value.conj
def rank (a : AlgebraicNumber) : Int
def candidate (r : RootCount) : Candidate
def choose (a b : Candidate) : Candidate
def select (roots : Array RootCount) : Option Candidate
def polynomial (a : AlgebraicNumber) (n : Nat) : AlgebraicPoly
end AlgebraicNumber.Radical

namespace QAdjoin
def powerTable (a : AlgebraicNumber) : Array AlgebraicNumber
def ofAlgebraic? (a b : AlgebraicNumber) : Option (QAdjoin a)
def ofAlgebraics? (a : AlgebraicNumber) (bs : Array AlgebraicNumber) :
    Array (Option (QAdjoin a))
structure Presentation where
  generator : AlgebraicNumber
  entries : Array (QAdjoin generator)
def common (bs : Array AlgebraicNumber) : Presentation
end QAdjoin
```


`AlgebraicNumber.partialCompare : AlgebraicNumber → AlgebraicNumber → Option Ordering`
returns `none` exactly for unequal imaginary parts. Global executable `LT`,
`LE` and their decisions match Mathlib's complex partial order: equal imaginary
parts and ordered real parts. Structural equality and real-real comparisons
are direct paths; differing orientation tags reject immediately; remaining
cases first reject disjoint imaginary-coordinate intervals. Unresolved cases
try 16 and 64 additional bits relative to each stored precision, then test
whether the exact difference is real and use `realCompare`. The `<` and `≤`
decisions also reject impossible real-coordinate inequalities before asking
whether imaginary parts are equal: `a.lower ≥ b.upper` rejects `<`, and
`a.lower > b.upper` rejects `≤`. Inconclusive interval tests are distinct from
incomparability; overlap never establishes equality. The exact fallback
path performs an exact subtraction, including resultant construction,
factorization and root isolation; it can cost as much as field arithmetic. There is no
`Ord` or `LinearOrder` instance on the complex type. The companion supplies
`PartialOrder`, `IsStrictOrderedRing`, `StarRing`, `conjRingEquiv` and an order
embedding into the scoped complex order.

`AlgebraicNumber.nthRoot a n` agrees with `a.toComplex ^ ((n : ℂ)⁻¹)`;
`sqrt a` is `nthRoot a 2`. Index zero returns one; positive indices at zero
return zero. The general path still solves `X^n - a`, but branch selection
works on lazy roots. Positive real inputs retain real candidates; negative real
inputs retain upper candidates; nonreal inputs retain their own imaginary side.
Among retained candidates, certified real intervals select the maximum. Stored
intervals precede two refinement rounds at 16 and 64 additional bits, with
representatives threaded and cached. Only the winner is canonicalized on this
path. Inconclusive selection uses the existing exact selector, which caches
each candidate's doubled real part and prefers the upper side on a tie.
Square roots usually have one candidate after the side test; positive real
inputs select the positive real root. The real square-root API shares this path. Root completeness proves selection succeeds, and the
companion proves the result lies in the principal argument sector
`(-π/n, π/n]`. General radicals can be expensive. Conjugation commutes with
this branch away from the negative real axis, not unconditionally.

`QAdjoin.ofAlgebraic? a b` returns coordinates exactly when `b ∈ ℚ(a)`.
`ofAlgebraics? a bs` shares the power table and preserves one option per input.
`QAdjoin.common bs` returns a `Presentation` with one `generator` and an
`entries : Array (QAdjoin generator)`, preserving input values, order and
duplicates. Empty and all-zero inputs use generator zero. These wrappers
reuse the existing certified primitive-element search and coordinate recovery;
no independent field-search implementation is added.

The real library owns `AlgebraicNumber.re`, `im`, and `ofReal`, with both
projections returning `RealAlgebraicNumber`. It computes them through
conjugation and exact arithmetic, with direct paths for real values. Keeping
the projections there avoids a dependency from number fields to their real
subtype. The companion proves projection arithmetic and reconstruction.

The number-field companion provides `IsAlgClosed AlgebraicNumber` and
`IsAlgClosure ℚ AlgebraicNumber`, using the complete algebraic-coefficient
root solver and algebraicity of every represented value. Neither instance
introduces new axioms or admits unfinished proofs.

## Roots of unity and complex norms

```lean
def AlgebraicNumber.rootOfUnity (q : Rat) : AlgebraicNumber
-- Owned by hex-real-algebraic:
def AlgebraicNumber.normSq (a : AlgebraicNumber) : RealAlgebraicNumber
def AlgebraicNumber.abs (a : AlgebraicNumber) : RealAlgebraicNumber
```

`rootOfUnity q` denotes `exp (2 * π * I * q)` and has exact order `q.den`.
Reduce the numerator modulo the positive denominator. Denominators 1, 2, and 4
use constants. For other denominators `n`, isolate `X^n - 1` when `n` is odd,
or `X^(n/2) + 1` when even. The upper root with greatest real part is
`exp (2πI/n)`; select it lazily, then compute the requested power in its
`QAdjoin`, converting once. Generator and conjugate cases reuse existing values.
No generic algebraic-coefficient solver or integer-index factorization is used.
The polynomial degree is still linear in the denominator; the cyclotomic route
and general recognition are specified in the
[direct radical design](hex-number-field.md#cyclotomic-construction-and-coprime-powers).
Radicals of `-1`, `I`, and `-I` use their principal rational angles divided by
the positive index. No representation metadata or global cache is added.

`normSq` packs `a * a.conj` as a real value. `abs` uses its nonnegative square
root, with the existing real absolute value for real inputs. The companion
proves the norm correspondences, nonnegativity, zero characterization,
conjugation invariance, multiplicativity, and `abs² = normSq`. These are named
real-valued functions, not an `Abs AlgebraicNumber` instance.

Conformance includes separated and touching intervals, close cross-factor and
Mignotte pairs, same-imaginary nonreal pairs, unequal imaginary coordinates,
forced fallback, branch-cut radicals, rational-angle periodicity and orders,
and complex norm identities. FLINT qqbar supplies exact expected values.
Benchmarks separate construction, selection, and complete extraction, retaining
eight adjacent AB/BA blocks under the shared-host measurement policy.

The [interval and radical measurements](../../bench-results/algebraic-fast-paths/README.md)
separate preconstructed comparisons, lazy branch selection, and complete
extraction. They include the same-imaginary fallback overhead as well as
successful fast paths; every completed AB/BA block is retained.

## Direct certified radicals and cyclotomic embeddings

This is the required replacement design for principal radicals in
[hex-number-field](hex-number-field.md), with proof ownership in the
[companion SPEC](../../HexNumberFieldMathlib/SPEC/hex-number-field-mathlib.md#direct-radical-proof-obligations).
It specifies future executable code, not shipped declarations. The existing
`Radical.polynomial`/`AlgebraicPoly.roots` route remains the reference until
this design's end-to-end proofs and evidence are complete. Comparison work in
[#10142](https://github.com/kim-em/hex-dev/issues/10142) is separate.

### Contracts and route ownership

For `a : AlgebraicNumber` and `n : Nat`, retain
`(a.nthRoot n).toComplex = a.toComplex ^ ((n : ℂ)⁻¹)` and
`a.sqrt.toComplex = Complex.sqrt a.toComplex`. Test conventions in this order:
index zero returns one, including `0.nthRoot 0`; index one returns the input;
zero at a positive index returns zero; one returns one. For nonzero input and
positive index the argument is in `(-π/n, π/n]`. Negative real inputs use
argument `+π`: the principal cube root of `-8` is `1 + √3 I`, not `-2`.
Conjugation commutes only away from the negative real axis (and in the
appropriate trivial cases); no unconditional commuting law is introduced.

The complete general route is integer substitution, certified principal
approximation, one factorization, certification of one embedding, and local
canonicalization. It must not call common-field discovery, norm or evaluation
eliminants, `AlgebraicPoly.roots`, or exactify a list of candidates. Integer
factorization remains necessary when the substituted polynomial is reducible.
All routes below finish through the same canonical constructor. Improving
approximation alone does not discharge this design.

### Direct annihilator and retained work

Let `p = a.p`, `d = p.natDegree`, `H = max 1 (coeffAbsMax p)`, and
`h = ceilLog2 (H + 1)`. For `a ≠ 0` and `n > 1`, spread coefficient `p[i]`
to position `n*i`, filling other entries with zero:

```
P = p.substPow n = p(X^n),    D = n*d,    height(P) = H.
```

Use the dense `substPow` prerequisite in the
[cyclotomic SPEC](../../SPEC/Libraries/hex-cyclotomic.md#prerequisite-changes-in-other-libraries).
Do not implement this spread as repeated dense composition. A sparse view may
skip zeros during evaluation, but factorization adapters must account for the
full dense allocation. The proof is `P(β) = p(β^n) = p(a) = 0` for the
principal root `β`. Primitive content and positive leading coefficient are
preserved. `p(0) ≠ 0`, separability of `p`, and
`P' = n X^(n-1) p'(X^n)` imply that `P` is squarefree in characteristic zero.
The nonzero-input hypothesis is essential; never apply this argument to `X`.

Factor `P` once into primitive positive-leading irreducibles, keeping the
product equality, multiplicities, and per-factor irreducibility evidence.
Since `P` is squarefree the multiplicities are one. Use the existing bounded
factorizer, including `factorTrial` with `defaultFactorCoeffBound` as its
unconditional fallback. An independent conservative candidate bound is
`B = 2^D*(D+1)*H`: enumerate coefficients in `[-B,B]` for degrees at most
`D`, testing exact division, and recurse on strictly smaller degrees. At most
`D²*(2*B+1)^(D+1)` candidate tests bound such a fallback. This is a totality
bound, not the intended fast factorization strategy; retain the production
factorizer's bounded modular, lifting and recombination work as well. This factorization can be
scheduled after approximation, but no losing factor's algebraic roots are
constructed. Keep the substituted polynomial, separation bound, factor list,
selected factor, selected enclosure, Taylor workspace, and certificates in a
request-local work record. Clear losing workspaces as they are consumed. A
batch of embeddings may share immutable polynomials and factor evidence;
there is no global mutable cache and no cache data in structural equality.

### Computable precision and enclosure algorithm

All searches below use explicit natural-number budgets, not convergence as an
unbounded loop. Conservative bounds establish totality; measured strategies
may stop much earlier. A bound may be large without being a performance claim.

A Cauchy bound and its reciprocal give rational numbers

```
R = 1 + max_{i<d} |p[i]/p[d]|,
ρ = 1 / (1 + max_{1≤i≤d} |p[i]/p[0]|),
0 < ρ ≤ |a| ≤ R.
```

For any squarefree nonconstant integer `f` use
`δ(f) = 2^(-mahlerPrec f)` as a deliberately smaller strict lower bound for
distinct-root distance; degree one uses this number without a pair obligation.
This follows from the existing `mahlerPrec_separates`, not from an empirical
root gap. Nonreal roots have `|im| > δ(f)/2`, by comparison with their
conjugates. Thus side recognition needs no unknown distance to the cut.

To enclose `β` to radius `2^-k`, use rational outward arithmetic throughout:

1. Refine the input to radius at most `2^-b`, where
   `b = k + ceilLog2(ceil C) + 16` and
   `C = 256*(1+R)^2*(1+1/ρ)^2`. Retain the exact real/upper/lower tag;
   a ball crossing the cut never changes that tag. Input refinement uses
   `RefinedIsolation.refineTo?` with its existing input-computable depth/fuel.
2. Enclose `r = |a|` by rational bisection of `x²+y²`, intersecting the
   squared-modulus bounds with `[ρ²,R²]` and the result with `[ρ,R]`.
   Enclose the nonnegative real `t = r^(1/n)` by bisection on `[0,max 1 R]` using exact
   comparisons of rational `n`th powers. Bisect at most
   `ceilLog2(ceil(max 1 R)) + b + 4` times for absolute endpoint width
   `2^(-b-4)`. Bound uncertainty in `r` using the same `ρ` lower bound;
   interval root endpoints are each computed with that budget.
3. Enclose the argument on the tagged branch. On the positive real axis it
   is exactly zero; on the negative real axis use a certified interval for
   `+π`. For nonreal input intersect the coordinate enclosure with its known
   closed half plane. Use an `atan2` chart with a denominator certified in
   absolute value at least `ρ/4`; one coordinate always supplies such a
   chart after the stated refinement. When the imaginary coordinate is the
   denominator the formula is `sgn(y)*π/2 - atan(x/y)`. When the real
   coordinate is the denominator use `atan(y/x)` and the known half-plane
   tag to add `+π` or `-π` if `x < 0`. This remains valid arbitrarily close
   to the cut; real negative inputs never go through a two-sided chart.
4. Evaluate rational endpoint bounds for `atan` monotonically. Reciprocal
   reduction brings the endpoint into `[-1,1]`; the identity
   `atan u = 2*atan(u/(1+sqrt(1+u²)))` brings its magnitude below `1/2`.
   Rational square-root bisection with outward bounds supplies the argument.
   The alternating series remainder is at most
   `|v|^(2N+1)/(2N+1)`; choose `N = b+16`. Compute `π` using
   `16*atan(1/5)-4*atan(1/239)` with the same certified remainders.
5. Divide the angle interval by positive `n`; enclose sine and cosine by
   their Taylor polynomials with rational interval remainders. For arguments
   bounded by `4`, using `16*(b+16)` terms is a conservative explicit
   factorial-tail budget. Multiply these intervals by the interval for `t`
   and round outwards to a dyadic enclosure of radius at most `2^-k`.
   Internal rounding is allocated a fixed fraction of the final error.

The companion must prove the stated error budget (including chart changes,
endpoint arithmetic, rounding and remainders), and encode integer ceilings
without floating-point logarithms. In particular `C` bounds the radial and
angular error amplification on each tagged half plane with `|z| ≥ ρ/2`;
there is no claim of continuity across the cut. Increasing precision doubles
bits up to the explicit `b` cap, then runs that final precision once.
At most eight approximate Newton iterations may seed this algorithm; only
checked enclosures are accepted. They cannot replace these guarantees or
supply a branch certificate by a residual alone.

#### Square-root specialization

Avoid trigonometry for `n = 2`. Enclose `r = sqrt(x²+y²)` and use a stable
component formula. When `r+x ≥ ρ/2` is certified, compute
`u = sqrt((r+x)/2)`, `v = y/(2u)`. Otherwise certify `r-x ≥ ρ/2`, compute
`|v| = sqrt((r-x)/2)`, choose its sign from the input side (positive on the
negative real axis), and set `u = |y|/(2|v|)`. The real positive and negative
axis cases use `sqrt(|x|)` directly. Overlapping applicability is harmless:
both formulas denote the same principal root. After the input refinement
above at least one safe denominator is certified; there is no equality test
on a vanishing approximate component and no division by zero. The same `C`
and bisection budgets suffice, with the formula identity and nonnegative-real
branch as separate soundness lemmas. Certification and canonicalization below
are still required.

### One embedding and one factor

Take `m(P) = mahlerPrec P + ceilLog2(max 2 D) + 16`,
`s = 2^(-m(P))`, and approximate `β` to error at most `s/256`. Round the centre
to the grid of spacing `s/64`. Run the existing exact three-radius,
linear-term Pellet checker on the square of half-width `s` at that centre.
The new quantitative completeness lemma must show this succeeds: the centre
is within `s/32` of a simple root and every other root is more than `δ(P)`
away. Taylor coefficients divided by the derivative are bounded by the
coefficients of `(1+T/(δ(P)-s/32))^(D-1)`; the slack of 16 accommodates
three radii, the `lo`/`hi` modulus bounds, and centre error. This supplies a
`RefinedIsolation P` and identifies its root with the enclosed principal root.
A root count without this overlap/separation argument would not identify the
input embedding.

Test the retained irreducible factors at the same centre and half-width,
reusing the approximation and exact shift workspace. The unique factor
vanishing at `β` passes the same one-root test since its roots are a subset
of those of `P`; any passing factor in this disc must be that factor. At most
`D` tests suffice. No factor's root list is generated. Carry the division and
irreducibility certificate into the final constructor, transport the selected
root to that factor, then run local canonicalization. The selected enclosure
has more than the factor's needed separation geometrically; if its formal
`RefinedIsolation` precision threshold is larger, refine just this root to
that threshold using the factor's computed depth. A proof must connect this
transport with `SimpleRoot`, not merely compare untyped overlapping balls.

### Local canonicalization and representation migration

The current `IsCanonical` literally means membership in the output of
`isolateComplexRoots?` at `separationDepth`. It cannot justify inserting the
enclosure above. Replace that predicate and the constructor together with the
following deterministic normal form for each normalized irreducible `f`.

Set `m(f) = mahlerPrec f + ceilLog2(max 2 (degree f)) + 16`,
`s = 2^(-m(f))`, and lattice spacing `g = s/64`. Consider all squares of
half-width `s` centred at `(j*g,k*g)`, for integers `j,k`, whose **exact**
three-radius linear Pellet checker passes and whose certified root is the
chosen real or upper root. The canonical square is the lexicographically
least pair `(j,k)` in this set. The set is finite: any such centre is within
`radiusHi < 2s` of the root. It is nonempty: rounding the root to this fine
grid gives the quantitative Pellet success above. Lexicographic minimum is
therefore well-defined even though the whole integer lattice has no minimum.

The executable constructor finds it locally. Reflect a lower root to the
upper half plane, refine that one root to error `≤ s/256`, and enumerate
lattice centres in the rational bounding box of coordinate radius `3s` about
its approximate centre. This has fewer than `400²` centres independent of
degree, height, or root magnitude. For each centre run the fixed exact checker
and retain successes. Every successful disc in this box contains the same
root: its root is within `6s` of the target, less than `δ(f)`. Every successful
disc containing the target has its centre in this box. Hence the minimum is
independent of the input enclosure, its precision, strategy, or enumeration
order. Points on grid lines or failed strict-checker boundaries require no
special equality decision; nearby overlapping squares supply a success.

Only the real or upper base is normalized. A nonreal base is wholly above the
axis by the conjugate separation bound; a real base meets the axis. Preserve
`OrientedIsolation`, the real/upper/lower tag, zero's distinguished base,
constant-time conjugation, and reflected `AtomCertificate.conj` transport.
The fixed checker and square determine the canonical certificate data; do not
store a caller's successful soft/NK/reflection trace as the canonical base.
Proof fields are irrelevant, but data-bearing certificate constructors are
not. Canonical provenance now records least successful local-grid square,
with completeness of the local enumeration, instead of an all-roots array.

Keep `rep`, `x`, `rep_mk`, approximation, and `QAdjoin a` semantic contracts.
Reprove `toComplex` injectivity, extensionality, `LawfulBEq`/`DecidableEq`, and
root identity for the new normal form. All constructors must migrate together:
constants, rational construction, `AlgebraicRoot.exact`, integer roots,
`PolyQuot` conversion, radicals, and unity. All-roots callers already holding
a list reuse each selected isolation; none re-isolates a polynomial per root.
The current centre-based `rootKey` and its injectivity/adjacency proofs must
be updated; root enumeration indices and nearest-root ties may change.
Mathematical partial order, structural equality of equal values within the
new version, and the represented values must not change. Byte-identical old
hidden records and old enumeration indices are not promised.

`Repr` emits a checked constructor for normalized polynomial, canonical grid
square, side, and canonical evidence, or re-normalizes a checked supplied
isolation. Never use an unchecked arbitrary enclosure or an old root index
as provenance. Keep `PolyQuot.ofIsolation` for reflected raw roots. Old printed
isolation expressions still denote their old root and normalize into the new
form; decoding old cached canonical records requires validation and migration.
Tests must elaborate generated expressions and compare the resulting values
structurally, including lower roots and double conjugation.

#### Reusing irreducibility evidence

`ZPoly.CheckedIrreducible` currently stores `isIrreducible p = true`, whose
runtime producer factorizes `p`. Introduce a Mathlib-free evidence predicate in `Prop` with
three checked constructors: the existing Boolean check; membership in a
retained certified factorization output (membership in the actual
`factorize` result, not merely a list with the correct product); and equality
with `cyclotomic F`
for positive checked index `F`. Each requires positive polynomial degree.
Replace the class's Boolean field with this evidence, retaining the class name
and an adapter for old Boolean callers. The Boolean equality becomes a
companion consequence, not a field all executable producers must compute.
Audit every projection and constructor use across the library graph.
Runtime work records hold the polynomial and factor data; the class stores
only proof evidence, which is never eliminated into executable data.
The companion proves each evidence constructor implies rational
irreducibility; computational code does not import that companion.
Do not simply assert that a modular irreducibility test will succeed on every
irreducible polynomial. The selected factor and cyclotomic routes must not
re-factorize to manufacture an obsolete evidence field.

### Specialized inputs and dispatch

All candidate optimizations return a checked result or an explicit miss.
Dispatch order is conventions/constants, a supplied unity witness, rational
and square-root specializations, then direct `p(X^n)`. Recognition of unity
without supplied evidence is optional within a fixed budget; exhaustive
recognition is a separate API. Composite-index planning is optional and must
have a bounded plan and a measured advantage over one substitution.

#### Rational and binomial radicals

Detect a rational input from its degree-one minimal polynomial. For reduced
`u/v` with `v > 0`, directly build `v*X^n-u`. Test perfect powers of `|u|` and
`v` using integer root bisection plus exact powering, not integer prime
factorization. Each search is bounded by operand bit length, with
`O(log n)` multiplications per power comparison. If both are exact `n`th
powers, a nonnegative rational input yields its rational root; a negative
input yields the positive magnitude times `rootOfUnity (1/(2*n))`, with the
axis branch retained even for odd indices.

For partial powers, enumerate divisors `e` of `n` by trial division up to `n`
(or use a supplied checked factorization), testing exact `e`th powers of both
operands. If `|a| = c^e`, `c > 0`, and `n = e*m`, use the smaller binomial
`X^m-c` for the positive magnitude. For negative `a`, retain angle `π/n`;
never take a principal root of an arbitrary chosen negative `e`th root.
Rational scaling or multiplication by the required unity value may itself
require exactification; charge it explicitly. The unsplit binomial is always
a complete finite fallback, and may be cheaper.

A binomial is not presumed irreducible. Factor the reduced annihilator by the
existing complete integer factorization and certify the selected factor as
above, including cases such as `X^4-4` and `X^4+4`. No appeal to an incomplete
perfect-power criterion replaces factorization. General inputs represented by
a binomial minimal polynomial may combine exponents directly, but still need
the input embedding in the principal enclosure. For `n = r*s`, `r,s > 0`,
principal extraction obeys `(a.nthRoot r).nthRoot s = a.nthRoot (r*s)`:
prove this via argument division and magnitude, not unrestricted `cpow_mul`.
Bound any decomposition search by the finite divisor list of `n`. Estimate
all intermediate degrees, heights, factorization and canonicalization costs;
repeated canonicalization can erase the benefit. Rational perfect powers,
reduced binomials, and composite plans each require route-agreement theorems
and the same final canonical form, including their intermediate values.

#### Cyclotomic construction and coprime powers

Use [hex-cyclotomic](../../SPEC/Libraries/hex-cyclotomic.md), whose public
constructor consumes `CheckedFactorization N` and computes `Φ_N` by a prime
ladder and final exponent spread. It is specified but not implemented in this
checkout. Do not invent a second cyclotomic polynomial generator here.
A checked index is positive; index zero is rejected by the checked entry point
and does not inherit Mathlib's polynomial convention `Φ₀ = 1`.

For rational `q`, reduce to numerator `k` modulo denominator `N = q.den`.
Then `gcd(k,N)=1` (including the order-one case). Reduce the turn to
`(-1/2,1/2]` for trigonometric evaluation, so the angle has absolute value
at most `π < 4`. Enclose `exp(2πi*k/N)` using the bounded rational-angle
sine/cosine algorithm above, certify it as one root of `Φ_N`, and canonicalize locally. The cyclotomic
irreducibility evidence directly supplies the minimal polynomial. No
`QAdjoin` power conversion or Krylov minimal-polynomial computation is needed.
The exported `rootOfUnity q` remains this constructor's rational-angle front
end, with the same exponential value, periodicity, addition and order laws.
Constants of orders 1, 2, 4 remain direct paths.

To power a certified primitive `N`th root, retain its reduced angle and exact
order in a **separate witness**, not in the canonical number. A checked index
factorization is optional acceleration data in that witness. For a coprime
power `j`, replace the angle by `j*k/N`, share `Φ_N` and its irreducibility
evidence, and certify only the new embedding. For a noncoprime power reduce
to order `M = N/gcd(j,N)`. If a checked factorization is available, project
it to `M` and build `Φ_M`; otherwise use the total construction below.
Do not claim the old polynomial is still minimal. Exponent zero gives
one. The companion proves both the same-minimal-polynomial coprime theorem
and the general order formula.

For radicals of a unity value, first put its turn into `(-1/2,1/2]`, then
divide by positive `n`, reduce the fraction, and construct that embedding.
In particular `I.nthRoot 4 = rootOfUnity (1/16)`. A residue in `[0,1)` must
not be divided before moving a lower-half-plane input to its principal turn.

If no checked index is supplied, attempt the existing integer-factor search
with its input-computable `defaultFuel N` budget and a fixed deterministic
random seed. It is a partial search: `Hex.Nat.factor?` has no totality theorem, and `PrimeCert.small`
only accepts stored table entries. A successful search supplies the checked
input to cyclotomic construction. On exhaustion, construct `X^N-1` directly,
enclose the requested rational-angle embedding, and run the one-factor
certification and local canonicalization pipeline above with degree `N` and
height one. Its squarefreeness follows from `N > 0`. This is a complete
integer-polynomial fallback, with the same computed separation, factorization,
and certification bounds; it uses no common field or algebraic-coefficient
solver. The selected factor is `Φ_N` for a reduced turn, by its semantic
primitive order. A budgeted cyclotomic-only entry point instead reports index
factorization exhaustion. Neither entry point invents prime certificates or
interprets exhaustion as non-unity. Measure the potentially large degree-`N`
fallback and index-factor search separately; checked-index callers bypass it.

#### Exact recognition

`unityOrder? a` is a total decision returning the exact order or `none` for a
non-root-of-unity. Reject zero and nonmonic minimal polynomials. For the
remaining monic `p = a.p`, compute `R₀ = 1` and
`R_(j+1) = (X*R_j) mod p` using exact integer monic division. Search
`1 ≤ j ≤ 2*d²` for the first `R_j = 1`. Retain only the current remainder,
whose degree is less than `d`; never construct canonical powers of `a`.
Polynomial evaluation and minimality give
`R_j = 1 ↔ a.toComplex^j = 1`. The first success is its exact order.
The negative result uses the new bound `N ≤ 2*φ(N)^2` for positive `N`:
a primitive `N`th root has minimal polynomial `Φ_N` and degree `φ(N)=d`.
Thus a negative answer is exhaustive, not a timeout or an approximate failure
to lie on the unit circle. There are at most `2*d²` updates with degree at
most `d` before reduction. This test needs no integer-index factorization or
cyclotomic polynomial generation. Checked-index polynomial comparisons may
accelerate positive recognition, but must retain the bounded modular fallback
for a complete negative decision.

If a rational angle witness is wanted, enumerate reduced `k` modulo this
known `N`, enclose each corresponding root to the precision in one-embedding
certification, and use separation against the supplied root of `a.p` to
select its unique numerator. The order proof establishes `a.p = Φ_N`
semantically; there is no need to generate that polynomial again. This takes
at most `N` bounded enclosure tests, constructing no canonical candidates.
`unity?` returns the reduced turn and exact order in an external witness tied
to `a`. Its original irreducibility evidence suffices for coprime powers.
Obtaining an optional checked integer factorization remains a partial search.
A budgeted recognition returns `found`, `notUnity` only after exhaustion of
the mathematical range, or `unknown` on resource exhaustion. Default `nthRoot`
must not silently pay exhaustive recognition on every general algebraic input.

### APIs, failures, and proof composition

The following are proposed surfaces; dependent certificate fields are specified
by their contracts, not by pretending these schematic signatures compile now.

| Owner | Proposed API | Contract |
| --- | --- | --- |
| HexPoly | `DensePoly.substPow` | Direct coefficient spread, with index-zero collapse |
| HexRoots | `RootEnclosure`, `certifyNear?` | Rational/dyadic enclosure; bounded one-root Pellet certificate |
| HexNumberField | `Radical.annihilator a n` | `p(X^n)`; positive-index/nonzero hypotheses on the root and squarefree theorems |
| HexNumberField | `Radical.enclose a n bits` | Principal enclosure with width/radius bound; no factorization |
| HexNumberField | `Radical.factorRoot? work` | One selected irreducible factor and transported root, retaining evidence |
| HexNumberField | `AlgebraicNumber.ofCertified?` | Normalized irreducible polynomial plus selected root to the new canonical form |
| HexNumberField | `AlgebraicNumber.nthRoot`, `sqrt` | Existing total signatures and branches |
| HexNumberField | `Unity.Witness a`, `Unity.power`, `Unity.radical` | External reduced-angle/order witness, optional checked factorization; reuse polynomial where justified |
| HexNumberField | `Unity.ofChecked F k` | Positive checked index, arbitrary residue; reduce order before construction |
| HexNumberField | `unityOrder?`, `unity?` | Total exact recognition, then optionally the selected angle |
| HexNumberField | Budgeted counterparts | Typed exhaustion/unknown, never a fabricated value or false negative |

Work records carry polynomial equalities, root membership, factor membership,
and checked evidence, never a user assertion that an arbitrary ball is
canonical. Malformed certificate input is rejected distinctly from an
inconclusive budgeted search. Internal checked constructors in total APIs must
have `_isSome` theorems at their computed budgets. Their `none` branches are
`unreachable-by-pipeline-invariant`; no default zero, empirical fuel, or generic
solver fallback supplies the direct route's totality proof. OS allocation
failure is an operational failure, not a mathematical `none` or non-unity
result. Resource-limited entry points must expose that distinction.

The proof chain for every route is: annihilator/known minimal polynomial;
principal enclosure and its computed error bound; bounded certificate success;
unique embedding and factor; canonical existence/uniqueness; unchanged public
Mathlib correspondence. Optimizations have independent soundness at any budget
and an explicit complete fallback. The companion lists the missing lemmas.

### Cost and required evidence

Let `M(b)` denote integer multiplication cost, `F(D,h)` the measured/analysed
integer factorization cost, `e ≤ D` the selected factor degree, `h_f` its height
in bits, and `k` the requested approximation precision. Factor coefficient
height can grow: a Landau–Mignotte bound gives `h_f = O(h+D+log D)`; do not
substitute `h` for `h_f` without a proof. Root separation requires
`O(D*(h+log D))` bits with the current Mahler bound.

| Phase | Work and storage to report |
| --- | --- |
| Input preparation | Original canonical construction and input refinement, separately from extraction on preconstructed values |
| Annihilator | `Θ(D)` dense slots, `O(D*h)` bits; sparse evaluation may skip zeros |
| Approximation | Bisection iterations linear in the computed precision plus magnitude bits; powers use `O(log n)` multiplications; series term budgets above; rational numerator/denominator growth and peak workspace must be measured |
| Factorization | One `F(D,h)` invocation in the general route; all modular factors, Hensel lifts, LLL/recombination storage included; no polynomial-time claim for the current implementation |
| Certification/selection | At most the number of factors in linear Pellet tests; exact Taylor shift is quadratic in each factor degree using the current kernel; separation precision and temporary coefficient bit lengths included |
| Canonicalization | One-root refinement plus fewer than `400²` fixed local tests of the selected degree `e`; current exact Taylor kernel gives `O(e²)` arithmetic per centre, at `O(h_f+e*(m(f)+log(1+R_f)))` coefficient bits; stream centres using one workspace |
| Cyclotomic | Checked integer-index factorization, `Φ_N` generation at output degree `φ(N)` and actual coefficient height, one embedding certificate, one local canonicalization; coprime powers reuse generation and evidence |
| Recognition/composite plans | Recognition uses at most `2*d²` degree-`d` monic remainder updates, `O(d)` coefficient operations per update and one retained remainder; bound its coefficient bits by `O(d²*(h+log(d+1)))`. Include optional index factorizations, rejected plans, and intermediate exactification costs |

Bounds involving `m(f)` are precision bounds, not permission to allocate a
Cauchy grid of `4^m` squares. Local canonicalization has a constant-sized
centre window; large root magnitude changes coordinate bit length, not the
number of visited cells. Polynomial factorization still needs its own memory
analysis. Neither lower degree nor fast numerical approximation alone implies
an end-to-end improvement. Fast soft checks may filter candidates, but the
canonical success predicate and certificate must agree with the fixed exact
checker; changing the normal form is a versioned migration.

Include the canonical integer-root construction
`(#p[1099513724929, 0, 1099511627776] : ZPoly).algebraicRoots`, whose exact roots
are `±(1048577/1048576)*I`. In
[#10156](https://github.com/kim-em/hex-dev/issues/10156) this exhausted an 8 GiB
process cap before comparison; the responsible phase was not localized.
Measure squarefree normalization, factorization, all-roots isolation and each
canonical construction separately, and heights around the smaller completing
`#p[1050625, 0, 1048576]`. Include arithmetic construction of the same values
as a separate arm. Reproduce only in a process-tree 8 GiB memory cap with swap
disabled and one-CPU quota; retain failures and peak RSS/cgroup memory, not
just successful runtimes. The new single-root route and the ordinary
integer-root route must both be measured: this design does not declare the
independent integer-root bug fixed.

Use exact python-flint qqbar conformance, following the existing
[oracle policy](../../SPEC/testing.md); Sage is not an oracle. Encode an output
as its integer polynomial plus a certified selected root, reconstruct it in
qqbar, and compare exactly with qqbar's principal radical or rational-angle
value. Polynomial equality, a small residual, approximate agreement, or merely
`result^n = input` cannot validate the branch. Pin and check the adapter's
actual qqbar surface, including the zero-index convention implemented on the
Hex side. Required cases include:

- `I.nthRoot 4`, `-I`, `-1`, all zero/one conventions, and square-root agreement.
- `-1 ± 2^-t I`, `-1` on the cut, positive real inputs, and imaginary-axis
  inputs; vary `t`, force enclosures to initially cross the cut, and force
  short-budget failures followed by the complete bound.
- Reducible `p(X^n)`: rational perfect powers, `X^4-4`, `X^4+4`, partial
  perfect powers, composite indices, and general nonrational inputs.
- High-height real and nonreal inputs, the quadratic above, near-zero nonzero
  inputs, and construction costs independently of preconstructed radicals.
- Growing prime, prime-power, and highly composite unity orders; positive and
  negative turns, periodicity, coprime/noncoprime/zero powers, exact positive
  and negative recognition, and recognition budget exhaustion.
- Structural agreement across every constructor, scaled/reducible input
  polynomials, different initial enclosures, conjugation, generated Repr
  elaboration, and old isolation-expression migration.

Measure the old general route, current constant/unity shortcuts, direct route,
square-root route, binomial reductions, and optional composite/cyclotomic
routes with phases above reported separately. Record degree, height, index,
precision, factor count, number of root certificates, calls to factorization,
and canonicalization, plus allocation and peak live memory. Coprime power
reuse must show zero minimal-polynomial computations and zero repeated
factorizations. General direct extraction must show zero common-field,
norm-eliminant and evaluation-eliminant calls. Dispatch thresholds come from
retained end-to-end crossover evidence, including misses and negative
recognition overhead; do not choose thresholds from approximation timings.

Follow the [shared-host benchmark policy](../../SPEC/benchmarking.md): compiled
Mathlib-free drivers, automatically selected CPU affinity where supported,
fixed trial-major schedules, adjacent alternating AB/BA arms, all completed
samples retained, at most one unchanged rerun of an inconclusive result.
Extend existing conformance/oracle/bench jobs when implementing; do not add CI
matrices. This SPEC issue adds no solver or benchmark implementation.

### Dependency and delivery order

The computational DAG remains Mathlib-free:

```
HexPoly ── substPow ──> HexPolyZ
HexPolyZ + HexIntFactor ──> HexCyclotomic
HexRoots + HexBerlekampZassenhaus ──> HexNumberField
HexCyclotomic ──> HexNumberField ──> HexRealAlgebraic, HexNumberFieldTower
```

These are added prerequisites, not a complete replacement of existing edges.
`HexRoots` owns generic near-root certificates and separation facts, without
importing number fields. `HexNumberField` owns principal enclosures, selected
factor construction, canonicalization, and unity witnesses; cyclotomic code
knows nothing about algebraic numbers. Companions add the parallel
`HexCyclotomicMathlib → HexNumberFieldMathlib` edge, with
`HexRootsMathlib` and `HexBerlekampZassenhausMathlib` supplying transport proofs.
There is no edge back from computational libraries to companions or from
number fields to the real algebraic subtype. Real square-root wrappers reuse
the complex implementation and keep their nonnegative real contracts.

Implement in this order: shared substitution and certificate/evidence
interfaces; quantitative enclosures and local canonicalization with migration
proofs; direct factor selection and end-to-end radicals; cyclotomic library and
companion then unity reuse/recognition; optional plans after comparative
measurements. Update `libraries.yml`, Lake requirements, and the authoritative
[release manifest](../../scripts/release/released.yml) only when these libraries
and edges actually exist. Existing release pins are not changed by a design.
Manual acceptance requirements live in
[HexManual](../../HexManual/README.md#direct-radical-design-requirements).
