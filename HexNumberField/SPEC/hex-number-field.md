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

The shipped Mathlib-free API separates the semantic class
`Hex.ZPoly.Irreducible p` from the factorization-backed Boolean
`Hex.ZPoly.isIrreducible p`. This library adds the runtime-constructible wrapper

```lean
class ZPoly.CheckedIrreducible (p : ZPoly) : Prop where
  is_true : ZPoly.isIrreducible p = true
  pos_degree : 0 < p.degree?.getD 0
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

structure QAdjoin (p : ZPoly) (x : SimpleRoot p) where
  coeffs    : DensePoly Rat
  degree_lt : coeffs.degree?.getD 0 < p.degree?.getD 0

@[ext] theorem QAdjoin.ext (h : a.coeffs = b.coeffs) : a = b
instance : DecidableEq (QAdjoin p x)

/-- A factorization-lazy algebraic number. -/
structure AlgebraicRoot where
  p          : ZPoly
  prim       : ZPoly.Primitive p
  pos_lc     : 0 < p.leadingCoeff
  pos_degree : 0 < p.degree?.getD 0
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
    0 < a.p.degree?.getD 0
def AlgebraicNumber.checked (a : AlgebraicNumber) :
    ZPoly.CheckedIrreducible a.p
def AlgebraicNumber.squarefree (a : AlgebraicNumber) :
    HasOnlySimpleRoots a.p
def AlgebraicNumber.rep (a : AlgebraicNumber) : RefinedIsolation a.p
def AlgebraicNumber.IsCanonical (p : ZPoly)
    (squarefree : HasOnlySimpleRoots p) (rep : RefinedIsolation p) : Prop
def AlgebraicNumber.canonical (a : AlgebraicNumber) :
    AlgebraicNumber.IsCanonical a.p a.squarefree a.rep
def AlgebraicNumber.x (a : AlgebraicNumber) : SimpleRoot a.p
def AlgebraicNumber.rep_mk (a : AlgebraicNumber) :
    SimpleRoot.mk a.rep = a.x
def AlgebraicNumber.zeroRep : RefinedIsolation ZPoly.X
def AlgebraicNumber.canonicalRep? (p : ZPoly)
    (squarefree : HasOnlySimpleRoots p) (rep : RefinedIsolation p)
    (hzero : p ≠ ZPoly.X) :
    Option {r : RefinedIsolation p //
      AlgebraicNumber.IsCanonical p squarefree r ∧ r.sameRoot rep = true}
theorem AlgebraicNumber.ext (a b : AlgebraicNumber) (hp : a.p = b.p)
    (hrep : HEq a.rep b.rep) : a = b
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
def AlgebraicPoly.isZero (f : AlgebraicPoly) : Bool
def AlgebraicPoly.beq (f g : AlgebraicPoly) : Bool
instance : BEq AlgebraicPoly

end Hex
```

Here and in the tower SPEC, `opaque` marks a public abstraction boundary, not a
requirement that the implementation literally use an `opaque` Lean declaration.
Implementations use representation-private structures where constructors or
recursors are needed internally.

Every `AlgebraicNumber` smart constructor normalizes the primitive polynomial.
The normalized polynomial `X` uses one fixed explicit certified representative;
this makes canonical zero total without depending on success of the bounded
isolation driver. Every other polynomial is re-isolated with the fixed default
strategy at `separationDepth`, storing the unique matching disc. Thus equal
complex values have identical hidden data, not merely a semantic `BEq`; this
representation can support field laws stated with Lean equality. User-supplied
alternative refined discs cannot enter the private constructor. The sealed
record retains provenance that its representative belongs to the deterministic
isolation/refinement array (or is the fixed `X` representative); the companion
uses pairwise root separation in that array to prove this invariant unique.
The certificate stored inside `RefinedIsolation` is proof-relevant, so this
canonical-provenance field is load-bearing: every constructor path must use the
fixed `zeroRep` or `canonicalRep?`, never insert an independently transported
certificate directly.

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

`QAdjoin p x` retains canonical reduced rational coordinates. Addition,
subtraction, negation, multiplication modulo `p`, and rational scalar actions do
not require irreducibility, and neither do the constants:

```lean
def QAdjoin.ofRat (q : Rat) : QAdjoin p x
instance : NatCast (QAdjoin p x)
instance : IntCast (QAdjoin p x)
instance (n : Nat) : OfNat (QAdjoin p x) (n + 2)
```

so numerals such as `2 : QAdjoin p x` denote `(2 : Rat) • 1`, and the
companion's field structure reuses these casts rather than defining its own.
`instance : Repr (QAdjoin p x)` prints the reduced coordinates as a rational
polynomial in the generator `x`, for example `2*x^2`. Inversion requires
`[ZPoly.CheckedIrreducible p]` and uses a monic-normalized polynomial extended
gcd over `ℚ` to control rational coefficient growth. For the presentation a
canonical number induces, that evidence is an instance:

```lean
instance (a : AlgebraicNumber) : ZPoly.CheckedIrreducible a.p
```

so `a.toQAdjoin : QAdjoin a.p a.x` inverts and divides without any evidence
registered by hand.
The computational API supplies `Inv` and `Div`, with `0⁻¹ = 0`; the companion
proves their field laws after converting the checked certificate to semantic
irreducibility.

```lean
def QAdjoin.approx (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    RefinedIsolation p × DyadicComplexBall

theorem QAdjoin.approx_root (a : QAdjoin p x)
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
def AlgebraicNumber.toQAdjoin (a : AlgebraicNumber) : QAdjoin a.p a.x
def AlgebraicNumber.toRoot (a : AlgebraicNumber) : AlgebraicRoot

def QAdjoin.toAlgebraicNumber? [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option AlgebraicNumber
def QAdjoin.toAlgebraicNumber [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : AlgebraicNumber

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

`QAdjoin.toAlgebraicNumber?` materializes `1, a, a², ...` once with one
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
def QAdjoin.roots? [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Option RootSet
def QAdjoin.roots [ZPoly.CheckedIrreducible p] (...) : RootSet

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
4. For each component, build one shared integer evaluation eliminant
   `q(S) = Res_y(p(y), Res_z(e(z), S - G(y,z)))`, where `e` is the
   squarefree norm eliminant and `G` is the denominator-cleared component.
   Dilate `q` by the common denominator so its roots are the original
   component evaluations. The eliminant is nonzero and contains the true
   evaluation at every candidate. Reject candidates belonging only to other
   embeddings of `QAdjoin p x` by evaluating the original component at the
   candidate and the selected `x`; refute wrong candidates at
   `evalDisambiguationPrec`.
5. Return the surviving `AlgebraicRoot` values with the Yun multiplicity.

`AlgebraicPoly.roots?` first embeds all nonzero coefficients into one computed
primitive `QAdjoin`, then invokes the fixed-field algorithm. This common-field
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
    (pos_lc : 0 < q.leadingCoeff) (pos_degree : 0 < q.degree?.getD 0)
    (squarefree : HasOnlySimpleRoots q) (rep : RefinedIsolation q) :
    AlgebraicRoot
def ZPoly.algebraicRoots? (p : ZPoly) : Option (Array AlgebraicNumber)
def ZPoly.algebraicRoots  (p : ZPoly) : Array AlgebraicNumber

def DyadicSquare.meetsRealAxis (s : DyadicSquare) : Bool
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

The array is sorted by `AlgebraicNumber.rootLe`: real roots first, in
increasing order, then the nonreal roots ordered by isolation centre (real
part, then imaginary part, then precision). The order of the real roots is a
theorem about the values. The order among nonreal roots is deterministic,
because isolation is deterministic, but it is not determined by the roots
alone and no client may rely on it beyond determinism.

`meetsRealAxis` tests whether the closed circumscribed disc meets the real
axis, with the disc radius rounded up to the dyadic `radiusHi`: the centre's
imaginary part is at most `radiusHi` in absolute value. At separation
precision this is exact for a stored isolation: a real root lies in the
closed disc, so its centre is within the true radius, which is below
`radiusHi`, of the axis; a nonreal root and its conjugate are distinct roots
of the same integer polynomial, so `radiusHi` itself is less than a quarter
of their distance `2 |im z|` (the separation bound carries the `1449/1024`
slack), and the centre is more than `radiusHi` from the axis. `isReal`
applies it to the stored representative; the companion proves `isReal_iff`.

`approx a prec` is `QAdjoin.approx` applied to `a.toQAdjoin` with the stored
representative; its ball contains `a.toComplex` and has radius at most
`2^(-prec)`. The `Repr` instance prints the minimal polynomial and the ball
centre truncated to twelve decimal places (real part only when `isReal`); it
is for display and carries no contract beyond `approx`. Its two helpers,
`AlgebraicNumber.Display.decimal` and `AlgebraicNumber.Display.polynomial`,
are public only because the instance is, and carry no contract either.

## Common-field construction

The `Hex.AlgebraicPoly.Common` namespace is the public bounded
primitive-element machinery behind `AlgebraicPoly.roots?`, consumed directly
by hex-number-field-tower (raw evaluation, flattening recovery) and its
Mathlib companion. Everything is option-valued and checked: a `none` records
a failed certification, never a wrong value.

```lean
structure Presentation where
  generator : AlgebraicNumber
  coefficients : Array (QAdjoin generator.p generator.x)

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
    (powers : Array AlgebraicNumber) : Option (QAdjoin gamma.p gamma.x)
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
  QAdjoin.lean        : fixed-field operations and threaded approximation
  Convert.lean        : canonicalization and exactification
  Lazy.lean           : eliminants and lazy arithmetic
  Disambiguate.lean   : candidate bounds and certified selection
  AlgebraicPoly.lean  : semantic coefficient-polynomial representation
  Roots.lean          : fixed-field and algebraic-coefficient root APIs
  IntegerRoots.lean   : roots of integer polynomials, reality test, display
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
  `QAdjoin.roots?` on `g² * (X - 1)` over `ℚ(√2)`, with `g` the controlled
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
is the callable unit surface computing exactly `QAdjoin` multiplication and
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
- *Root APIs* (`QAdjoin.roots?`, `AlgebraicPoly.roots?`): PARI's
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
