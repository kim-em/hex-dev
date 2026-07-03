# hex-number-field (algebraic numbers + number-field elements, depends on hex-poly-z + hex-roots + hex-resultant + hex-berlekamp-zassenhaus + hex-matrix + hex-row-reduce)

Two related types representing algebraic numbers in ℂ:

- `QAdjoin p x`: an element of `ℚ(α)`, where `α` is the simple complex
  root of `p ∈ ℤ[x]` identified by `x : SimpleRoot p`. Carries a
  rational-coefficient polynomial `coeffs` of degree `< deg p`,
  representing the value `coeffs.eval α`.
- `AlgebraicNumber`: a canonical representation of an arbitrary
  algebraic `α ∈ ℂ`, by its minimal polynomial (primitive, positive
  leading coefficient, irreducible) and the `SimpleRoot` identifying
  which complex root is meant. No coefficient data: the identified
  root *is* the algebraic number.

`QAdjoin p x` is the working representation, used during arithmetic
and directly useful when many operations happen in one fixed field.
`AlgebraicNumber` is the canonical representation, the input and
output of operations like `α + β`.

The matrix dependencies (`hex-matrix`, `hex-row-reduce`) supply the
dense ℚ-linear algebra used by `toAlgebraicNumber` (the
minimal-polynomial computation).

## Executable irreducibility

The `AlgebraicNumber` invariants include irreducibility of the stored
polynomial, and this library constructs such values, so it needs an
irreducibility test **in the Mathlib-free layer**. `hex-berlekamp-
zassenhaus` gains one small addition:

```lean
/-- `f` is irreducible over ℤ, in canonical form (primitive, positive
    leading coefficient, positive degree). Tested by a ladder of
    checks, cheapest first; the early rungs certify only `true`, and
    the final rung decides both ways:

    1. degree 1: canonical-form check alone;
    2. degree 2 or 3: canonical form and no rational root
       (a loop over the divisors of the constant and leading
       coefficients);
    3. any degree: canonical form, and Rabin's irreducibility test
       (from hex-berlekamp) accepts `f mod p` at unchanged degree for
       one of a fixed handful of small primes p (sound: an
       irreducible mod-p image of a primitive polynomial forces
       irreducibility over ℤ; incomplete: some irreducibles, such as
       `x⁴ + 1`, are reducible mod every prime);
    4. fallback: `HexBerlekampZassenhaus.factor f` reports the single
       factor `f` itself with multiplicity 1. -/
def Hex.ZPoly.isIrreducible (f : ZPoly) : Bool := …

/-- Prop form, decidable by `decide`. -/
class Hex.ZPoly.IsIrreducible (f : ZPoly) : Prop where
  holds : isIrreducible f = true
```

Constructing an `AlgebraicNumber` from a candidate polynomial `g`
tests `isIrreducible g` at runtime, and the proof field comes from the
`if h : _` branch. At runtime the ladder is a fast path in front of
`factor`, nothing more.

The ladder is what makes proof-level `decide` viable, since
`native_decide` is banned and the kernel would otherwise have to
evaluate the whole factoring pipeline. Measured on this toolchain
with a list-based model of the mod-p arithmetic: the Rabin rung on a
degree-10 polynomial over `F_5` kernel-reduces in well under a second
inside the default elaborator limits, and a deliberately oversized
degree-20-over-`F_13` workload takes tens of seconds with raised
`maxRecDepth`/`maxHeartbeats`. So `decide` is practical exactly for
the small-degree literals that fixtures and worked examples use
(`X² − 2`, `Φ₅`, `X² − 8`), and the rung-4 fallback should be treated
as runtime-only. The constant `0 : AlgebraicNumber` carries an
`isIrreducible X` proof through rung 1, which is kernel-trivial.

The Mathlib companion of hex-berlekamp-zassenhaus proves
`IsIrreducible f ↔ Irreducible (toPolynomial f)`. Its existing
factor-correctness machinery
(`Hex.ZPoly.Irreducible_iff_polynomialIrreducible` and
`FactorSoundness`) covers rung 4; rungs 1-3 add the rational-root
criterion and the mod-p lifting lemma (irreducible image at unchanged
degree lifts, via Gauss's lemma), with the mod-p decidability already
present in hex-berlekamp-mathlib.

## Types

```lean
namespace Hex

/-- A number-field element indexed by a complex simple root.
    `p` need not be irreducible for the ring operations; the field
    operations (notably `Inv`) take a `[Hex.ZPoly.IsIrreducible p]`
    instance argument. The represented value is `coeffs.eval α` where
    `α` is the root identified by `x`. `degree?` compares in the
    `Option Nat` order, where the zero polynomial (`none`) is below
    everything. -/
structure QAdjoin (p : ZPoly) (x : SimpleRoot p) where
  coeffs    : Hex.DensePoly Rat
  degree_lt : coeffs.degree? < p.degree?

/-- Canonical representation of an algebraic number `α ∈ ℂ`.
    `p` is the minimal polynomial of `α` in canonical form (primitive,
    positive leading coefficient, irreducible), `x` identifies which
    complex root of `p` is `α`, and `rep` is a working isolation of
    that root, kept at separation precision so that equality tests
    need no further refinement. -/
structure AlgebraicNumber where
  p      : ZPoly
  prim   : Hex.ZPoly.Primitive p
  pos_lc : 0 < p.leadingCoeff
  irred  : Hex.ZPoly.IsIrreducible p
  x      : SimpleRoot p
  rep    : RefinedIsolation p
  rep_mk : SimpleRoot.mk rep = x

end Hex
```

### Equality

The library's equality on `AlgebraicNumber` is `BEq`:

```lean
instance : BEq AlgebraicNumber where
  beq a b := a.p == b.p && (h ▸ a.rep).sameRoot b.rep
  -- when the polynomials are equal, compare the isolations with
  -- `sameRoot` (transporting along the polynomial equality)
```

This is a total Boolean test: minimal polynomials in canonical form
are structurally comparable, and `sameRoot` on `RefinedIsolation`
values is a single dyadic comparison (both representatives are at
separation precision by the type). The Mathlib companion proves
`a == b ↔ a.toComplex = b.toComplex`. Structural `=` on the record is
finer (it also fixes the representative) and is not the intended
notion of equality.

```lean
def AlgebraicNumber.isZero (a : AlgebraicNumber) : Bool :=
  a.p == X   -- X is the canonical minimal polynomial of 0
```

## Conversions between the two types

```lean
/-- Embed an `AlgebraicNumber` into its own field. For `deg p ≥ 2` the
    element α is represented by the polynomial `t` (degree 1, which is
    then `< deg p`). For `deg p = 1` the value is the rational
    `−p₀/p₁`, represented by a constant. The two cases are why this is
    not simply `coeffs := t`. -/
def AlgebraicNumber.toQAdjoin (a : AlgebraicNumber) : QAdjoin a.p a.x := …

/-- Project a `QAdjoin` element to canonical form, computing its
    minimal polynomial and the matching `SimpleRoot`. Requires `p`
    irreducible: on a reducible `p`, the multiplication operator on
    `ℚ[t]/(p)` sees every factor of `p`, and its minimal polynomial is
    not the minimal polynomial of the value at α. `none` only when a
    root-isolation certificate fails to appear by its depth bound
    (see hex-roots.md), which the companion proves impossible. -/
def QAdjoin.toAlgebraicNumber? [Hex.ZPoly.IsIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : Option AlgebraicNumber

/-- Total form; see "Totalisation" below. -/
def QAdjoin.toAlgebraicNumber [Hex.ZPoly.IsIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) : AlgebraicNumber :=
  (a.toAlgebraicNumber? rep h).getD
    (panicWith 0 "toAlgebraicNumber: certification failed")
```

`toAlgebraicNumber?` is the substantive operation:

1. Form the multiplication-by-`a` operator on the ℚ-vector space
   `ℚ[t]/(p)`, a `(deg p) × (deg p)` matrix over ℚ (`hex-matrix`).
2. Compute its minimal polynomial: the first ℚ-linear dependence
   among `{1, a, a², …, a^(deg p)}`, found by row reduction
   (`hex-row-reduce`). Because `p` is irreducible, `ℚ[t]/(p)` is a
   field, so this is the minimal polynomial of the *value* of `a` at
   α, of degree dividing `deg p`.
3. Clear denominators; take the primitive part; make the leading
   coefficient positive. Call the result `m`.
4. Certify `isIrreducible m` (true by construction, but the runtime
   check is what produces the proof field).
5. Identify the matching root of `m`: approximate `a`'s value from
   `rep` (evaluate `coeffs` at the isolation's disc), isolate the
   roots of `m` with `HexRoots.isolate`, refine until exactly one
   isolation's disc meets the approximation ball, and take that one
   as `rep`/`x` of the result.

## `QAdjoin p x` operations

The ring operations need no irreducibility:

```lean
instance : Zero (QAdjoin p x) := ⟨{coeffs := 0, degree_lt := …}⟩
instance : One (QAdjoin p x) := …   -- constant 1; needs deg p ≥ 1,
                                    -- which follows from x
instance : Add (QAdjoin p x) := ⟨fun a b => ⟨a.coeffs + b.coeffs, …⟩⟩
instance : Mul (QAdjoin p x) :=
  ⟨fun a b => ⟨(a.coeffs * b.coeffs) % (p.map Rat.cast), …⟩⟩
-- and Neg, Sub, scalar multiplication by Int / Rat
```

(`p` is cast to `DensePoly Rat` before the `%`. The reduction is
Euclidean division over ℚ from `HexPoly`.)

The field operations take the irreducibility instance:

```lean
instance [Hex.ZPoly.IsIrreducible p] : Inv (QAdjoin p x) where
  inv a := …   -- extended GCD of a.coeffs and p over ℚ (HexPoly.xgcd)

instance [Hex.ZPoly.IsIrreducible p] : Field (QAdjoin p x) := …
```

The `Field` instance carries real proof obligations in this
Mathlib-free library: the ring axioms for arithmetic mod `p`, and
`mul_inv_cancel`, which needs "gcd of `a.coeffs` and `p` is a unit
when `p` is irreducible over ℚ and `a ≠ 0`". The precedent is
`hex-gfq-field`, which proves the same shape of facts for
`F_p[x]/(f)` without Mathlib. Budget comparable effort here.

Numerical evaluation threads the isolation explicitly (the threading
pattern of hex-roots.md):

```lean
/-- Evaluate `a` to a complex ball. Refines the given isolation as
    needed and returns it, so the caller can pass the refined value to
    the next call. Evaluation is exact at the isolation's centre
    (rational arithmetic), with a derivative bound for the radius,
    rounded outward to dyadics. Total, and *always sound*: if
    refinement stalls (hex-roots.md), the fallback result is the
    input isolation with the ball derived from its current disc,
    which still contains the true value, just wider than `2^{−prec}`.
    The radius meets `2^{−prec}` whenever refinement succeeded, which
    the companion proves is always. -/
def QAdjoin.approx (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    RefinedIsolation p × DyadicComplexBall
```

## `AlgebraicNumber` operations

### Totalisation

The user-facing arithmetic (`add`, `mul`, `sub`, `neg`, `inv`,
`toAlgebraicNumber`) is **total**. Internally, each operation has an
`Option`-valued form (`add?`, and so on) whose `none` branch means
"a certificate failed to appear by an explicit, input-computable
bound". The public form pins that branch to the junk value `0`:

```lean
/-- Print `msg` and return `v` (compiled code); definitionally `v`
    (for reasoning). Lives in HexNumberField/Basic.lean; can move to
    HexBasic if other libraries want it. -/
@[never_extract] def Hex.panicWith (v : α) (msg : String) : α := …

instance : Inhabited AlgebraicNumber := ⟨0⟩
-- `0 : AlgebraicNumber` is the value with `p = X`; its invariant
-- proofs reduce cheaply (the degree-1 fast path in isIrreducible).

def AlgebraicNumber.add (α β : AlgebraicNumber) : AlgebraicNumber :=
  (α.add? β).getD (panicWith 0 "AlgebraicNumber.add: certification failed")
```

The junk branch is loud, not silent: `panicWith` prints at runtime
(this matters because `0` is also a legitimate output, of
`α + (−α)` for example). Logically it is just the constant `0`, so
the companion reasons about it directly: it proves soundness of the
`?`-forms first, then that each `?`-form never returns `none`
(certificates appear within the stated bounds), and the composition
gives unconditional correctness of the total forms. Every internal
loop has a computable bound: root refinement is bounded by
`separationDepth` (hex-roots.md), and the two bounds specific to this
library are named below.

`neg`, `isZero`, and `==` are total with no junk branch.

### `commonField?`

```lean
structure CommonField (α β : AlgebraicNumber) where
  r     : ZPoly
  irred : Hex.ZPoly.IsIrreducible r
  γ     : SimpleRoot r
  γrep  : RefinedIsolation r
  γ_mk  : SimpleRoot.mk γrep = γ
  αIn   : QAdjoin r γ
  βIn   : QAdjoin r γ

/-- Find one field containing both α and β: a defining polynomial `r`
    with a distinguished root γ = α + c·β, and α, β expressed in the
    basis `{1, γ, …, γ^(deg r − 1)}`. Algorithm-layer function, so it
    keeps the informative `Option` signature; the arithmetic wrappers
    absorb it. -/
def AlgebraicNumber.commonField? (α β : AlgebraicNumber) :
    Option (CommonField α β)
```

Implementation:

1. **Resultant.** Compute `r₀(t) := resultant_y(β.p(y), α.p(t − c·y))`
   for a small integer shift `c` (default `c = 1`). The roots of `r₀`
   are exactly the values `αᵢ + c·βⱼ` over the conjugates, so
   `γ = α + c·β` is among them.
2. **Factor.** `(HexBerlekampZassenhaus.factor r₀).factors` is an
   `Array (ZPoly × Nat)` of (irreducible primitive polynomial,
   multiplicity) pairs. The minimal polynomial of `γ` is one of the
   polynomials. (The `Factorization.scalar` field is ignored: the
   resultant's content and sign do not affect which factor vanishes
   at `γ`.)
3. **Numerical disambiguation.** Approximate `γ` from `α.rep` and
   `β.rep` (refining as needed), evaluate each factor on the
   approximation ball, and shrink the ball until exactly one factor's
   value straddles zero. The precision needed is bounded a priori.
   Suppose `m` is the (unknown) minimal polynomial of `γ` among the
   factors and `g` any other factor. Distinct irreducible factors are
   coprime, so `Res(m, g)` is a nonzero integer, `|Res(m, g)| ≥ 1`,
   and the root-product formula
   `Res(m, g) = lc(m)^{deg g} · ∏_{m(γᵢ)=0} g(γᵢ)` gives

   ```
   |g(γ)| ≥ ( ‖g‖₁^{deg m − 1} · M̄(m)^{deg g} )⁻¹,
   M̄(m) := √(deg m + 1) · ‖m‖∞
   ```

   after bounding each other conjugate's contribution by
   `|g(γᵢ)| ≤ ‖g‖₁ · max(1, |γᵢ|)^{deg g}` and
   `∏ max(1, |γᵢ|) = M(m)/|lc m| ≤ M̄(m)/|lc m|` (Landau). All
   quantities are read off the factor list, so

   ```
   disambiguationPrec := guard +
     max over ordered pairs (m, g) of distinct factors of
       ⌈log₂( ‖g‖₁^{deg m − 1} · M̄(m)^{deg g} )⌉
   ```

   with a small pinned `guard` for the ball-evaluation rounding. The
   loop refines to that depth and no further: at that precision
   exactly one factor's ball straddles zero.
   If the chosen factor has multiplicity `> 1` in `r₀`, the shift is
   degenerate (two conjugate pairs collide at the value `γ`): restart
   with `c = 2`, then `c = 3`, and so on. At most
   `maxShift α β := (deg α.p · deg β.p)²` shifts can be degenerate
   (one per collision of conjugate pairs), so trying `maxShift + 1`
   shifts is a bounded loop.
4. **Identify the root.** Run `HexRoots.isolate` on the chosen factor
   and locate the isolation whose disc meets the approximation ball.
5. **Recover β, then α, as elements of ℚ(γ).** Work in the field
   `QAdjoin r γ` (its `Field` instance is available, since `r`
   passed the irreducibility check in step 4). Using HexPoly's
   Euclidean algorithm over that field, compute

   ```
   g(y) := gcd( β.p(y), α.p(γ − c·y) )   in (QAdjoin r γ)[y]
   ```

   For a non-degenerate shift the two operands have exactly one
   common root, `y = β`, so `g` is linear: `g(y) = y − B` with
   `B : QAdjoin r γ`. Set `βIn := B` and `αIn := γ − c·βIn`. A gcd
   of degree ≥ 2 is one more detector of a degenerate shift: restart
   with the next `c`, in the same loop as step 3. (`DensePoly` over
   `QAdjoin r γ` is the instantiation at work here; the coefficient
   field supplies the `Div` that HexPoly's gcd needs.)

The multiplicity test in step 3 is exactly the classical
primitive-element condition: `γ = α + c·β` fails to generate
`ℚ(α, β)` only when some other conjugate pair gives the same value,
which forces the chosen factor to appear squared in `r₀`.

### Arithmetic

```lean
def AlgebraicNumber.add? (α β : AlgebraicNumber) : Option AlgebraicNumber := do
  let cf ← α.commonField? β
  haveI := cf.irred
  (cf.αIn + cf.βIn).toAlgebraicNumber? cf.γrep cf.γ_mk

def AlgebraicNumber.add (α β : AlgebraicNumber) : AlgebraicNumber :=
  (α.add? β).getD (panicWith 0 "AlgebraicNumber.add: certification failed")
```

The conversion back through `toAlgebraicNumber?` performs the field
minimisation: the result may generate a smaller field than `ℚ(γ)`.
For example `α + (−α) = 0` lands in ℚ even though both inputs live in
`ℚ(α)`.

`mul?`/`mul` and `sub?`/`sub` follow the same pattern. `neg` is total
outright: the minimal polynomial of `−α` is `p(−t)` re-canonicalised,
and the isolation is reflected exactly. `inv?` avoids the resultant:
the minimal polynomial of `1/α` is `p` with its coefficient order
reversed, re-canonicalised. The matching isolation is obtained by
transforming `rep`'s disc under `z ↦ 1/z` with `Dyadic.invAtPrec` and
re-certifying the witness; the re-certification is the one step of
`inv?` that can decline, and `inv` pins it with `panicWith` like the
others. On zero input, `inv 0 = 0` by definition (Mathlib's
convention for division), so `inv` takes no hypothesis; the
correctness theorem carries `¬ α.isZero`.

## File organisation

- `HexNumberField/Basic.lean`: `QAdjoin`, `AlgebraicNumber`,
  constructors, accessors, `BEq`, `isZero`, `panicWith`, the
  `Inhabited` instance.
- `HexNumberField/Operations.lean`: `QAdjoin` arithmetic and the
  `Field` instance.
- `HexNumberField/Approx.lean`: `QAdjoin.approx`.
- `HexNumberField/Convert.lean`: `toQAdjoin`,
  `toAlgebraicNumber?`, `toAlgebraicNumber`.
- `HexNumberField/CommonField.lean`: `commonField?`,
  `disambiguationPrec`, `maxShift`.
- `HexNumberField/AlgOps.lean`: `AlgebraicNumber` arithmetic
  (`?`-forms and their total wrappers).
- `conformance/HexNumberField/{Conformance,EmitFixtures}.lean` and
  `bench/HexNumberField/Bench.lean`: conformance and bench drivers in
  the shared sub-projects.

The `isIrreducible` addition lands in `hex-berlekamp-zassenhaus`
(one Bool-valued definition next to `factor`), not here.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md):

- *core* (Lean-only):
  - `√2 + √2 = 2·√2`: build `α : AlgebraicNumber` for the positive
    root of `X² − 2`, compute `α + α`, check the result's minimal
    polynomial is `X² − 8` and `sameRoot` matches the positive root.
  - `√2 · √2 = 2`: the result `==` the `AlgebraicNumber` of `X − 2`.
  - `√2 + (−√2) = 0`: checks field minimisation (the result lies in
    ℚ, not `ℚ(√2)`).
  - `(1 + √2) · (1 − √2) = −1`.
  - Cyclotomic check: `ζ₅ + ζ₅⁻¹ = (−1 + √5)/2`.
  - `QAdjoin` ring identities on committed elements of `ℚ(√2)` and
    `ℚ(ζ₅)`.
- *ci*: 30 random small-degree `(α, β, op)` triples with a
  deterministic seed; oracle from SageMath.
- *local*: higher-degree arithmetic, timed against the complexity
  contract.

External oracles: SageMath
(`R.<x> = ZZ[]; K.<a> = NumberField(...)`), python-flint.

## Complexity contract

Per-operation costs, with `n = max(deg α.p, deg β.p)` and
`H = max(‖α.p‖∞, ‖β.p‖∞)`:

- `α + β`, `α · β`: dominated by resultant + factoring.
  - Resultant over `R = ZPoly`: `O(n)` pseudo-division steps and
    `O(n²)` coefficient operations, where each coefficient is itself
    a polynomial in `t` (see the hex-resultant complexity contract;
    `deg r₀ ≤ n²`).
  - Factoring (`hex-berlekamp-zassenhaus` on a polynomial of degree
    `≤ n²`): per the existing BZ complexity contract.
  - Numerical disambiguation: bounded by `mahlerPrec` of the chosen
    factor.
  - Recovering β: one Euclidean gcd in `(QAdjoin r γ)[y]` on
    operands of degree ≤ `n`, where each coefficient operation is
    polynomial arithmetic mod `r`.
- `1/α`: `O(deg α.p)` for the coefficient reversal, plus one disc
  transformation and witness re-check (one `O(n²)`-operation
  certification; see hex-roots.md).
- `α + q` for rational `q`: `O(deg α.p)`; no field change.
- `isZero`, `==`: one polynomial comparison plus one dyadic
  comparison.

Each operation refines root isolations once and stores the refined
representatives in its result, so repeated operations on the same
numbers do not repeat refinement work.

## Time budgets (Phase 4 validation)

Rough estimates, to be measured against SageMath:

- `α + β` for `α, β` of degree ≤ 5: under 1 second.
- Arithmetic in a fixed degree-10 field: under 100 ms per operation.
- `α + β` for `α, β` of degree ≤ 20: under 30 seconds.

## References

- Cohen, H. *A Course in Computational Algebraic Number Theory.*
  Springer, 1993. The standard reference: especially §4.1-4.2
  (algebraic numbers, resultant-based arithmetic) and §4.5 (number
  field elements).
- Belabas, K. *Topics in computational algebraic number theory.*
  J. Théorie des Nombres de Bordeaux 16 (2004), 19-63. A survey of
  the algorithms used here.
- Bostan, A.; Flajolet, P.; Salvy, B.; Schost, É. *Fast computation
  of special resultants.* JSC 41 (2006), 1-29. Faster alternatives
  for the `commonField` resultant, if it becomes the bottleneck.
