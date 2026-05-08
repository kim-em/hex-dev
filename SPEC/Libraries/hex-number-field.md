# hex-number-field (algebraic numbers + number-field elements, depends on hex-poly-z + hex-roots + hex-resultant + hex-berlekamp-zassenhaus)

Two related types representing algebraic numbers in `ℂ`:

- `NumberField p x` — an element of `ℚ(α)` where `α` is the simple
  complex root of `p ∈ ℤ[x]` identified by `x : SimpleRoot p`.
  Carries a rational-coefficient polynomial `coeffs` of degree
  `< deg p`, evaluated at `α`.
- `AlgebraicNumber` — a canonical representation of an arbitrary
  `α ∈ ℂ_alg`, by its minimal polynomial (primitive, positive leading
  coefficient, irreducible) and the `SimpleRoot` identifying which
  complex root is meant. **No coefficient data**; the simple root
  itself is the algebraic number.

`NumberField p x` is the *working* representation, used internally
during arithmetic and useful when many operations happen in a fixed
field. `AlgebraicNumber` is the *canonical* representation, used as
the user-facing input/output of operations like `α + β`.

## Types

```lean
namespace Hex

/-- A number-field element indexed by a complex simple root.
    `p` need not be irreducible structurally; field-specific operations
    (notably `Inv`) use a `[Hex.ZPoly.Irreducible p]` instance argument.
    The element this represents is `coeffs.eval α` where `α` is the
    complex root identified by `x`. -/
structure NumberField (p : ZPoly) (x : SimpleRoot p) where
  coeffs    : Hex.DensePoly Rat
  degree_lt : coeffs.degree < p.degree

/-- Canonical representation of an arbitrary algebraic number `α ∈ ℂ_alg`.
    The simple root *itself* is the algebraic number — there is no
    coefficient data. `p` is `α`'s minimal polynomial in canonical form
    (primitive, positive leading coefficient, irreducible) and `x`
    identifies which complex root of `p` is `α`.

    Decidable equality is structural: two `AlgebraicNumber` values are
    equal iff `(p₁, x₁) = (p₂, x₂)`. This is genuinely canonical
    because `α`'s minimal polynomial is unique up to associates,
    normalised here to primitive + positive leading coefficient. -/
structure AlgebraicNumber where
  p      : ZPoly
  prim   : Hex.ZPoly.Primitive p
  pos_lc : 0 < p.leadingCoeff
  irred  : Hex.ZPoly.Irreducible p
  x      : SimpleRoot p

end Hex
```

`AlgebraicNumber.x : SimpleRoot p` is a Quotient value; equality of
`AlgebraicNumber`s reduces to equality of the `(p, x)` pair, both
decidable via the corresponding `Decidable` instances from `HexPolyZ`
and `HexRoots`.

## Conversions between the two types

```lean
/-- Embed an `AlgebraicNumber` into its own number field as the basis
    element α. Trivial: coeffs is the polynomial representing α as a
    variable (i.e., the polynomial `0 + 1·t`). -/
def AlgebraicNumber.toNumberField (a : AlgebraicNumber) :
    NumberField a.p a.x :=
  { coeffs    := <basis element representing α: coeffs[1] = 1, others = 0>,
    degree_lt := <follows from a.p.degree ≥ 1, by `irred.not_unit`> }

/-- Project a `NumberField` element down to an `AlgebraicNumber`,
    computing its actual minimal polynomial and the corresponding
    SimpleRoot. -/
def NumberField.toAlgebraicNumber (a : NumberField p x) : AlgebraicNumber := ...
```

`toAlgebraicNumber` is the substantive operation:

1. Compute the multiplication-by-`a` operator on the `ℚ`-vector space
   `NumberField p x` (a `(deg p) × (deg p)` matrix over `ℚ`).
2. Compute its minimal polynomial via standard linear algebra (the
   first `ℚ`-linear dependence among `{1, a, a², …, a^(deg p)}`).
3. The result `m(t)` is the minimal polynomial of `a`'s value over
   `ℚ` — a polynomial of degree dividing `deg p`.
4. Take primitive part, normalise leading coefficient to positive.
5. Identify the corresponding `SimpleRoot m`: numerically evaluate
   `a.approx prec` for sufficient `prec` to get a complex disc
   containing `a`'s value; isolate roots of `m` via
   `HexRoots.isolate`; find the `SimpleRoot m` whose disc contains
   `a`'s numerical value.
6. Return `AlgebraicNumber { p := m, prim, pos_lc, irred, x }`.

## `NumberField p x` operations

Pure ring operations don't need irreducibility:

```lean
instance : Zero (NumberField p x) := ⟨{coeffs := 0, degree_lt := …}⟩
instance : One (NumberField p x) := ⟨{coeffs := 1, degree_lt := …}⟩
instance : Add (NumberField p x) := ⟨fun a b => ⟨a.coeffs + b.coeffs, …⟩⟩
instance : Mul (NumberField p x) := ⟨fun a b => ⟨(a.coeffs * b.coeffs) % p, …⟩⟩
instance : Neg (NumberField p x) := ⟨fun a => ⟨-a.coeffs, …⟩⟩
-- and Sub, scalar multiplication by Int / Rat, etc.
```

Field operations require `[Hex.ZPoly.Irreducible p]`:

```lean
instance [Hex.ZPoly.Irreducible p] : Inv (NumberField p x) where
  inv a := ...   -- via extended GCD on a.coeffs and p

instance [Hex.ZPoly.Irreducible p] : Field (NumberField p x) := ...
```

Users with a specific irreducibility proof `h : Hex.ZPoly.Irreducible
myPoly` register it once via `haveI := h` (or `decide` for concrete
polynomials), and `x⁻¹` notation works on subsequent `NumberField myPoly y`
values.

Numerical evaluation uses the threading pattern from `hex-roots.md`:

```lean
/-- Numerical evaluation of `a : NumberField p x` to precision `prec`.
    Returns a refreshed `NumberField p x` (with the SimpleRoot's internal
    representative refined for cheap subsequent calls) alongside a complex
    disc guaranteed to contain `a`'s true value. -/
def NumberField.approx (a : NumberField p x) (prec : Nat) :
    NumberField p x × DyadicComplexBall
```

The returned `NumberField` is propositionally equal to the input `a`
but has its underlying `x : SimpleRoot p` refined. Callers should
store/forward the returned value to keep subsequent `approx` calls on
the cheap path.

## `AlgebraicNumber` operations

All operations follow the **threading pattern**: each returns a
refreshed `AlgebraicNumber` whose internal `SimpleRoot`
representative has been refined to `mahlerPrec p + canonOverhead p`
for the result's polynomial `p`. Callers store/forward the returned
values.

### `commonField` (public API)

```lean
/-- Find a number field containing both `α` and `β`. Returns:
    - a defining polynomial `r : ZPoly` (irreducible primitive)
    - a SimpleRoot `r` identifying the primitive element γ
    - α and β embedded as `NumberField r γ` elements. -/
def AlgebraicNumber.commonField (α β : AlgebraicNumber) :
    Σ' (r : ZPoly) (γ : SimpleRoot r),
        Hex.ZPoly.Irreducible r ×
        NumberField r γ × NumberField r γ
```

Implementation:

1. **Resultant.** Compute `r₀(t) := resultant_y(α.p(y), β.p(t − c·y))`
   for a small integer shift `c` (default `c = 1`; on degenerate
   cases — when `r₀` happens to have repeated factors crossing the
   `α + β` value — try `c = 2`, `c = 3`, etc.).
2. **Factor.** `(HexBerlekampZassenhaus.factor r₀).factors` is an
   `Array (ZPoly × Nat)` of `(irreducible primitive polynomial,
   multiplicity)` pairs. The minimal polynomial of `α + c·β` is one
   of these polynomial factors. (We ignore the `Factorization`'s
   `scalar` field — the resultant's content/sign is irrelevant for
   choosing the factor that vanishes at `α + c·β`.)
3. **Numerical disambiguation.** Use `α.x.refine` then `α.x.out prec`
   and similarly for β to get high-precision dyadic centres, sum to
   get an approximation of `α + c·β`, evaluate each polynomial
   factor at the approximation; the unique factor where the value
   is "small" (within the propagated dyadic error) is the minimal
   polynomial of `α + c·β`. Refine `prec` until the smallest factor
   is unambiguous. Multiplicity > 1 indicates a degenerate shift `c`
   — restart with a different `c`.
4. **Identify the SimpleRoot.** Run `HexRoots.isolate` on the chosen
   factor; locate the `SimpleRoot` whose disc contains the numerical
   approximation.
5. **Build the embeddings.** Express `α` and `β` in the `ℚ`-basis
   `{1, γ, γ², …, γ^(deg r − 1)}` where `γ = α + c·β`. Standard
   linear algebra: solve a `(deg r) × (deg r)` linear system. The
   results are `NumberField r γ` values for `α` and `β`.

### Arithmetic on `AlgebraicNumber`

```lean
def AlgebraicNumber.add (α β : AlgebraicNumber) : AlgebraicNumber :=
  let ⟨r, γ, _, αIn, βIn⟩ := commonField α β
  haveI : Hex.ZPoly.Irreducible r := _   -- from commonField's third component
  (αIn + βIn).toAlgebraicNumber
```

(The conversion back to canonical `AlgebraicNumber` form via
`toAlgebraicNumber` performs the field minimisation: the result might
live in a smaller field than `r`, e.g., `α + (−α) = 0` lives in `ℚ`
even though `α` and `−α` were in `ℚ(α)`.)

`mul`, `sub`, `neg`, scalar action, and `inv` (under `α ≠ 0`) follow
the same pattern. `inv` has a special-case implementation for
efficiency: `1/α` has minimal polynomial obtained by reversing the
coefficient sequence of `α.p` (then re-canonicalising), avoiding
the resultant computation.

```lean
def AlgebraicNumber.isZero (a : AlgebraicNumber) : Bool :=
  decide (a.p == X)   -- the polynomial whose only root is 0
```

Decidable equality is structural on `(p, x)`, both with decidable
equality from `HexPolyZ` and `HexRoots`.

## Layered file organisation

- `HexNumberField/Basic.lean` — types `NumberField`,
  `AlgebraicNumber`, basic constructors, accessors, decidable
  equality.
- `HexNumberField/Operations.lean` — `NumberField p x` arithmetic
  (Add, Sub, Mul, Neg, scalar action, Inv with
  `[Hex.ZPoly.Irreducible p]`). Field instance.
- `HexNumberField/Approx.lean` — `NumberField.approx` via the
  threading pattern (`x.refine` then `x.out`).
- `HexNumberField/Convert.lean` — `AlgebraicNumber.toNumberField`
  (trivial) and `NumberField.toAlgebraicNumber` (linear algebra +
  minimal polynomial computation + SimpleRoot identification).
- `HexNumberField/CommonField.lean` — public `commonField` via
  resultant + factor + numerical disambiguation + linear algebra.
- `HexNumberField/AlgOps.lean` — `AlgebraicNumber` arithmetic
  (`add`, `mul`, `sub`, `neg`, `inv`, `isZero`) via `commonField` +
  `NumberField.toAlgebraicNumber`.
- `HexNumberField/Conformance.lean` — `core` fixtures.
- `HexNumberField/Bench.lean`, `HexNumberField/EmitFixtures.lean` —
  standard testing trio.

## Conformance fixtures

Per `SPEC/testing.md`:

- *core* (Lean-only):
  - `√2 + √2 = 2·√2`: build `α := AlgebraicNumber` for the positive
    root of `X² − 2`, compute `α + α`, verify the result has minimal
    polynomial `X² − 8` with the matching `SimpleRoot`.
  - `√2 · √2 = 2`: same setup, multiplication, verify result is the
    `AlgebraicNumber` for `X − 2` (i.e., the integer 2).
  - `√2 + (−√2) = 0`: verify field minimisation kicks in (result is
    in `ℚ` not in `ℚ(√2)`).
  - `(1 + √2) · (1 − √2) = −1`: cross-check.
  - Cyclotomic check: `ζ_5 + ζ_5⁻¹ = (−1 + √5)/2`.
  - `NumberField` ring axioms on a few committed elements of `ℚ(√2)`,
    `ℚ(ζ_5)`.
- *ci*: 30 random small-degree `(α, β, op)` triples with deterministic
  seed; oracle from SageMath.
- *local*: high-degree number-field arithmetic for performance
  validation.

External oracles: SageMath
(`R.<x> = ZZ[]; K.<a> = NumberField(...); ...`), python-flint.

## Complexity contract

Per-operation costs (with `n = max(deg α.p, deg β.p)`,
`H = max(‖α.p‖∞, ‖β.p‖∞)`):

- `α + β`, `α · β`: dominated by resultant + factor.
  - Resultant: `O(n²)` polynomial-pseudodivision steps.
  - Factor (Berlekamp–Zassenhaus on a polynomial of degree ≤ `n²` and
    coefficient size ≤ exponential in `n` and `H`): per the existing
    BZ complexity contract, polynomial in input size.
  - Numerical disambiguation: bounded by `mahlerPrec` of the chosen
    factor, polynomial in factor's data.
  - Linear algebra in `commonField`: `O(n³)` over `ℚ` with
    Bareiss-style fraction-free elimination.
- `1/α`: `O(deg α.p)` for the coefficient reversal + canonicalisation.
- `α + (rational q)`: `O(deg α.p)` (no field change).
- `isZero`, equality: structural, `O(deg p)`.

The threading pattern keeps `out` calls on the cheap path: per
operation, one `refine` call (`O(refinement work to mahlerPrec p)`)
amortises across all subsequent `out` calls in that operation and
downstream callers.

## Time budgets (Phase 4 validation)

Rough estimates, refined against SageMath comparisons:

- `α + β` for `α, β` of degrees ≤ 5: < 1 second.
- Arithmetic in a fixed degree-10 number field: < 100ms per op.
- `α + β` for `α, β` of degrees ≤ 20: < 30 seconds.

## References

- Cohen, H. *A Course in Computational Algebraic Number Theory.*
  Springer, 1993. Standard reference for everything in this library.
  Especially §3 (algebraic numbers + number fields), §4 (algorithms
  on number fields).
- Belabas, K. *Topics in computational algebraic number theory.*
  J. Théorie des Nombres de Bordeaux 16 (2004), 19–63. Survey
  covering the algorithms used here.
- Bostan, A.; Flajolet, P.; Salvy, B.; Schost, É. *Fast computation
  of special resultants.* JSC 41 (2006), 1–29. Background on the
  resultant computations used in `commonField`.
