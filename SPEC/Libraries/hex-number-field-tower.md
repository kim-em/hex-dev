# hex-number-field-tower (depends on hex-number-field + hex-resultant + hex-berlekamp-zassenhaus + hex-row-reduce)

Executable successive algebraic extensions of `ℚ`. The library supports
canonical arithmetic within a fixed tower, Trager factorization, adjoining a
specified algebraic root, constructing splitting fields, and flattening a tower
to one primitive-element presentation.

The tower is a field with a fixed embedding into `ℂ`, not an abstract field only
specified up to isomorphism. Every level therefore records both an irreducible
defining polynomial over the preceding tower and the absolute `AlgebraicRoot`
chosen as its generator.

## Representation

```lean
namespace Hex

opaque NumberTower

namespace NumberTower

def rat : NumberTower

/-- Canonical mixed-radix rational coordinates in `T`. -/
opaque Elem (T : NumberTower)

abbrev Poly (T : NumberTower) := DensePoly (Elem T)

instance : DecidableEq (Elem T)
instance : Zero (Elem T)
instance : One (Elem T)
instance : Add (Elem T)
instance : Sub (Elem T)
instance : Neg (Elem T)
instance : Mul (Elem T)
instance : Inv (Elem T)
instance : Div (Elem T)

def dim (T : NumberTower) : Nat
def coeffs (a : Elem T) : Array Rat

end NumberTower
end Hex
```

Internally, `NumberTower` is a validated array of levels. A level stores its
degree, the defining polynomial's coefficients as flattened rational coordinate
arrays over the preceding dimension, computational irreducibility evidence, and
the chosen absolute root. An element stores exactly `T.dim` rational coordinates
in the mixed-radix basis

```text
α₁^e₁ * ... * αₙ^eₙ,  0 ≤ eᵢ < dᵢ.
```

This flattened representation avoids a runtime-dependent Lean carrier while the
index `Elem T` still supplies the per-tower arithmetic operations required by
`DensePoly` gcd and resultant algorithms. Coordinate equality is exact within a
fixed checked tower. Inversion is totalized by `0⁻¹ = 0`.

Raw constructors are private. Only the smart constructors below may create a
`NumberTower`. Each level stores a successful executable factorization check and
a consistent chosen complex embedding by construction. The computational
library does not turn those Boolean checks into semantic irreducibility or claim
a `Lean.Grind.Field` instance; factorization-check soundness and the law-bearing
field structure live in the Mathlib companion.

## Dependent result types

```lean
namespace Hex.NumberTower

structure Extension (T : NumberTower) where
  tower   : NumberTower
  embed   : Elem T → Elem tower
  gen     : Elem tower
  root    : AlgebraicRoot

def checkFactorization (f : Poly T) (scalar : Elem T)
    (factors : Array (Poly T × Nat)) : Bool

structure Factorization (T : NumberTower) (f : Poly T) where
  scalar  : Elem T
  factors : Array (Poly T × Nat)
  checked : checkFactorization f scalar factors = true

inductive Roots (T : NumberTower) where
  | all
  | finite (roots : Array (Elem T × Nat))

structure Splitting (T : NumberTower) (f : Poly T) where
  extension : Extension T
  roots     : Roots extension.tower

structure Flattening (T : NumberTower) where
  root          : AlgebraicNumber
  toPrimitive   : Elem T → QAdjoin root.p root.x
  fromPrimitive : QAdjoin root.p root.x → Elem T

end Hex.NumberTower
```

`Factorization.checked` is an executable certificate that the scalar and
monic positive-multiplicity factor array reconstruct the input and that every
listed factor passes the tower irreducibility checker. The companion gives its
semantic interpretation. Factors are sorted lexicographically by canonical
coordinate arrays. The zero polynomial has scalar zero and an empty factor array.
`Roots.all` records that every element is a root of the zero polynomial.

## Constructors and operations

```lean
namespace Hex.NumberTower

/-- Build a one-level tower for the irreducible presentation `ℚ(x)`. -/
def ofQAdjoin [ZPoly.CheckedIrreducible p]
    (hsf : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    Extension rat

/-- Adjoin the selected absolute algebraic root to `T`. -/
def adjoin? (T : NumberTower) (a : AlgebraicRoot) : Option (Extension T)

/-- Complete irreducible factorization with multiplicity. -/
def factor? (T : NumberTower) (f : Poly T) : Option (Factorization T f)

/-- Construct an extension in which `f` splits into linear factors. -/
def split? (T : NumberTower) (f : Poly T) : Option (Splitting T f)

/-- Replace the whole tower by one canonical primitive-element field. -/
def flatten? (T : NumberTower) : Option (Flattening T)

end Hex.NumberTower
```

`ofQAdjoin` takes squarefreeness explicitly because its returned extension
stores an `AlgebraicRoot`. Although irreducibility implies squarefreeness in
characteristic zero, that implication belongs to the Mathlib companion, while
`HasOnlySimpleRoots p` is already decidable and can be supplied by a
Mathlib-free caller.

These operations retain `Option` because their successful results contain new
dependent carrier indices and certificates; there is no honest junk
`Extension T` or `Flattening T` with which to implement a `panicWith` wrapper.
The Mathlib companion proves every result is `some` for a valid input. Callers
may preserve the checked API or eliminate `none` using those theorems.

## Embedding invariant

For a tower with generators `α₁, ..., αₙ`, each level polynomial `fᵢ` must satisfy

```text
fᵢ(αᵢ) = 0
```

after coefficients from the lower tower are evaluated through the already chosen
embedding into `ℂ`. Irreducibility alone is insufficient: it would define an
isomorphic abstract extension but could choose the wrong conjugate.

The computational layer enforces the invariant through constructor-produced
certificates:

- `ofQAdjoin` uses its supplied matching `RefinedIsolation`.
- `adjoin?` selects the unique irreducible factor that vanishes at the requested
  `AlgebraicRoot` under the current embedding.
- `split?` calls `adjoin?` for every new generator.

If serialization is later added, decoding must rerun these validations. No raw
level decoder may be public.

## Tower arithmetic

Addition and negation act coordinatewise. Multiplication recursively convolves
mixed-radix coordinates and reduces from the highest generator downward by each
monic defining polynomial. Inversion uses extended gcd in the top polynomial
quotient and recurses into the lower coefficient field. `rat` has dimension one
and identifies `Elem rat` with `Rat`.

The computational layer implements the quotient operations, including
`inv 0 = 0`. The companion turns the checked factorization evidence into
semantic irreducibility and proves the field laws, following the quotient-field
pattern of `QAdjoin` and `hex-gfq-field`.

## Trager factorization

`factor? T f` first separates content and runs Yun decomposition over `Elem T`.
Each squarefree component is factored independently, and the Yun index is the
output multiplicity. This rule is mandatory; factoring the whole input norm and
recovering multiplicity afterward is not accepted.

For one squarefree component `g`:

1. If `T = rat`, clear denominators and factor `g` directly with
   Berlekamp-Zassenhaus over `ℤ`.
2. Otherwise write `T = K(αₙ)`, let `d` be the top defining-polynomial degree,
   and let `m = degree g`. For `N = d * m`, define

   ```text
   tragerShiftCount(d, m) = choose(N, 2) + 1.
   ```

   Enumerate exactly that many distinct shifts in the deterministic order
   `0, 1, -1, 2, -2, ...`.
3. For each `c`, substitute `X - c * αₙ` and compute only the one-level norm
   `Res_Y(mₙ(Y), g(X - cY))`, a polynomial over `K`.
4. Accept the first shift whose one-level norm is squarefree over `K`. Among the
   `N` conjugate shifted roots, each unordered pair excludes at most one integer
   shift, so `tragerShiftCount` proves that the bounded search succeeds.
5. Recursively call the same factorization algorithm on that norm over `K`.
6. Embed each returned lower-tower factor into `Poly T`, take its gcd with the
   shifted component, undo the shift, normalize monically, and discard
   constants.
7. Verify that the recovered factors reconstruct the component and pass the
   tower factorization checker.

Each recursive step uses a one-level executable resultant, not a determinant
materialized as a dense matrix. It is intentionally not replaced by one absolute
norm: a factor defined over an intermediate field can make the absolute norm a
repeated power for every top-generator shift. `hex-resultant-mathlib` full
agreement is required to prove that the norm factorization and gcd recovery are
complete.

## Adjoining roots

`adjoin? T a` lifts `a.p` to `Poly T`, factors it, and evaluates each factor under
the fixed embedding of `T` together with `a.toComplex`. The
`evalDisambiguationPrec` construction from `hex-number-field`, applied to each
factor evaluation eliminant, refutes every wrong factor. The selected factor
passes the recursive irreducibility checker and becomes the new defining
polynomial; its semantic irreducibility is a companion theorem.

If the selected factor is linear, `a` already belongs to the embedded tower. The
result is an identity extension with `tower = T`, `embed = id`, and `gen` equal
to the recovered tower element. Otherwise append one validated level.

## Splitting fields

`split? T f` returns `Roots.all` for zero and a finite empty array for a nonzero
constant, without extending the tower. For a nonconstant polynomial:

1. Factor over the current tower.
2. For each nonlinear irreducible factor, compute an absolute integer eliminant
   by recursively taking norms to `ℚ`.
3. Isolate the eliminant roots and retain a root that zeros the original factor
   under the current embedding.
4. Call `adjoin?`, map the remaining polynomial into the returned tower, and
   refactor.
5. Stop when every factor is linear; collect equal roots into positive
   multiplicity buckets.

Every nonidentity adjoining step makes one selected factor linear, so the sum of
remaining nonlinear degrees decreases. This supplies the outer termination
measure. The returned extension is generated only by roots of the input.

## Flattening

`flatten?` combines the fixed generators one level at a time. For generators
`θ` and `α`, enumerate the same deterministic integer shifts and try
`γ = θ + c * α`. Compute its integer eliminant by iterated resultants and accept
the first candidate whose irreducible factor has degree equal to the combined
dimension at that generator-adjoining step. This degree test is the executable
primitive-element certificate.

For a tower of dimension `D`, at most `choose(D, 2)` shifts collide two complex
embeddings. `flattenShiftCount(D) = choose(D, 2) + 1`; test exactly the first
that many values in the signed enumeration. Candidate factor selection uses
`evalDisambiguationPrec`, so both the shift search and the root selection have
input-computable finite bounds.

Recover every old generator as a polynomial in `γ` by gcd and rational row
reduction. These coordinate expressions define `fromPrimitive`; evaluation of
mixed-radix basis elements defines `toPrimitive`. Verify both coordinate
composites on basis vectors before returning. Exactify `γ` to the canonical
`AlgebraicNumber` stored by `Flattening`.

The direct dependency on `hex-row-reduce` is intentional: flattening uses exact
rational linear algebra even though tower arithmetic itself does not.

## Conformance

- *core*: rational tower identity; `ℚ(√2)` arithmetic; the two-level tower
  `ℚ(√2, √3)`; adjoining a root already present; factorization of a polynomial
  with repeated factors; splitting a quadratic and a quartic; flattening both
  one-level and two-level towers; both flattening coordinate round trips.
- Every public operation has typical, edge, and adversarial cases. Adversarial
  cases include a bad first Trager shift, conjugate factor impostors, and a
  reducible absolute polynomial whose selected relative factor is irreducible.
  Factor `X² - 3` in `ℚ(√2, √3)` to ensure a polynomial whose linear factors
  live over the intermediate field `ℚ(√3)` is handled by recursive one-level
  Trager rather than an absolute-norm squarefreeness test.
- *ci*: deterministic fixtures checked independently with cypari2 `nfinit`,
  `nffactor`, and splitting-field operations.
- *local*: taller towers and optional Nemo/Hecke comparisons.

Sage is not an oracle. CI extends the existing single ubuntu job and does not add
a matrix or a new workflow.

## Complexity and Phase 4 budgets

Let `D = T.dim`, `n = deg f`, and let `H` bound coefficient height.

- Coordinate addition costs `O(D)` rational operations. Schoolbook
  multiplication and reduction cost `O(D²)` before later fast-arithmetic work.
- A Trager step at `K(α)/K` tries at most
  `choose(deg(mα) * n, 2) + 1` one-level resultants, then recursively factors one
  accepted norm of degree at most `deg(mα) * n` over `K`. The base case performs
  one rational factorization. This recurrence, rather than one absolute-norm
  factorization cost, is the implementation budget.
- `split?` repeats factorization after genuine degree-reducing extensions.
- `flatten?` computes primitive-element eliminants of degree at most `D` and
  solves rational systems of dimension `D`.

No standalone wall-clock ceiling is pinned before the first complete compiled
implementation. Phase 4 records component timings, then sets each ceiling from
the measured reference-host ceiling under the repository benchmarking policy.
Merge-facing conformance is restricted to tower dimension at most 8 and input
degree at most 4 until those measurements exist.

## File organisation

```text
HexNumberFieldTower/
  Basic.lean       : private level data, NumberTower, Elem, coordinates
  Arithmetic.lean  : field operations
  Embed.lean       : Extension and smart constructors
  Norm.lean        : recursive resultants
  Factor.lean      : Yun and Trager factorization
  Split.lean       : root adjoining and splitting fields
  Flatten.lean     : primitive-element conversion
```

## References

- Trager, B. M. *Algebraic factoring and rational function
  integration.* SYMSAC 1976, 219-226.
- Yuan, C.-M. [*Generalized Trager's Factorization Algorithm over Successive
  Extension Fields.*](https://mmrc.amss.cas.cn/xz/MM_Preprints/Vol_25/)
  MM Research Preprints 25 (2006), 240-247.
- van der Hoeven, J.; Lecerf, G. [*Accelerated tower
  arithmetic.*](https://doi.org/10.1016/j.jco.2019.03.002) Journal of
  Complexity 55 (2019), 101402.
- Cohen, H. *A Course in Computational Algebraic Number Theory.* Springer,
  1993.
