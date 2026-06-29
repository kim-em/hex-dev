# Further work

Items not on the critical path for Berlekamp-Zassenhaus, but worth
doing once the core is stable.

**Hermite normal form.** Row reduction over `Int`: upper triangular
with positive pivots, entries above each pivot in `[0, pivot)`. Uses
extended GCD to create pivots without division: given entries `a`, `b`
in the same column, compute `(g, s, t)` with `s * a + t * b = g`,
then apply the 2×2 row transformation `[[s, t], [-b/g, a/g]]` to
zero out `b` and replace `a` with `g`. Reduce entries above each pivot
modulo the pivot. The result is unique. Returns `RowEchelonData`; an
`IsHNF` Prop-valued structure extending `IsEchelonForm` (parallel to
`IsRowReduced`) certifies correctness, with HNF-specific fields:
- Each pivot is positive
- Entries above each pivot are in `[0, pivot)`
- `det transform = 1 ∨ det transform = -1`

HNF requires extended GCD, which lives in hex-arith. Since
hex-matrix currently has no dependencies, HNF would either need:
extended GCD upstreamed into Lean 4 stdlib, a new dependency
hex-matrix → hex-arith, or a separate library (e.g.
`hex-matrix-hermite` depending on both hex-matrix and hex-arith).

**Smith normal form.** Diagonal form obtained by both row and column
operations over a principal ideal domain. The diagonal entries satisfy
`d₁ | d₂ | ⋯ | dᵣ` (divisibility chain). Useful for computing the
structure of finitely generated abelian groups and solving integer
linear systems. Like HNF, requires extended GCD and is not needed for
Berlekamp-Zassenhaus.

**Sylvester's identity (hex-matrix).** The Desnanot-Jacobi identity
relating minors of a matrix. Now the primary proof strategy for
`bareiss_eq_det` (see hex-matrix section above). Listed here as
further work only in the sense that it's a useful standalone result
beyond the Bareiss application.

**Generic Bareiss over integral domains (hex-matrix).** Generalize
Bareiss from `Int` to any integral domain with a data-carrying exact
division operation (`ediv : α → α → α` with `b ∣ a → ediv a b * b = a`);
for `Int` this is `Int.divExact`
and no zero divisors (`a * b = 0 → a = 0 ∨ b = 0`).

**Swappable polynomial representations.** Abstract over the polynomial
representation via typeclasses, allowing sparse and hash-backed
representations alongside `DensePoly`. For now, all libraries use
`DensePoly` directly.

Typeclass interface:
```lean
class PolyOps (P : Type*) (R : outParam Type*) extends
    Add P, Mul P, Neg P, Zero P, One P, BEq P where
  X : P
  C : R → P
  degree : P → Nat
  coeff : P → Nat → R
  leadingCoeff : P → R
  dropZeros : P → P
  divMod : P → P → P × P
  eval : P → R → R
  ofCoeffs : Array R → P
  toCoeffs : P → Array R

class LawfulPolyOps (P : Type*) (R : outParam Type*) [PolyOps P R] where
  -- Ring axioms
  add_comm : ∀ a b : P, a + b = b + a
  add_assoc : ∀ a b c : P, a + b + c = a + (b + c)
  mul_comm : ∀ a b : P, a * b = b * a
  mul_assoc : ∀ a b c : P, a * b * c = a * (b * c)
  add_zero : ∀ a : P, a + 0 = a
  mul_one : ∀ a : P, a * 1 = a
  left_distrib : ∀ a b c : P, a * (b + c) = a * b + a * c
  -- Coefficient semantics
  coeff_add : ∀ (a b : P) (i : Nat), coeff (a + b) i = coeff a i + coeff b i
  coeff_mul : ...  -- convolution formula
  -- BEq correctness: == agrees with coefficient equality
  beq_iff : ∀ a b : P, (a == b) = true ↔ ∀ i, coeff a i = coeff b i
  -- dropZeros: normalization to canonical form
  dropZeros_idem : ∀ p, dropZeros (dropZeros p) = dropZeros p
  dropZeros_coeff : ∀ p i, coeff (dropZeros p) i = coeff p i
  dropZeros_ext : ∀ p q, dropZeros p = p → dropZeros q = q →
      (∀ i, coeff p i = coeff q i) → p = q
  -- Division
  divMod_spec : ∀ a b : P, let (q, r) := divMod a b; q * b + r = a
  -- Evaluation is a ring homomorphism
  eval_C : ∀ r x, eval (C r) x = r
  eval_X : ∀ x, eval X x = x
  eval_add : ∀ p q x, eval (p + q) x = eval p x + eval q x
  eval_mul : ∀ p q x, eval (p * q) x = eval p x * eval q x
```

`dropZeros` is the canonical form function. For dense representations,
it strips trailing zeros. For sparse representations, it removes entries
with zero coefficients. `dropZeros_ext` gives extensionality on the
subtype `{ p : P // dropZeros p = p }` — two canonical-form polynomials
with the same coefficients are propositionally equal.

The subtype `CanonicalPoly P := { p : P // dropZeros p = p }` is where
the `≃+*` lives. The `-mathlib` bridge library would prove:

```lean
def CanonicalPoly (P : Type*) [PolyOps P R] := { p : P // dropZeros p = p }

def equiv [LawfulPolyOps P R] : CanonicalPoly P ≃+* Polynomial R
```

Eagerly-normalizing implementations (like `DensePoly`) satisfy
`dropZeros = id`, so `CanonicalPoly (DensePoly R) ≃ DensePoly R` and
the subtype wrapper is trivial. Lazy implementations pay the cost of
normalization only when they need propositional equality.

Alternative representations:

Sparse sorted array:
```lean
structure SparsePoly (R : Type*) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  sorted : ∀ i j, i < j → i < terms.size → j < terms.size →
           (terms[i]).1 < (terms[j]).1
  nonzero : ∀ i, i < terms.size → (terms[i]).2 ≠ 0
```

Sparse `ExtHashMap`-backed (with extensional equality):
```lean
structure ExtHashPoly (R : Type*) [Zero R] [BEq R] [Hashable Nat]
    [EquivBEq Nat] [LawfulHashable Nat] where
  map : ExtHashMap Nat R
  nonzero : ∀ k v, map.find? k = some v → v ≠ 0
```

Using `ExtHashMap` (not `HashMap`) gives extensionality lemmas — two
`ExtHashPoly` values are equal iff they have the same key-value pairs.
