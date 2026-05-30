# hex-berlekamp-zassenhaus (the capstone)

Depends on hex-berlekamp + hex-hensel + hex-lll.

Complete factoring of univariate polynomials over `Z`.

This library exposes a stable public factoring API delivered by a
**two-tier architecture**: a fast van Hoeij CLD lattice path
(`factorFast`, returning `Option`, conditionally correct), an
exhaustive slow path (`factorSlow`, unconditionally correct), and an
unconditionally-correct combinator `factor` defaulting to fast with
fallback to slow. Both paths are first-class top-level functions; the
fast path is the production code path; the slow path is the verified
backstop. No `axiom` declarations are introduced in this library or
its Mathlib bridge; every theorem has a real proof.

The public API accepts arbitrary input polynomials and normalizes
internally: extract content, remove powers of `X`, and reduce to the
primitive square-free case — then make that square-free core monic via
the integral-normalisation transform `ZPoly.toMonic`
(`c^(deg−1)·core(X/c)`, `c = leadingCoeff`), so Hensel lifting and
recombination see a monic polynomial and factors are scaled back
afterward — before running the recombination pipeline.
The output is a **`Factorization` record** explicitly separating the
signed scalar (sign · content) from the polynomial-factor multiset
with explicit multiplicities. Factor order in the polynomial-factor
array is operationally the array order, but the mathematical contract
is through product and membership rather than any semantic significance
of that order.

**Top-level API:**
```lean
def factorSlow (f : ZPoly) : Factorization
def factorFast (f : ZPoly) : Option Factorization
def factorWithBound (f : ZPoly) (B : Nat) : Factorization :=
  (factorFastWithBound f B).getD (factorSlowWithBound f B)
def factor (f : ZPoly) : Factorization :=
  factorWithBound f (ZPoly.defaultFactorCoeffBound f)
```

`factorSlow` is the unconditionally-correct exhaustive recombination
path; `factorFast` is the proof-facing van Hoeij CLD path exposing the
combined BHKS/Mignotte precision cap (`factorFastPrecisionCap`);
`factorWithBound` is the bounded combinator shared by the slow and
fast paths at a caller-supplied precision; `factor` is the public
entry point and uses the runtime-oriented Mignotte coefficient bound
`ZPoly.defaultFactorCoeffBound` for both paths.

The public `factor` does **not** call `factorFast` at the full BHKS
threshold. Irreducible inputs that split modulo the chosen prime
(e.g. `X^4 + 1`, `Φ_15`) force the van Hoeij doubling loop to grind
through every precision up to `bhksBound f`, which is intractable
even on the small conformance corpus. The smaller Mignotte cap keeps
public `factor` runtime within the per-call CI budget and falls
through to `factorSlow` whenever the fast attempt does not yield a
recombination certificate. `factorFast` itself is retained at the
full BHKS cap as the proof-facing entry point: its conditional-
correctness theorem (Group B) and the eventual BHKS Theorem 5.2
termination guarantee (Group D, leaf) apply to the BHKS-capped
combinator.

**Output convention: the `Factorization` record.**

```lean
structure Factorization where
  /-- Signed scalar absorbing both sign and content of the input.
      For nonzero input: `scalar = sign(lc(f)) · ZPoly.content(f)`.
      For `f = 0`: `scalar = 0`. -/
  scalar  : Int
  /-- Polynomial factors (each irreducible primitive with positive
      leading coefficient) with multiplicities ≥ 1; no two pairs
      share a polynomial. -/
  factors : Array (ZPoly × Nat)
deriving DecidableEq

def Factorization.product (φ : Factorization) : ZPoly :=
  φ.factors.foldl (fun acc ⟨g, m⟩ => acc * g^m) (DensePoly.C φ.scalar)
```

For `f : ZPoly`, `factor f` returns a `Factorization` such that:

1. `scalar = sign(lc(f)) · ZPoly.content(f)`. Zero iff `f = 0`.
2. Each `(g, m) ∈ factors` has:
   - `g` primitive with positive leading coefficient
     (`Hex.ZPoly.Primitive g ∧ 0 < g.leadingCoeff`),
   - `g` irreducible (`Hex.ZPoly.Irreducible g`; see below),
   - `m > 0`.
3. **No duplicate polynomial factors**: distinct entries in `factors`
   have distinct first components.
4. **Product preservation**: `Factorization.product (factor f) = f`.
5. Factor order is operationally array order; the mathematical
   contract is product + membership (an array of pairs as a multiset).

**Convention: don't break content into primes.** `factor 6 = ⟨6, #[]⟩`,
not `⟨1, #[(C 2, 1), (C 3, 1)]⟩`. The `factors` field carries
*polynomial* factors of `primitivePart(f)`; the integer
factorisation of the content lives in the `scalar` field as a single
signed integer. This matches FLINT and SymPy.

### Edge cases

| Input `f` | `factor f` |
|---|---|
| `0` | `⟨0, #[]⟩` |
| `1` | `⟨1, #[]⟩` |
| `-1` | `⟨-1, #[]⟩` |
| `2` | `⟨2, #[]⟩` |
| `-6` | `⟨-6, #[]⟩` |
| `X` | `⟨1, #[(X, 1)]⟩` |
| `-X` | `⟨-1, #[(X, 1)]⟩` |
| `X²` | `⟨1, #[(X, 2)]⟩` |
| `-X² + 1` | `⟨-1, #[(X-1, 1), (X+1, 1)]⟩` |
| `(X-1)²` | `⟨1, #[(X-1, 2)]⟩` |
| `-(X-1)²` | `⟨-1, #[(X-1, 2)]⟩` |
| `2(X-1)(X+1)` | `⟨2, #[(X-1, 1), (X+1, 1)]⟩` |
| `-2(X-1)²` | `⟨-2, #[(X-1, 2)]⟩` |

**Why this representation, vs. `Array ZPoly` with content folded as
a constant element?** Two reasons:

1. The signed-scalar field gives uniform sign handling. With a flat
   `Array ZPoly`, sign would have to be encoded as a constant-
   polynomial factor or as a separately-tracked `Int`, neither
   ergonomic. The Mathlib-bridge product theorem
   `Factorization.product (factor f) = f` then becomes provably
   exact (no "up to sign" caveat).
2. Multiplicity is explicit, matching how mature CAS systems
   (FLINT's `fmpz_poly_factor_t`, SageMath's `Factorization`,
   SymPy's `factor_list`, Mathematica's `FactorList`) represent
   integer-polynomial factorisations.

**Mathlib-free `Hex.ZPoly.Irreducible` class.**

```lean
namespace Hex.ZPoly

/-- Mathlib-free irreducibility for ZPoly. Defined as a `class` (not
    a plain `Prop`) so that downstream APIs that require `p`
    irreducible — particularly `NumberField.Inv` and the `Field`
    instance on `NumberField p x` in `hex-number-field` — can use it
    as an instance argument and have `x⁻¹` notation work via
    typeclass inference.

    A bare `Prop` would force inverse-related operations to take
    explicit hypothesis arguments, breaking the `Inv` typeclass
    contract. Mathlib's `Fact` wrapper would solve this at the
    Mathlib level, but `Fact` is unavailable in our Mathlib-free
    setting.

    This contradicts the project's usual "irreducibility is a
    term-level fact, not a class" convention (cf.
    `HexGfqField.FiniteField`'s explicit `_hirr` constructor
    argument), but the convention applies when irreducibility is
    *part of a type's identity*. For `NumberField.Inv`'s case,
    irreducibility is an *ambient assumption used by an operation*
    on an existing type, so a class is appropriate. -/
class Irreducible (f : ZPoly) : Prop where
  not_zero  : f ≠ 0
  not_unit  : ¬ Hex.ZPoly.IsUnit f       -- IsUnit defined in hex-poly-z
  no_factors : ∀ a b : ZPoly, f = a * b →
                Hex.ZPoly.IsUnit a ∨ Hex.ZPoly.IsUnit b

/-- Computational checker for irreducibility. -/
def isIrreducible (f : ZPoly) : Bool :=
  if f = 0 then false
  else if f.natDegree = 0 then
    -- Constant case: f = C k. Irreducible iff |k| > 1 and |k| is prime.
    let k := (f.coeff 0).natAbs
    1 < k && k.Prime
  else
    -- Polynomial case: irreducible iff `factor f` returns a
    -- `Factorization` whose scalar is a unit (±1) and whose
    -- factors array has exactly one entry with multiplicity 1.
    let φ := factor f
    decide (φ.scalar.natAbs = 1) &&
    φ.factors.size == 1 &&
    decide ((φ.factors.get! 0).snd = 1)

theorem isIrreducible_iff (f : ZPoly) :
    isIrreducible f = true ↔ Irreducible f

instance (f : ZPoly) : Decidable (Irreducible f) :=
  decidable_of_iff _ (isIrreducible_iff f)

end Hex.ZPoly
```

`Irreducible 0 = False` is explicit by the `not_zero` clause; the
boolean checker returns `false` on zero input. The constant-case
primality test on `Nat` lives in `HexArith`. The polynomial-case
predicate uses the `Factorization` projections directly: scalar
must be a unit (i.e., `f` is primitive up to sign), `factors` has
exactly one entry, and that entry has multiplicity 1.

**Prime selection sub-API:**
```lean
def isGoodPrime (f : ZPoly) (p : Nat) : Bool
def choosePrime (f : ZPoly) : Nat
```

`isGoodPrime` expresses the mathematical admissibility condition for
the modular reduction prime: at minimum `p ∤ lc(f)`, `p ≥ 3` (avoid
`p = 2`; see Pitfall 6), and `f mod p` is square-free. `choosePrime`
is the default total heuristic chooser. It searches through a small
fixed number of admissible small primes (≥ 3), factors `f mod p` for
each, and chooses the prime with the fewest modular factors, breaking
ties toward the smallest prime.

**Explicit pipeline records:**
```lean
structure PrimeChoiceData where
  p : Nat
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

structure LiftData where
  p : Nat
  k : Nat
  liftedFactors : Array ZPoly
```

`LiftData` is the pipeline's shared "we have factors mod `p^k`"
record: it is the output of the Hensel-lift stage and the input to
recombination. The fast-path recombination needs additional internal
metadata (the CLD lattice basis, surviving short vectors, equivalence
classes, candidate factors); these live in dedicated internal helper
records inside the recombination implementation, rather than expanding
`LiftData` itself.

Suggested stage helpers:
```lean
def choosePrimeData (f : ZPoly) : PrimeChoiceData
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData
def bhksBound (f : ZPoly) : Nat
```

`bhksBound` is the precision cap used by `factorFast`'s doubling
loop; it is the integer-arithmetic upper bound on BHKS Theorem 5.2's
threshold (see *Precision schedule* below).

## Recombination: conditional fast / unconditional slow / fallback combinator

Three top-level functions, all with full Mathlib-bridge proofs:

- **`factorSlow : ZPoly → Factorization`.** Exhaustive subset enumeration. Worst-case `O(2^r)`. **Unconditional correctness:** `factorSlow f = irreducibleFactorisationOf f`.
- **`factorFast : ZPoly → Option Factorization`.** Van Hoeij CLD at the full BHKS precision cap (`factorFastPrecisionCap f := max (bhksBound f) (defaultFactorCoeffBound f)`). **Conditional correctness:** `factorFast f = some φ ⟹ φ is the irreducible factorisation of f`. May return `none`. Proof-facing entry point.
- **`factorWithBound : ZPoly → Nat → Factorization := λ f B, (factorFastWithBound f B).getD (factorSlowWithBound f B)`.** Bounded combinator at caller-supplied precision `B`.
- **`factor : ZPoly → Factorization := λ f, factorWithBound f (defaultFactorCoeffBound f)`.** Public entry point at the runtime-oriented Mignotte coefficient bound. Unconditionally correct.

The public `factor` does not use `factorFast`'s full BHKS cap. Irreducible inputs that split modulo the chosen prime force the van Hoeij doubling loop to grind to `bhksBound f`, which is intractable even on the small conformance corpus (e.g. `X^4 + 1`, `Φ_15`). Using `defaultFactorCoeffBound` as the public cap keeps the runtime within the per-call CI budget while preserving unconditional correctness via the `factorSlow` fallback.

No axioms. BHKS Theorem 5.2 ("for precision exceeding a paper-stated
bound, `factorFast` always returns `some`") is a leaf theorem of this
development: it is in the project's requirements (Group D obligation
D1 below) but no `Decidable` instance, no `factor` correctness
theorem, and no public-API contract depends on it.

## Slow path: exhaustive recombination

Algorithm:

1. Hensel-lift `f mod p` to `f mod p^a` for `a := ⌈log_p (2 · ZPoly.defaultFactorCoeffBound f + 1)⌉`, the smallest exponent with `p^a > 2 · defaultFactorCoeffBound f`. Obtain lifted factors `g_1, …, g_r ∈ (ℤ/p^a)[x]`.
2. Enumerate subsets `S ⊆ {1, …, r}` (current implementation: the existing `recombinationSearch` helper). For each: compute `g_S := lc(f) · ∏_{i ∈ S} g_i mod p^a`, lift via centred residue, remove content, check exact division of `f`. On exact division, accept and recurse on the quotient.
3. Termination is by induction on `|remaining factors|`; the search is finite by construction.

The Mignotte coefficient bound `defaultFactorCoeffBound f` and the
Hensel precision exponent `a` are different quantities and **must
not be conflated**. The coefficient bound is a magnitude in ℤ — a
number like 1008 — describing how large any factor's coefficient
can be. The precision exponent `a` is the small integer with
`p^a > 2·(coefficient bound)` — typically a single-digit number.
Setting `a := defaultFactorCoeffBound f` makes `p^a` astronomically
large (e.g. `3^1008` for Φ_11) and renders Hensel lifting
intractable on inputs the algorithm could in principle solve.

### Slow-path correctness sketch (in-bridge proof)

Goal: `∀ f, factorSlow f = irreducibleFactorisationOf f` (up to ordering and units).

Argument:

1. **Hensel correspondence.** Every irreducible integer factor `g | f` over ℤ corresponds to a unique subset `S ⊆ {1, …, r}` such that `g ≡ ∏_{i ∈ S} g_i (mod p^a)`. Mathlib has `hensels_lemma` in `Mathlib.NumberTheory.Padics.Hensel`; the explicit subset-correspondence form may need a small wrapper lemma but follows directly.
2. **Mignotte recoverability.** At precision `a` such that `p^a > 2 · defaultFactorCoeffBound f`, the centred-residue lift in `(−p^a/2, p^a/2]` of `(∏_{i ∈ S} g_i mod p^a)` exactly recovers `g`'s integer coefficients. Mathlib has `Polynomial.mahlerMeasure_le_sqrt_sum_sq_coeff` (Landau); the repo wraps it as `mignotte_bound` in [HexPolyZMathlib/Mignotte.lean](../../HexPolyZMathlib/Mignotte.lean).
3. **Exhaustive search soundness.** The search enumerates all `2^r` subsets, accepts only those whose product reconstructs to a true integer factor (verified by exact division). By (1) and (2) every irreducible factor is found.
4. **Uniqueness.** ℤ[x] is a UFD (Mathlib: `Polynomial.UniqueFactorizationMonoid` over `Int`). The output array contains exactly one representative of each associate class.

No BHKS termination theorem is needed: the loop is finite by subset enumeration, and correctness is by Hensel + Mignotte + UFD.

## Fast path: van Hoeij CLD lattice

Recombination uses van Hoeij's algorithm with the **Combined Logarithmic Derivative (CLD)** invariant (BHKS Definition 3.1.1; HHN Definition 2). The all-coefficients-lattice variant of BHKS §5.2 is pinned: every coefficient index of the CLD is a column of the lattice. HHN's incremental-column / U-LLL / Progress-potential refinements are deliberately not used — they are a constant-factor performance optimisation, not required for correctness, and add proof complexity disproportionate to their gain.

Variant choice rationale: CLD over KP-style traces (sharper bounds, no Newton-identity recursion, non-monic `f` requires no scaling); all-coefficients over HHN incremental columns (simpler proof obligations, smaller code surface, only constant-factor slower).

### The CLD invariant

For a p-adic factor `g | f`, the CLD of `g` is the polynomial

    Φ(g) := f · g' / g  ∈  (ℤ/p^a)[x],   deg < deg f.

Φ is **additive under factor multiplication**: `Φ(g · h) = Φ(g) + Φ(h)` whenever `gh | f`. BHKS Lemma 3.1: if `g ∈ ℤ[x]` is a true factor of `f`, then `Φ(g) ∈ ℤ[x]`. Computation: one polynomial multiplication and one polynomial division of `f · g_i'` by `g_i` modulo `p^a`; division is exact because `g_i | f` over ℤ_p.

### Coefficient bound

Pinned: **BHKS Lemma 5.1 with Landau's inequality**. For `g ∈ ℤ[x]` a true factor of `f` and `j ∈ {0, …, deg f − 1}`,

    |[x^j] Φ(g)|  ≤  B_j  :=  C(n − 1, j) · n · ‖f‖₂

where `n = deg f` and `‖f‖₂² = Σ |a_i|²` is the Euclidean norm of `f`'s coefficient vector. Pure integer arithmetic; the proof reduces to Landau's classical bound `M(f) ≤ ‖f‖₂` plus the binomial bound on Φ-coefficients (BHKS Lemma 5.1 proof). HHN Algorithm 6's sharper `B₁/B₂` minimisation is rejected because it requires `Float.exp/log` and a non-trivial soundness proof; the constant-factor looseness of BHKS adds at most ~2 bits to per-coordinate precision, sub-linear in lattice size.

### Lattice construction (BHKS eq. 5.1, all-coefficients)

Let `r` be the number of lifted mod-`p` factors `g_1, …, g_r ∈ (ℤ/p^a)[x]` after Hensel lifting to precision `a`. Let `n = deg f`, so the column index set is `J = {0, …, n − 1}` of size `n`.

For each `j ∈ J`, choose the per-coordinate precision threshold

    ℓ_j := ⌈log_p (2 · B_j + 1)⌉    so that  p^{ℓ_j} > 2 B_j.

Define the **two-sided cut** (BHKS eq. 5.1; KP eq. 8): for any integer `x` and `b ≤ a`,

    Ψ^a_b(x) := (x − (x mod^± p^b)) / p^b

where `mod^±` is the centred residue in `(−p^b/2, p^b/2]`. (Plain `x / p^b` loses centring and breaks the rounding-error bound — Pitfall 1.)

The recombination basis is the `(r + n) × (r + n)` integer matrix (this is the **row-basis transpose** of BHKS eq. 5.1, since `hex-lll`'s `lll.shortVectors` API takes lattices in row-basis form):

    ┌  I_r        Ã          ┐
    │                        │     dimensions:  r rows of [I_r | Ã]
    └   0    diag(p^{a−ℓ_j}) ┘                   n rows of [0   | diag]

where `Ã[i, j] := Ψ^a_{ℓ_j}([x^j] Φ(g_i))` for `i ∈ {1,…,r}, j ∈ {0,…,n−1}`. The first `r` columns are the **indicator coordinates**; the next `n` columns hold the centred high-bits of CLD data; the last `n` rows enforce the modular-reduction structure.

### Recovery procedure (BHKS Step 7 + Lemma 3.3)

1. Run LLL on the basis above (existing `lll.shortVectors` from `hex-lll` is the surface).
2. **Cut.** Discard LLL-reduced basis vectors whose Gram–Schmidt length exceeds the BHKS Cor. 5.2 norm bound `B' := √(r + n · (r/2)²)`. (**BHKS Lemma 5.7** — the Gram–Schmidt-only argument, not the full LLL-reduction theorem — guarantees all short vectors lie in the span of the surviving basis vectors.)
3. **Project.** Map surviving vectors onto their first `r` coordinates. They span a sublattice `L' ⊆ ℤ^r` containing the indicator lattice `W := ⟨ {indicator vectors of true integer factors of f} ⟩`.
4. **Equivalence-class identification (BHKS Lemma 3.3 / FLINT Algorithm 8).** Compute reduced row echelon form of `L'`. Declare two indices `i ∼ j` iff every basis vector of `L'` agrees at positions `i` and `j`. Each equivalence class `C` produces one candidate indicator vector `w_C ∈ {0, 1}^r` with `w_C[i] = 1` iff `i ∈ C`.
5. **Reconstruct and verify.** For each candidate `w`: compute `g_w := lc(f) · ∏ g_i^{w_i} mod p^a`, lift to ℤ via centred residue, remove content, and verify by exact division of `f`. There are two distinct failure modes:
    - **(a) Reconstruction-only failure:** the equivalence-class structure on `L'` is stable (same partition produced if you re-ran the cut + projection at slightly higher precision) but a candidate's centred-residue lift fails exact division. The indicator lattice has been correctly identified; only the precision is too coarse to recover integer coefficients. Remedy: **lift `a` further (double), keep the existing lattice work** — do not re-run LLL.
    - **(b) Lattice-too-large failure:** `L' ⊋ W`, manifesting as `dim(L') = dim(L)` (no nontrivial equivalence classes) or as candidate verifications failing in a way that does not stabilise under further lifting. Remedy: **lift `a`, rebuild the basis with new CLD data, re-run LLL.**

   Distinguishing the two: if the equivalence-class partition on `L'` is the same after one further `a`-doubling, the failure is mode (a); otherwise mode (b).

### Precision schedule

Pinned: start at `a = 4`, double on lattice/verification failure, cap at `bhksBound f` (a Lean-computable integer upper bound for the BHKS Theorem 5.2 threshold `c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`; an explicit choice is given below). The cap is the BHKS bound rather than the Mignotte coefficient bound because BHKS dominates Mignotte for every `n ≥ 2` (BHKS §5.3 explicitly: "an annoying extra factor of `n` … coming from a resultant upper bound"); a smaller cap would leave `factorFast f = none` reachable on inputs the algorithm could in principle solve. The constant `4` start is what the current pipeline already does and continues to work.

The `bhksBound : ZPoly → Nat` helper is one of HO-1's deliverables. A safe explicit choice (sound integer upper bound for BHKS eq. 5.3): `bhksBound f := 1 + n · 4^(n²) · (sumSquared f + 1)^n · (log2 (sumSquared f + 1))^n` where `n := deg f` and `sumSquared f := Σ |a_i|²`. Pure `Nat` arithmetic; the upper-bound argument is straightforward (each factor of (5.3) bounded by the corresponding piece of `bhksBound`).

Termination of the doubling loop:

- If the loop reaches a state where every equivalence-class candidate verifies via exact division and `∏ candidates = f` (up to `lc(f)` and content), `factorFast` returns `some gs`. This is the success path; conditional correctness applies. **In practice, the BHKS algorithm exits via this `L' = W` certificate at precision much lower than the BHKS-bound cap** (BHKS §4.4 explicitly: "a practical implementation should not use the precision bound … because the equations could already be sufficient for smaller values of `ℓ`"); the cap is a theoretical guarantee, not a usual exit condition.
- If the loop reaches `bhksBound f` without satisfying that condition, `factorFast` returns `none`. The combinator `factor` then falls back to `factorSlow`. **`factorFast` makes no irreducibility claim on its own**; verified irreducibility is the property of `factor` (via the combinator) or `factorSlow` (called directly). HO-4 will prove the `none` branch is unreachable, but the existence of the branch makes `factor` correct without needing HO-4 first.

An additive-coefficient lattice that decodes short vectors as `Σ λ_i g_i (mod p^a)` candidate polynomials is *not* van Hoeij and is not admissible.

### Pitfalls (durable; implementer must read)

1. **Centred-residue rounding `Ψ` is the upper digits.** `Ψ^a_b(x) = (x − (x mod^± p^b)) / p^b`, *not* `x / p^b`. The latter loses centring and breaks BHKS Lemma 5.2 / KP Lemma 2.6.
2. **Short LLL vectors are not 0/1 indicators.** LLL produces a basis of a lattice *containing* `W`, not `W` itself. The indicator vectors are recovered in three stages: (i) Gram–Schmidt cut + projection to first `r` coordinates gives a sublattice `L' ⊇ W`; (ii) rref + BHKS Lemma 3.3 equivalence-class identification produces 0/1 candidate indicators; (iii) exact-division verification on each candidate certifies that `L' = W` (BHKS Lemma 3.4). All three steps are required; the algorithm cannot skip the verification round and treat candidates as confirmed factors.
3. **Two distinct failure modes — different remedies.** *Mode (a):* equivalence-class partition is stable under further lifting but reconstruction fails exact division (precision insufficient for centred-residue lift). Remedy: lift `a` only, keep lattice work. *Mode (b):* equivalence-class partition is unstable or absent (`L' ⊋ W`). Remedy: lift `a` and rebuild the lattice. Distinguishing them: re-run rref at one further `a`-doubling and check if the partition is the same. (HHN §3.1.1 articulates this distinction.)
4. **`f` in `f · g'/g` is the original input**, not a running residual after dividing out earlier-found factors.
5. **Non-monic `f`** requires no per-coordinate scaling — one of CLD's advantages over traces. Reconstruct as `lc(f) · ∏ g_i^{w_i}` followed by content removal.
6. **Avoid `p = 2`.** KP Lemma 2.6 needs a separate parity argument. Pick the smallest admissible prime ≥ 3.
7. **Coefficients of `g` (rather than CLD coefficients of `g_i`) in the lattice is the LLL82 algorithm, not van Hoeij.** Lattice dimension becomes `O(N)` not `O(r)`; entries grow exponentially.
8. **The identity block `I_r` on the first `r` columns enforces the 0/1 structure.** Without it LLL recovers some short vector but not indicators. Don't omit or rescale.
9. **If `dim(L') = dim(L)` after step 4, LLL has not made progress.** Remedy: lift more, not retry. (Manifests as `L'` having no nontrivial equivalence classes.)
10. **Hensel-precision start is constant 4, not Landau–Mignotte.** Mignotte is a possible cap only for the slow path; the fast path's cap is `bhksBound f`.

## Proof obligations (for `hex-berlekamp-zassenhaus-mathlib`)

Four groups, reflecting the two-tier architecture. Groups A, B, C are
deliverables of HO-1's bridge work; Group D is HO-4's leaf theorem
(non-blocking — nothing else depends on it). No axioms.

### Group A — slow-path correctness (gives full mathematical guarantee for `factorSlow`)

A1. **Hensel-correspondence subset bijection (squarefree case).** For `f ∈ ℤ[x]` squarefree primitive, `p` an admissible prime, `g_1, …, g_r ∈ (ℤ/p^a)[x]` the Hensel-lifted mod-`p` factorisation: every irreducible integer factor `g | f` over ℤ has a unique subset `S ⊆ {1, …, r}` with `g ≡ ∏_{i ∈ S} g_i (mod p^a)`.
    *Sketch:* `g mod p` factorises into a unique subset of `{g_i mod p}` (irreducible mod-`p` decomposition), and Hensel's lemma uniquely lifts that subset to mod `p^a`. Mathlib's `hensels_lemma` covers the analytic version; the explicit subset-correspondence form needs a small wrapper. Read BHKS §3 + Mathlib `Mathlib.NumberTheory.Padics.Hensel` before attempting.

A2. **Mignotte recoverability (modulus form).** Let `B := defaultFactorCoeffBound f`. At precision `a` such that `p^a > 2 B`, the centred-residue lift in `(−p^a/2, p^a/2]` of `(∏_{i ∈ S} g_i mod p^a)` exactly recovers `g`'s integer coefficients.
    *Sketch:* Mignotte's bound (the existing executable `defaultFactorCoeffBound` in [HexPolyZ/Mignotte.lean](../../HexPolyZ/Mignotte.lean), which Mathlib-side `mignotte_bound` in [HexPolyZMathlib/Mignotte.lean](../../HexPolyZMathlib/Mignotte.lean) already establishes via Landau) gives `|coeff(g, j)| ≤ B`; the centred residue is then unique. Implementation note: `factorSlow` uses exponent `a := B` as a sufficient choice because `p ≥ 3` ⟹ `p^a ≥ 3^B > 2B`; this is a corollary, not the abstract statement.

A3. **Exhaustive search soundness and completeness (squarefree case).** The exhaustive subset enumeration on `(henselLift f a)` returns the irreducible-factor list of squarefree primitive `f`.
    *Sketch:* Soundness: every accepted candidate passes exact division. Completeness: A1+A2 say every irreducible factor `g` corresponds to a subset `S` whose product reconstructs to `g`'s exact coefficients; the enumeration tries every subset; therefore `g` is found. Uniqueness: `Polynomial.UniqueFactorizationMonoid` over `Int` (Mathlib).

A4. **Squarefree-core correctness.** For squarefree primitive `f`, `factorSlow f = irreducibleFactorisationOf f`. Follows from A1+A2+A3.

A5. **Normalisation + reassembly bridges A4 to arbitrary input.** `factor f` (and `factorSlow f`) handle non-squarefree, non-primitive inputs by routing through `normalizeForFactor` and `reassembleNormalizedFactors`. The existing sorry'd theorems `normalizeForFactor_reassembles`, `reassembleNormalizedFactors_product`, `normalizedConstantFactors_product` (in [HexBerlekampZassenhaus/Basic.lean](../../HexBerlekampZassenhaus/Basic.lean)) must all be discharged; combined with A4, they yield `factorSlow f = irreducibleFactorisationOf f` for arbitrary `f`.
    *Sketch:* `normalizeForFactor` decomposes `f = content · X^k · h · h_repeated` where `h` is squarefree primitive. Each piece's irreducible factorisation is either standard (constants, X-powers) or given by A4 (squarefree primitive `h`); reassembly is multiplicative bookkeeping. Mathlib has `Polynomial.UniqueFactorizationMonoid` over `Int`; the GCD-based squarefree-core extraction is standard.

### Group B — fast-path conditional correctness (`factorFast f = some gs ⟹ gs is the irreducible factorisation of f`)

The fast path is allowed to return `none`; we only prove correctness conditional on `some` output. BHKS Theorem 5.2 (existence of a precision at which `none` is impossible) is *not* a Group B obligation — it's Group D.

B1. **CLD additivity.** `Φ(g · h) = Φ(g) + Φ(h)` whenever `gh | f` in `(ℤ/p^a)[x]`. The identity is `(gh)'/(gh) = g'/g + h'/h`; no coprimality hypothesis. (BHKS Lemma 3.1.) Routine.

B2. **Integrality + binomial-Mahler bound.** `g ∈ ℤ[x]` with `g | f` ⟹ `Φ(g) ∈ ℤ[x]` with `|[x^j] Φ(g)| ≤ B_j := C(n−1, j) · n · ‖f‖₂` (BHKS Lemma 5.1).
    *Sketch:* Integrality is `Φ(g) = (f/g) · g'` with `f/g ∈ ℤ[x]` (because `g | f` over ℤ; Gauss's lemma in Mathlib). For the bound: writing `g'/g = Σ_α 1/(x−α)` (formal expansion over roots of `g`), the coefficient `[x^j] (f · g'/g)` is a sum over roots `α` of `g` of `f(α) · α^{j−n+...}`-style terms. Bound by Mahler measure: `|[x^j] Φ(g)| ≤ deg(g) · M(f) · M(g)^{−1} · ...`. Apply Landau (`M(g) ≥ 1` for monic integer `g`) and the classical binomial bound on coefficients via Mahler measure; final bound is `≤ C(n−1, j) · n · ‖f‖₂`. Pathway: import `Polynomial.mahlerMeasure_le_sqrt_sum_sq_coeff` from Mathlib (already wraps Landau); reuse `mignotte_bound` from [HexPolyZMathlib/Mignotte.lean](../../HexPolyZMathlib/Mignotte.lean) for the divisor coefficient bound; transport these through one polynomial multiplication and division to reach the Φ-coefficient form. **Read BHKS Lemma 5.1's proof in §5 before attempting.**

B3. **Two-sided cut soundness.** `|x − p^b · Ψ^a_b(x)| ≤ p^b / 2` (BHKS Lemma 5.2). Routine integer arithmetic.

B4. **Norm bound for true-factor vectors.** The lattice vector corresponding to a true integer factor `g | f` has Euclidean norm `≤ B' := √(r + n · (r/2)²)`. Bookkeeping over B2 + B3 (BHKS Cor. 5.2).

B5. **LLL cut soundness (BHKS Lemma 5.7, *not* full LLL theory).**
    *Sketch:* Lemma 5.7 is *not* a full LLL-reduction theorem; it's a Gram–Schmidt argument independent of reduction quality. Statement: in any basis of a lattice `L`, if `b*_t` is the largest GS vector with `‖b*_t‖ ≤ B'`, every lattice vector `v` of norm `≤ B'` lies in the integer span of `b_1, …, b_t`. Proof: write `v = Σ λ_i b_i = Σ μ_i b*_i`; if any `λ_i ≠ 0` for `i > t`, the corresponding `μ_{i'} ≠ 0` for some `i' > t`, giving `‖v‖² ≥ ‖b*_{i'}‖² > B'^2`, contradiction. Pathway: reuse `hex-lll`'s existing Gram–Schmidt support ([HexLLL/Basic.lean](../../HexLLL/Basic.lean)) for the orthogonality identities; the new lemma is a single contradiction argument using those identities. **Read BHKS §5 (especially Lemma 5.7) before attempting** — note that the "cut" theorem we need is the GS argument, not full LLL reduction quality.

B6. **`W ⊆ L'`.** Every true-factor indicator vector survives the cut+projection into `L'`.
    *Sketch:* By B4 each true-factor lattice vector has norm `≤ B'`. By B5 such vectors lie in the span of the surviving (post-cut) basis vectors. Project to the first `r` coordinates: the indicator-block of a true-factor vector is exactly its `{0,1}^r` indicator (by construction of the lattice's `I_r` block), so `W ⊆ L'`. Pathway: direct application of B4 + B5; the proof is short bookkeeping once both are in place.

B7. **Equivalence-class identification given `L' = W` (BHKS Lemma 3.3).** When `L' = W`, the rref + equivalence-class procedure produces exactly the indicator vectors of irreducible-factor subsets.
    *Sketch:* `W` is generated by indicators of irreducible-factor subsets, which are constant-on-class and zero-outside. Apply rref to a basis of `W` and read off the support partition. Pathway: reuse the executable RREF in [HexMatrix/RREF.lean](../../HexMatrix/RREF.lean) and finish the bridge skeleton at [HexMatrixMathlib/RankSpanNullspace.lean](../../HexMatrixMathlib/RankSpanNullspace.lean) for the rational row-space side; the equivalence-class argument is then a finite case analysis on the rref output. **Read BHKS §3 (Lemma 3.3) before attempting.**

B8. **Verification certifies `L' = W` (BHKS Lemma 3.4) — the load-bearing obligation.** Given B6 (so `W ⊆ L'`): if for every equivalence-class candidate `w_C` the reconstructed `g_{w_C}` divides `f` exactly in ℤ[x] and `∏_C g_{w_C} = f` (up to `lc(f)` and content), then `L' = W` and the `g_{w_C}` are exactly the irreducible factors of `f`.
    *Sketch:* The classes refine (or equal) the irreducible-factor partition because every class union must be an integer-factor support (else its product wouldn't lift to a true integer divisor). Pathway: import `Polynomial.UniqueFactorizationMonoid` over `Int` from Mathlib for uniqueness-of-factorisation; use `Polynomial.Gauss` infrastructure for content/primitivity; the verified divisibility witnesses + uniqueness give the irreducibility conclusion. This is the theorem that *justifies the algorithm's stopping criterion*; B7 alone is too weak. **Read BHKS Lemma 3.4 in §3 before attempting.**

B9. **Conditional correctness of `factorFast`.** `factorFast f = some gs ⟹ gs is the irreducible factorisation of f` (up to associates and ordering).
    *Sketch:* `factorFast` returns `some gs` only when (i) every candidate verified via exact division and (ii) `∏ gs = f`. By B8, conditions (i) + (ii) together imply `L' = W` and `gs = irreducible factors of f`. This is the headline theorem; the proof is one application of B8 to the algorithm's terminating state.

### Group C — combined `factor` correctness (drives the public API)

C1. **`factor` unconditional correctness.** `factor f = irreducibleFactorisationOf f`.
    *Sketch:* `factor f` unfolds to `factorWithBound f (defaultFactorCoeffBound f) = (factorFastWithBound f B₀).getD (factorSlowWithBound f B₀)` for `B₀ := defaultFactorCoeffBound f`. Case analysis on the fast attempt at bound `B₀`: when it returns `some gs`, B9 (specialised to the bounded variant) gives the irreducible factorisation; when it returns `none`, A5 (via A4 squarefree-core) gives `factorSlowWithBound f B₀ = irreducibleFactorisationOf f`. The unboundedly-correct entry point `factorFast f := factorFastWithBound f (factorFastPrecisionCap f)` is not on `factor`'s correctness path; its conditional-correctness theorem is a separate Group B obligation (B9 above).

C2. **Public-API contracts** (`factor_product_of_bound`, `checkIrreducibleCert_sound`, `Decidable (Irreducible f)`) follow from C1.

The conditional correctness contract `factor_product_of_bound`:
```lean
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, |g.coeff i| ≤ B) :
    Factorization.product (factorWithBound f B) = f
```
follows from C1 specialised to the bound-aware variant. (Old
`Array.foldl`-based formulation superseded by `Factorization.product`
per the new output-convention section above.)

### Group D — leaf performance theorem (BHKS Theorem 5.2; not on the correctness critical path)

Required deliverable; structurally a leaf — no other proof obligation, public-API contract, `Decidable` instance, or theorem statement in the bridge depends on D1.

D1. **`factorFast` always succeeds: `factorFast f ≠ none`.** The theorem is about the implementation as written, with cap = `bhksBound f`. BHKS Theorem 5.2 directly gives this once the supporting lemmas are formalised; no cap extension or algorithm modification is needed (HO-1 already chose the cap correctly).

    **Pathway:**

    1. **Resultant in Mathlib4.** If `Polynomial.resultant` is not yet ported from Mathlib3, port it. The required surface: definition; `Res(f, g) = 0 ⟺ gcd(f, g) ≠ 1`; norm bound `|Res(f, g)| ≤ ‖f‖₂^(deg g) · ‖g‖₂^(deg f)` (Hadamard's inequality on the Sylvester matrix, which Mathlib has in `Mathlib.LinearAlgebra.Matrix.Determinant`).
    2. **BHKS Lemma 3.2 (bad-vector size bound).** Any vector `v ∈ L' \ W` has its associated polynomial `H_v` (built from `v`'s Φ-block) satisfying: `H_v` is divisible by some `f_i mod p^a` but not by the corresponding integer factor over ℤ, so `Res(f, H_v)` is a nonzero integer divisible by `p^(a·d)` for some `d ≥ 1`, while Hadamard bounds `|Res(f, H_v)| ≤ ‖f‖₂^(deg H_v) · ‖H_v‖₂^n`. Combining: `‖v‖₂` grows with `a`.
    3. **BHKS Theorem 5.2 (eq. 5.3 termination).** At precision satisfying `v^ℓ > c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`, the bad-vector lower bound from step 2 exceeds the LLL-cut radius `B'` from B4, so `L' \ W = ∅`. Combined with B6 (`W ⊆ L'`): `L' = W`. Read BHKS §5 (lines around eq. 5.3 and the proof following).
    4. **`bhksBound f` is a sound upper bound for the BHKS threshold.** Show that the integer-arithmetic `bhksBound f` (from the precision schedule) is `≥ ⌈log_v of the BHKS threshold⌉`. Step-by-step bounding of each factor: `n` direct; `(2C)^(n²) ≤ 4^(n²)` for `C ≥ 2` (which `hex-lll` uses); `‖f‖₂^(2n−1) ≤ (sumSquared f + 1)^n`; `(log ‖f‖₂)^n ≤ (log2 (sumSquared f + 1))^n`.
    5. **Forward verification at precision ≥ Mignotte.** The BHKS bound dominates Mignotte for every `n ≥ 2` (a one-line inequality), so any precision sufficient for separation is also sufficient for reconstruction. With `L' = W` from step 3 and precision ≥ Mignotte: B7 produces exactly the irreducible-factor indicators (Lemma 3.3), A2 gives exact integer-coefficient lifts of each `g_{w_C}`, and exact division of `f` succeeds for every candidate. So the algorithm exits via `some _`, not `none`.
    6. **Final theorem.** `theorem factorFast_terminates : ∀ f : ZPoly, factorFast f ≠ none`. Internal proof structure is the chain above.

    The bridge file gets one new theorem (`factorFast_terminates`) and a small handful of supporting lemmas (resultant Hadamard bound, BHKS Lemma 3.2, BHKS Theorem 5.2 instantiated at `bhksBound f`, BHKS-bound-dominates-Mignotte). Existing theorem statements (A1–A5, B1–B9, C1–C2) are unchanged.

    *Reading list:* BHKS §3.2 (Lemma 3.2 / "bad vector"), §5 (Theorem 5.2 termination + eq. 5.3 explicit bound, lines around `c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`); §4.4 (why the algorithm exits early in practice via the L'=W certificate); Hadamard's inequality in `Mathlib.LinearAlgebra.Matrix.Determinant`; resultant infrastructure in Mathlib4 (port from Mathlib3 if absent).

## Conformance fixtures

Core-tier conformance must include at least one input where true integer factors require a non-trivial subset product of lifted mod-p factors, and at least one input that splits heavily (≥ 4 distinct mod-p factors) over a small admissible prime. Concrete fixture instances live in [HexBerlekampZassenhaus/Conformance.lean](../../HexBerlekampZassenhaus/Conformance.lean) and the JSONL fixture file, not in this spec.

## References

- van Hoeij, *Factoring polynomials and the knapsack problem* (2002) "KP": https://www.math.fsu.edu/~hoeij/knapsack/paper/May16_2001/knapsack.pdf — original lattice + Lemma 2.6 (rounding error) + Lemma 2.8 (structural test).
- Belabas, van Hoeij, Klüners, Steel, *Factoring polynomials over global fields* (2009) "BHKS": https://www.math.u-bordeaux.fr/~kbelabas/research/factor-2008.pdf — pinned variant. CLD §3.1.1; lattice §5.2 eq. 5.1; bound Lemma 5.1; rounding Lemma 5.2; norm bound Cor. 5.2; cut soundness Lemma 5.7 (the GS-only "cut", *not* the full LLL-reduction theorem); equivalence-class Lemma 3.3; verification (`L' = W` certified by exact division) Lemma 3.4; separation/termination Theorem 5.2 with explicit threshold eq. 5.3 (`v^ℓ > c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`) — formalised in HO-4 as obligation D1, not relied on by the rest of the project; §4.4 on why practical implementations exit early via the L'=W certificate; §5.3 for the resultant-based proof structure.
- Hart, van Hoeij, Novocin, *Practical polynomial factoring in polynomial time* (2011) "HHN": https://wrap.warwick.ac.uk/id/eprint/43600/1/WRAP_Hart_0584144-ma-270913-poly_factor.pdf — referenced for completeness; incremental-column refinements are *not* used.

## Certificate structures for Z[x] irreducibility

```lean
structure PrimeFactorData where
  p : Nat
  factorDegrees : Array Nat
  factorCerts : Array IrreducibilityCertificate

structure ZPolyIrreducibilityCertificate where
  perPrime : Array PrimeFactorData
  -- Degree analysis data ruling out nontrivial factor degrees

def checkIrreducibleCert
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) : Bool
```

Grouping by prime in a single `PrimeFactorData` record keeps the
per-prime triple (prime, modular factor degrees, irreducibility
witnesses) aligned by construction, instead of relying on parallel
arrays matched up implicitly. Each `IrreducibilityCertificate` in
`factorCerts` carries its own `p` and `n` fields (see
`hex-berlekamp`), so the checker can cross-check that each entry's
`p` matches the enclosing `PrimeFactorData.p` and that its `n` lies
in `factorDegrees`.

The outer contract is checker-first: the precise internal certificate
layout may evolve, but the public contract should be stable.

Soundness split:
- `hex-berlekamp-zassenhaus` proves the computational soundness of the
  checker data flow and degree-obstruction computation.
- `hex-berlekamp-zassenhaus-mathlib` proves
  `checkIrreducibleCert f cert = true → Irreducible f`. This follows
  from C1 (`factor` correctness) plus the certificate's per-prime
  degree-obstruction soundness.
