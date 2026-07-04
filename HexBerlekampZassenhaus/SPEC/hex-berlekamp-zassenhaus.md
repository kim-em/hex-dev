# hex-berlekamp-zassenhaus (the capstone)

Depends on hex-berlekamp + hex-hensel + hex-lll.

Complete factoring of univariate polynomials over `Z`.

This library exposes a stable public factoring API delivered by a
**cost-based hybrid architecture**. Three recombination tiers share
the same front end (normalise → choose prime → Hensel lift) and differ
only in how they recombine the lifted mod-`p` factors into integer
factors:

- **`factorClassical`** (returns `Option`) — classical *size-ordered*
  subset recombination with factor removal: the same algorithm class
  as the verified Isabelle/AFP reference (`zassenhaus_reconstruction`,
  which iterates `subseqs` of the lifted factors). Fast when the
  number of lifted factors `r` is small; worst-case `O(2^r)`.
- **`factorLattice`** (returns `Option`) — van Hoeij CLD lattice
  recombination via `hex-lll`. *Polynomial in `r`*; used when `r` is
  large enough that classical recombination would exceed its subset
  budget (e.g. Swinnerton-Dyer inputs, on which the classical reference
  *also* explodes). The lattice tier is a **correct fallback** there;
  whether it is *fast enough to strictly beat* the reference on that
  extreme-`r` tail is a separate optimisation (it currently grinds to
  the precision cap — see the early-termination follow-up).
- **`factorTrial`** (total) — exhaustive integer trial division. No
  modular reduction; the unconditional totality backstop, reached only
  when no admissible prime exists.

The public combinator `factor` estimates the recombination cost from
the modular factorisation and dispatches: `factorClassical` for small
estimated cost, `factorLattice` for large `r`, `factorTrial` as the
final backstop. All three return canonical factorisations; the tiers
are result-equivalent, differing only in cost. The classical tier wins
the *constant-factor* race against the reference on easy inputs; the
lattice tier wins *asymptotically* on hard (high-`r`) inputs. No
`axiom` declarations are introduced in this library or its Mathlib
bridge; every theorem has a real proof.

> **Historical note (not part of the timeless design).** The current
> implementation names the lattice tier `factorFast` and the classical
> tier `factorSlowModular`, and its public `factor` dispatches by a
> *precision cap* rather than by estimated cost — which is why it is
> exponential on easy reducible inputs (a low-cap lattice attempt
> misses, then falls through to exhaustive recombination). The
> cost-based dispatch below replaces that.

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
def factorClassical (f : ZPoly) : Option Factorization
def factorLattice   (f : ZPoly) : Option Factorization
def factorTrial     (f : ZPoly) : Factorization
def factor          (f : ZPoly) : Factorization
```

`factorClassical` and `factorLattice` are the two recombination tiers,
both `Option`-valued because both require an admissible prime;
`factorTrial` is the total trial-division backstop; `factor` is the
public cost-based combinator. Each tier also exposes a bounded variant
`…WithBound f B` parameterised by a Mignotte coefficient bound `B`
(used by the precision/conformance tests); `factor` runs the tiers at
`ZPoly.defaultFactorCoeffBound f`.

The dispatch is **by estimated recombination cost, not by a precision
cap** (see *Cost-based hybrid dispatch* below). The estimate is read
off the modular factorisation: the lifted-factor count `r`, the
degree distribution of the modular factors, the coefficient height /
Mignotte precision, the expected size-ordered subset count, and the
CLD lattice dimension. When the estimated classical cost is small,
`factor` runs `factorClassical`; when `r` is large, it runs
`factorLattice`; when no admissible prime exists, it runs
`factorTrial`. The combinator is unconditionally correct because the
final backstop is `choosePrimeData?`-independent.

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
    `HexGFqField.FiniteField`'s explicit `_hirr` constructor
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

end Hex.ZPoly
```

This library provides the `Irreducible` *class* and the executable
`isIrreducible` *checker* only. It deliberately does **not** state
`isIrreducible f = true ↔ Irreducible f`, nor derive
`Decidable (Irreducible f)` from it.

The reason is a library-layering fact, not an oversight: that
biconditional is logically equivalent to the full forward
correctness of `factor` (its forward direction asserts the checker's
single-factor verdict implies genuine irreducibility — i.e. `factor`
found *every* factor; its backward direction asserts an irreducible
input yields exactly one factor). That correctness is the Group A/B/C
capstone, and the SPEC assigns those proofs to the Mathlib bridge
(they cite `Polynomial.UniqueFactorizationMonoid`, `hensels_lemma`,
and `Polynomial.Gauss`; see `Slow-path correctness sketch (in-bridge
proof)` and the Group C obligations below). A Mathlib-free file
cannot import the bridge, so the biconditional cannot be proved here.

Therefore `Hex.ZPoly.isIrreducible_iff` and the
`Decidable (Hex.ZPoly.Irreducible f)` instance it backs live in
`hex-berlekamp-zassenhaus-mathlib`. This library exposes the class
(so downstream Mathlib-free APIs such as `NumberField.Inv` can take
`[Hex.ZPoly.Irreducible p]` as an instance argument) and the
executable checker (pure computation, no proof obligation); it does
not claim the checker is *correct*.

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
`p = 2`; see Pitfall 6), and `f mod p` is square-free. The square-free
test is a single modular **GCD** — `gcd(f mod p, f' mod p)` is a unit —
**not** a factorisation, so `isGoodPrime` is cheap.

`choosePrime` selects the **first suitable prime**: it walks the
candidate primes in increasing order and returns the first `p` with
`isGoodPrime f p`, then factors `f mod p` only for that prime. This
matches the verified Isabelle/AFP `Berlekamp_Zassenhaus` reference
(`Suitable_Prime.thy` `find_prime` selects the first separable prime;
`berlekamp_zassenhaus_main` then runs `finite_field_factorization_int p f`
once). It does not *exhaustively* minimise the modular-factor count
across all candidate primes — that classical Zassenhaus heuristic costs
one modular factorisation per candidate prime (≈95 per call here). But
because `r` drives the cost-based dispatch (§*Cost-based hybrid
dispatch*), when the first suitable prime yields an `r` **near the
classical/lattice threshold**, the dispatcher may factor at one or two
further admissible primes and keep the smallest `r` — a bounded retry,
not a full sweep. On inputs comfortably inside the small-`r` regime,
first-suitable factors `f mod p` exactly once.

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
def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData
def bhksBound (f : ZPoly) : Nat
```

`bhksBound` is the BHKS component of the lattice tier's precision cap
`factorFastPrecisionCap` (keyed on the square-free core); it is the
integer-arithmetic upper bound on BHKS Theorem 5.2's threshold (see
*Precision schedule* below).

`choosePrimeData?` is `Option`-valued. The executable searches a
**bounded hot-path candidate set** `HotPathCandidates`, fixed in
SPEC as

> `HotPathCandidates := { p : Nat | 3 ≤ p ∧ p ≤ 500 ∧ Nat.Prime p }`

i.e. every prime in the closed range `[3, 500]` (`p = 2` is
excluded by `isGoodPrime`). This set has 95 elements; their
primorial `∏ HotPathCandidates ≈ 10^203`, which is the lower
bound D2 below uses to characterise `factorTrial` inputs.

The cap of 500 balances two constraints: the primorial must be large
enough that no realistic polynomial reaches the lower bound (so the
`none` case is unreachable in practice, per D2); and the cap must be
small enough that the modular kernel uses `ZMod64` throughout. The
primorial `10^203` exceeds any realistic `|lc(f)·disc(f)|` by tens of
orders of magnitude, and `p ≤ 500` is far inside `ZMod64`'s
`UInt64.word` domain.

`choosePrimeData?` walks `HotPathCandidates` in increasing order and
returns the **first** prime with `isGoodPrime f p`, factoring `f mod p`
only for that prime (first-suitable selection; see `choosePrime`
above). On realistic input a suitable prime appears among the first few
candidates, so the walk stops almost immediately. Only when **no**
candidate is suitable does the walk visit all 95 — and because
suitability is the cheap separability GCD (not a factorisation), even
that exhaustive `none`-case walk is fast.

The candidate set is SPEC-fixed: the `none` case MUST check every
element of `HotPathCandidates` before concluding `none` (this is what
D2's characterisation rests on), so a curated subset that skips primes
like `29, 37, 41, 43, 47, 53, 59, 61, 67`, or an input-dependent fuel
cap, is a SPEC violation. First-suitable changes *when the walk stops on
success*, not *which primes are eligible*.

`choosePrimeData? f = none` when no element of
`HotPathCandidates` satisfies `isGoodPrime f p`. This is by
design; implementing an unbounded `BigInt`-modular fallback
inside `choosePrimeData?` would cascade through every consumer of
`PrimeChoiceData` (the `ZMod64.Bounds`-indexed fields prevent
holding a non-ZMod64-backed `PrimeChoiceData`).

### Cost-based hybrid dispatch

**Load-bearing invariant: the dispatch always terminates in a
`choosePrimeData?`-independent backstop.** This is what makes `factor`
unconditionally correct on every `ZPoly`. The combinator chooses a
recombination tier from the modular factorisation, then falls back if
the chosen `Option`-tier returns `none`:

```lean
def factor (f : ZPoly) : Factorization :=
  match choosePrimeData? f with
  | none => factorTrial f                       -- no admissible prime: total backstop
  | some d =>
    let tier := dispatchTier f d                 -- cost estimate from `d`
    match (if tier = .lattice then factorLattice f else factorClassical f) with
    | some r => r
    | none =>
      -- the chosen tier missed (precision/lattice failure): try the
      -- other recombination tier, then the unconditional trial backstop
      match (if tier = .lattice then factorClassical f else factorLattice f) with
      | some r => r
      | none => factorTrial f
```

`dispatchTier f d` estimates the classical recombination cost from the
lifted-factor count `r`, the modular factors' degree distribution, the
coefficient height / Mignotte precision, the expected size-ordered
subset count, and the CLD lattice dimension; near the threshold it may
re-run `choosePrimeData?` at another admissible prime that yields a
smaller `r` (`r` depends on the prime, not on `f` alone). Small
estimated cost → `factorClassical`; large `r` → `factorLattice`.

- **`factorClassical`** — Hensel lift + *size-ordered* subset
  recombination with factor removal, under a **hard subset budget**
  (a cap on candidate subsets tried, derived from the cost estimate).
  Same algorithm class as the verified reference; the win is the
  arithmetic constant. Returns `none` only when `choosePrimeData? f =
  none` (which the outer `match` already handles) or when its subset
  budget is exceeded — in which case the budget was mis-estimated and
  `factorLattice` takes over.
- **`factorLattice`** — van Hoeij CLD lattice recombination; polynomial
  in `r`. Used when `r` is large enough that the classical subset
  search would exceed its budget (e.g. Swinnerton-Dyer inputs). May
  return `none` if its precision schedule does not reach the
  separation bound; the trial backstop then catches it.
- **`factorTrial`** — exhaustive integer trial division over the
  Mignotte-bounded divisor enumeration. No modular reduction, no
  `PrimeChoiceData`. Astronomically slow in the worst case but truly
  unconditional. Reached only when `choosePrimeData? f = none`, which
  by D2 below means `|lc(f)·disc(f)| ≥ ∏ HotPathCandidates`.

**Dispatch must be observable, and the merge gate asserts on it
(not just on wall-clock).** `factor` records a `FactorTrace` —
chosen tier, prime `p`, `r`, Hensel precision, subset candidates
tried, lattice dimension, and **whether the trial backstop ran**.
A pure timing gate is gameable (a regression can "pass" by silently
falling back to a slow tier, or by only timing out on machines CI does
not expose); the counter assertions close that hole. Per the named
conformance suite (fixtures under
`conformance-fixtures/HexBerlekampZassenhaus/`):

- every designated fixture must exit on its **expected tier**; an
  unexpected `factorTrial` fallback, or a small-`r` case entering
  `factorLattice` (or vice versa), is a SPEC violation and **fails the
  merge gate**;
- the size-ordered subset count on small-`r` fixtures must stay under
  the declared bound;
- `factorTrial` MUST never run on any fixture except the dedicated
  `X² − L²`-style regression cases that exercise the
  `choosePrimeData? = none` path; those are tagged `scheduledHardwareTag`
  and excluded from per-PR CI.

No silent suite-shrinking, and no silent tier-downgrade.

## Recombination tiers and the cost-based combinator

Three recombination tiers, all with full Mathlib-bridge proofs:

- **`factorClassical : ZPoly → Option Factorization`.** Size-ordered subset recombination with factor removal, under a hard subset budget. Same algorithm class as the verified reference. **Unconditional correctness when it returns `some`:** the output is the irreducible factorisation of `f`. Returns `none` only on budget exhaustion or no admissible prime.
- **`factorLattice : ZPoly → Option Factorization`.** Van Hoeij CLD at the full BHKS precision cap (`factorFastPrecisionCap f := max (bhksBound core) (defaultFactorCoeffBound f)` where `core := (normalizeForFactor f).squareFreeCore`; the BHKS component is keyed on the square-free core the CLD pipeline actually lifts, not on `f` — a core can have larger coefficient norm than `f`, e.g. `f = (x¹⁸−1)(x¹⁹−1)`, so `bhksBound f` can undershoot the core's separation threshold). **Conditional correctness:** `factorLattice f = some φ ⟹ φ is the irreducible factorisation of f`. May return `none`.
- **`factorTrial : ZPoly → Factorization`.** Exhaustive integer trial division. **Unconditional correctness:** `factorTrial f = irreducibleFactorisationOf f`.
- **`factor : ZPoly → Factorization`.** The cost-based combinator (above): dispatch by estimated recombination cost, fall back to the other tier, then to `factorTrial`. Unconditionally correct.

No axioms. BHKS Theorem 5.2 ("for precision exceeding a paper-stated
bound, `factorLattice` always returns `some`") is a leaf theorem of
this development: it is in the project's requirements (Group D
obligation D1 below) but no `Decidable` instance, no `factor`
correctness theorem, and no public-API contract depends on it.

## Classical recombination (small r)

`factorClassical` — the same algorithm class as Isabelle's
`zassenhaus_reconstruction` (which iterates `subseqs` of the lifted
factors), refined with size-ordering, factor removal, and a subset
budget:

1. Hensel-lift `f mod p` to `f mod p^a` for `a := ⌈log_p (2 · ZPoly.defaultFactorCoeffBound f + 1)⌉`, the smallest exponent with `p^a > 2 · defaultFactorCoeffBound f`. Obtain lifted factors `g_1, …, g_r ∈ (ℤ/p^a)[x]`. The lift may proceed **incrementally** — recombine at a low precision and double only when a candidate's centred lift fails exact division — with `a` (the Mignotte precision) as the completeness backstop.
2. Search subsets **in increasing size with factor removal**: for sizes `d = 1, …, ⌊r/2⌋`, and each size-`d` subset `S` of the *remaining* factors, form the candidate `g_S := normalizeFactorSign(primitivePart(dilate(lc(f))(centeredLift(∏_{i ∈ S} g_i mod p^a))))`; if `g_S` exactly divides the current target, accept it, remove `S`, and continue on the quotient. When no proper subset of the remaining factors divides, those factors form a single irreducible factor. A **hard subset budget** caps the candidates tried; exceeding it returns `none` (dispatch then routes to `factorLattice`). The budget is **level-aware**: it is tightened up front to the largest cumulative size-level boundary `∑_{d ≤ k} C(r-1, d)` that fits, since a partial size level certifies nothing beyond the previous level boundary — a search that cannot complete declines at the last completable level instead of burning the rest of the budget. When every level fits (small `r`) the budget is unchanged.
3. Termination is by induction on `|remaining factors|`, bounded by the subset budget.

Size-ordering with factor removal makes fully-split inputs `O(r²)`
(singletons peel immediately) while enumerating the same candidate set
as naive search, so soundness is unchanged; the worst case (irreducible
over ℤ but splitting into many factors mod every prime) is `O(2^r)` —
the regime handed to `factorLattice`.

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

## Large-r recombination: van Hoeij CLD lattice

`factorLattice` — the tier the cost-based combinator selects when the
lifted-factor count `r` is large enough that `factorClassical`'s
size-ordered subset search would exceed its budget. It is **polynomial
in `r`** (the classical reference, and `factorClassical`, are `O(2^r)`
there), so it is the asymptotically-correct path on the extreme-`r` tail
— e.g. Swinnerton-Dyer inputs, which split into many small factors mod
every prime. It certifies irreducibility (unlike a CLD recovery that
declines on the single-class case), so it returns `some` where exhaustive
search would explode. Beating the reference *in wall-clock* on that tail
additionally requires terminating before the precision cap (a separate
optimisation; today it grinds to the cap and is correct-but-slow). It is
built on the verified `hex-lll` short-vector
machinery.

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

Pinned: start at `a = 4`, double on lattice/verification failure, cap at `bhksBound core` for `core := (normalizeForFactor f).squareFreeCore` — the polynomial the pipeline actually lifts and separates. The papers have a single polynomial, but the executable normalizes first, and the square-free core's coefficient norm can *exceed* `f`'s (Mignotte divisor growth; witness `f = (x¹⁸−1)(x¹⁹−1)`, whose core `f/(x−1)` has `coeffNormSq 36` against `f`'s `4` and a strictly larger `bhksBound`), so keying the cap on `f` would undershoot the core's separation threshold. `bhksBound` is a Lean-computable integer upper bound for the BHKS Theorem 5.2 threshold `c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`; an explicit choice is given below. The cap is the BHKS bound rather than the Mignotte coefficient bound because BHKS dominates Mignotte for every `n ≥ 2` (BHKS §5.3 explicitly: "an annoying extra factor of `n` … coming from a resultant upper bound"); a smaller cap would leave `factorFast f = none` reachable on inputs the algorithm could in principle solve. The constant `4` start is what the current pipeline already does and continues to work.

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

Four groups. **Naming:** the obligations below use the historical tier
names — **`factorSlow` is the classical tier `factorClassical`** and
**`factorFast` is the lattice tier `factorLattice`**; the mathematical
content is unchanged by the rename. Group A gives `factorClassical`'s
unconditional correctness (the tier `factor` uses for small `r`); Group
B gives `factorLattice`'s conditional correctness (large `r`); Group C
gives `factor`'s correctness via the cost-based combinator (and the
tier-equivalence / dispatch-soundness contracts above); Group D is the
non-blocking leaf performance theorem. No axioms.

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
    *Sketch:* Lemma 5.7 is *not* a full LLL-reduction theorem; it's a Gram–Schmidt argument independent of reduction quality. Statement: in any basis of a lattice `L`, if `b*_t` is the largest GS vector with `‖b*_t‖ ≤ B'`, every lattice vector `v` of norm `≤ B'` lies in the integer span of `b_1, …, b_t`. Proof: write `v = Σ λ_i b_i = Σ μ_i b*_i`; if any `λ_i ≠ 0` for `i > t`, the corresponding `μ_{i'} ≠ 0` for some `i' > t`, giving `‖v‖² ≥ ‖b*_{i'}‖² > B'^2`, contradiction. Pathway: reuse `hex-lll`'s existing Gram–Schmidt support ([HexLLL/Basic.lean](https://github.com/leanprover/hex-lll/blob/main/HexLLL/Basic.lean)) for the orthogonality identities; the new lemma is a single contradiction argument using those identities. **Read BHKS §5 (especially Lemma 5.7) before attempting** — note that the "cut" theorem we need is the GS argument, not full LLL reduction quality.

B6. **`W ⊆ L'`.** Every true-factor indicator vector survives the cut+projection into `L'`.
    *Sketch:* By B4 each true-factor lattice vector has norm `≤ B'`. By B5 such vectors lie in the span of the surviving (post-cut) basis vectors. Project to the first `r` coordinates: the indicator-block of a true-factor vector is exactly its `{0,1}^r` indicator (by construction of the lattice's `I_r` block), so `W ⊆ L'`. Pathway: direct application of B4 + B5; the proof is short bookkeeping once both are in place.

B7. **Equivalence-class identification given `L' = W` (BHKS Lemma 3.3).** When `L' = W`, the rref + equivalence-class procedure produces exactly the indicator vectors of irreducible-factor subsets.
    *Sketch:* `W` is generated by indicators of irreducible-factor subsets, which are constant-on-class and zero-outside. Apply rref to a basis of `W` and read off the support partition. Pathway: reuse the executable RREF in [HexMatrix/RREF.lean](https://github.com/leanprover/hex-matrix/blob/main/HexMatrix/RREF.lean) and finish the bridge skeleton at [HexMatrixMathlib/RankSpanNullspace.lean](https://github.com/leanprover/hex-matrix-mathlib/blob/main/HexMatrixMathlib/RankSpanNullspace.lean) for the rational row-space side; the equivalence-class argument is then a finite case analysis on the rref output. **Read BHKS §3 (Lemma 3.3) before attempting.**

B8. **Verification certifies `L' = W` (BHKS Lemma 3.4) — the load-bearing obligation.** Given B6 (so `W ⊆ L'`): if for every equivalence-class candidate `w_C` the reconstructed `g_{w_C}` divides `f` exactly in ℤ[x] and `∏_C g_{w_C} = f` (up to `lc(f)` and content), then `L' = W` and the `g_{w_C}` are exactly the irreducible factors of `f`.
    *Sketch:* The classes refine (or equal) the irreducible-factor partition because every class union must be an integer-factor support (else its product wouldn't lift to a true integer divisor). Pathway: import `Polynomial.UniqueFactorizationMonoid` over `Int` from Mathlib for uniqueness-of-factorisation; use `Polynomial.Gauss` infrastructure for content/primitivity; the verified divisibility witnesses + uniqueness give the irreducibility conclusion. This is the theorem that *justifies the algorithm's stopping criterion*; B7 alone is too weak. **Read BHKS Lemma 3.4 in §3 before attempting.**

B9. **Conditional correctness of `factorFast`.** `factorFast f = some gs ⟹ gs is the irreducible factorisation of f` (up to associates and ordering).
    *Sketch:* `factorFast` returns `some gs` only when (i) every candidate verified via exact division and (ii) `∏ gs = f`. By B8, conditions (i) + (ii) together imply `L' = W` and `gs = irreducible factors of f`. This is the headline theorem; the proof is one application of B8 to the algorithm's terminating state.

### Group C — combined `factor` correctness (drives the public API)

C1. **`factor` unconditional correctness.** `factor f = irreducibleFactorisationOf f`.
    *Sketch:* `factor f` unfolds to `factorWithBound f (defaultFactorCoeffBound f) = (factorFastWithBound f B₀).getD (factorSlowWithBound f B₀)` for `B₀ := defaultFactorCoeffBound f`. Case analysis on the fast attempt at bound `B₀`: when it returns `some gs`, B9 (specialised to the bounded variant) gives the irreducible factorisation; when it returns `none`, A5 (via A4 squarefree-core) gives `factorSlowWithBound f B₀ = irreducibleFactorisationOf f`. The unboundedly-correct entry point `factorFast f := factorFastWithBound f (factorFastPrecisionCap f)` is not on `factor`'s correctness path; its conditional-correctness theorem is a separate Group B obligation (B9 above).

C2. **Public-API contracts** (`factor_product_of_bound`, `checkIrreducibleCert_sound`, `Hex.ZPoly.isIrreducible_iff`, and the `Decidable (Hex.ZPoly.Irreducible f)` instance it backs) follow from C1. Like C1 itself, these are bridge-side and are stated in `hex-berlekamp-zassenhaus-mathlib` (the Mathlib-free library provides only the `Irreducible` class and the `isIrreducible` checker — see the §`Mathlib-free Hex.ZPoly.Irreducible class`).

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

Required deliverable; structurally a leaf — no other proof obligation, public-API contract, `Decidable` instance, or theorem statement in the bridge depends on D1 or D2. Both are stated against the cost-based hybrid (see *Cost-based hybrid dispatch* above): D1 is the CLD lattice tier's completeness (`factorLattice f ≠ none` given a good prime), D2 the tight characterisation of the inputs that reach the `factorTrial` backstop.

D1. **The lattice tier succeeds when a good prime exists on the core: `toMonicPrimeData? (normalizeForFactor f).squareFreeCore ≠ none → factorLattice f ≠ none`.** The antecedent is keyed on `toMonicPrimeData?` of the square-free core — the monic-transform prime the CLD pipeline actually Hensel-lifts against — and the theorem is about the implementation as written, with cap `factorFastPrecisionCap f` (keyed on the core, per *Precision schedule* below), not `bhksBound f`. BHKS Theorem 5.2 supplies the precision/recombination half, conditional on a good prime being available. The unconditional `factorLattice f ≠ none` is **false** against the implementation — `HexBerlekampZassenhaus/Basic.lean` ships `finitePrimeSearchNoneQuadratic` and the `1 + L·X` family as witnesses where the hot-path prime search exhausts its bounded candidate set. This is by design; the unconditional safety net is the cost-based combinator's `factorTrial` backstop (per *Cost-based hybrid dispatch* above), not inside any modular tier. D2 below pins down exactly which inputs reach that backstop.

    **Pathway:**

    1. **Resultant in Mathlib4.** If `Polynomial.resultant` is not yet ported from Mathlib3, port it. The required surface: definition; `Res(f, g) = 0 ⟺ gcd(f, g) ≠ 1`; norm bound `|Res(f, g)| ≤ ‖f‖₂^(deg g) · ‖g‖₂^(deg f)` (Hadamard's inequality on the Sylvester matrix, which Mathlib has in `Mathlib.LinearAlgebra.Matrix.Determinant`).
    2. **BHKS Lemma 3.2 (bad-vector size bound).** Any vector `v ∈ L' \ W` has its associated polynomial `H_v` (built from `v`'s Φ-block) satisfying: `H_v` is divisible by some `f_i mod p^a` but not by the corresponding integer factor over ℤ, so `Res(f, H_v)` is a nonzero integer divisible by `p^(a·d)` for some `d ≥ 1`, while Hadamard bounds `|Res(f, H_v)| ≤ ‖f‖₂^(deg H_v) · ‖H_v‖₂^n`. Combining: `‖v‖₂` grows with `a`.
    3. **BHKS Theorem 5.2 (eq. 5.3 termination).** At precision satisfying `v^ℓ > c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`, the bad-vector lower bound from step 2 exceeds the LLL-cut radius `B'` from B4, so `L' \ W = ∅`. Combined with B6 (`W ⊆ L'`): `L' = W`. Read BHKS §5 (lines around eq. 5.3 and the proof following).
    4. **`bhksBound f` is a sound upper bound for the BHKS threshold.** Show that the integer-arithmetic `bhksBound f` (from the precision schedule) is `≥ ⌈log_v of the BHKS threshold⌉`. Step-by-step bounding of each factor: `n` direct; `(2C)^(n²) ≤ 4^(n²)` for `C ≥ 2` (which `hex-lll` uses); `‖f‖₂^(2n−1) ≤ (sumSquared f + 1)^n`; `(log ‖f‖₂)^n ≤ (log2 (sumSquared f + 1))^n`.
    5. **Forward verification at precision ≥ Mignotte.** The BHKS bound dominates Mignotte for every `n ≥ 2` (a one-line inequality), so any precision sufficient for separation is also sufficient for reconstruction. With `L' = W` from step 3 and precision ≥ Mignotte: B7 produces exactly the irreducible-factor indicators (Lemma 3.3), A2 gives exact integer-coefficient lifts of each `g_{w_C}`, and exact division of `f` succeeds for every candidate. So the algorithm exits via `some _`, not `none`, given a good prime is available.
    6. **Final theorem.** `theorem factorLattice_ne_none_of_goodPrime : ∀ f : ZPoly, toMonicPrimeData? (normalizeForFactor f).squareFreeCore ≠ none → factorLattice f ≠ none`. Internal proof structure is the chain above; the implementation-level statement is on the bounded raw tier, `factorLatticeFactorsWithBound f (factorFastPrecisionCap f) ≠ none`, with `factorLattice f ≠ none` as the `Factorization`-level corollary.

    The bridge file gets one new theorem (`factorLattice_ne_none_of_goodPrime`) and a small handful of supporting lemmas (resultant Hadamard bound, BHKS Lemma 3.2, BHKS Theorem 5.2 instantiated at the core's `bhksBound`, BHKS-bound-dominates-Mignotte). Existing theorem statements (A1–A5, B1–B9, C1–C2) are unchanged.

    *Reading list:* BHKS §3.2 (Lemma 3.2 / "bad vector"), §5 (Theorem 5.2 termination + eq. 5.3 explicit bound, lines around `c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n`); §4.4 (why the algorithm exits early in practice via the L'=W certificate); Hadamard's inequality in `Mathlib.LinearAlgebra.Matrix.Determinant`; resultant infrastructure in Mathlib4 (port from Mathlib3 if absent).

D2. **Tight characterisation of trial-backstop inputs.** Statement shape:

    ```lean
    theorem choosePrimeData?_none_implies_huge
        (f : ZPoly) (hp : f.Primitive) (hs : f.IsSquareFree)
        (hf : Hex.choosePrimeData? f = none)
        (p : Nat) (hp_range : 3 ≤ p ∧ p ≤ 500) (hp_prime : Nat.Prime p) :
        (p : ℤ) ∣ (f.leadingCoeff * f.discriminant)
    ```

    Equivalently, `|lc(f) · disc(f)| ≥ ∏ HotPathCandidates`, an astronomically large lower bound that no realistic polynomial reaches. (`HotPathCandidates` is the SPEC-fixed set defined in the algorithmic-architecture clause above.)

    `factorTrial` is reached only when no admissible hot-path prime exists, i.e. `choosePrimeData? f = none` (both modular tiers rest on the same hot-path candidate set, so neither `factorClassical` nor `factorLattice` has a prime to lift when there isn't one). Given a good prime, D1 makes `factorLattice` succeed and the classical tier's completeness makes `factorClassical` succeed, so whichever tier the cost-based dispatch selects resolves in a modular tier and never falls through. So D2 is the tight delineation of inputs that hit the trial backstop: any `f` with `|lc(f) · disc(f)| < ∏ HotPathCandidates` is provably handled by `factorClassical` or `factorLattice`, runs at `ZMod64` speed, and never touches `factorTrial`.

    **Pathway:**

    1. **`isGoodPrime f p` for `p ∈ HotPathCandidates` unfolds to `p ∤ lc(f) · disc(f)`.** Mathematical content: `p ≥ 3` plus `p ∤ lc(f)` keep the leading coefficient mod `p`, and `gcd(f mod p, f' mod p)` is a unit iff `f mod p` is square-free iff `p ∤ disc(f)` (over a field of characteristic `p`, square-free ↔ discriminant nonzero; the `p ≥ 3` constraint avoids characteristic-2 separability subtleties).
    2. **Reverse-engineer `choosePrimeData? f = none`.** It means every candidate `p` in `HotPathCandidates` failed `isGoodPrime f p`, which by step 1 means every such `p` divides `lc(f) · disc(f)`.
    3. **Primorial lower bound.** If every prime in a set `S` divides `M ∈ ℤ`, then `|M| ≥ ∏ S` (standard).

    The bridge file gets one new theorem (`choosePrimeData?_none_implies_huge`) and a small helper unfolding `isGoodPrime`. No new mathematical content; the bound is a clean divisibility argument.

    **Executable precondition.** D2 is about the `none` case only: `choosePrimeData? f = none` must mean *no* element of `HotPathCandidates` is suitable, so the `none` path MUST test every one of the 95 primes in `[3, 500]` before concluding `none`. First-suitable selection short-circuits on *success* (returning at the first suitable prime, which is correct and required for performance), but it must **not** short-circuit the `none` conclusion: a curated subset that skips primes, or an input-dependent fuel cap on the `none`-case walk, is a SPEC violation that would weaken D2.

## Headline correctness theorem

`HexBerlekampZassenhausMathlib` must carry, and the `done_through ≥ 4` bump is blocked on, an end-to-end theorem with the following **semantic shape**:

> For every nonzero `f : Hex.ZPoly`, the public-API output `φ := Hex.factor f : Hex.Factorization` satisfies all five clauses:
>
> 1. **Product preservation.** `Hex.Factorization.product φ = f`.
> 2. **Primitive irreducibility.** Every `entry ∈ φ.factors` is primitive and `Polynomial.Irreducible (HexPolyZMathlib.toPolynomial entry.1)` holds in the Mathlib sense.
> 3. **Positive multiplicities.** Every `entry ∈ φ.factors` has `entry.2 > 0`.
> 4. **No factor associates.** For any two distinct positions in `φ.factors`, the underlying polynomials are not associates of each other.
> 5. **Scalar carries sign and content.** `φ.scalar` equals the signed integer content of `f` (sign × content per `ZPoly.content` and `ZPoly.leadingCoeff` conventions).

The final Lean name (e.g. `factor_correct`, `factor_irreducible_factorisation`) may differ from this prose, and intermediate predicates such as `IsIrreducibleFactorization` may abbreviate the conjunction, but the five-clause shape is binding.

This is the post-condition of the public API and the contract the combinator advertises in its docstring. **The headline theorem is the critical-path artefact for `done_through ≥ 4`.** Intermediate lemmas are admissible when they are either

- (a) load-bearing for some proof of the headline theorem, or
- (b) independently justified as public API, executable checker, or regression guard with stated rationale.

Lemmas that satisfy neither are dead weight and should be removed or refactored until they earn their place.

A bridge file that proves an arbitrary collection of intermediate lemmas but does not prove the headline correctness theorem is incomplete by SPEC: the orchestrator must not bump `done_through` to 4 in that state. The local realisation of this clause for the open BZ architectural directive is rewritten in the dispatched rollback issue.

### Invariant contracts and dispatch soundness

Beyond the five-clause headline, the cost-based dispatch adds contracts
that the implementation must satisfy and that **conformance checks from
the start, even though the formal proofs land last** (freezing the
proof-shaped surface early so the migration does not discover, late,
that there is no clean theorem boundary):

- **Tier-result equivalence.** `factorClassical f`, `factorLattice f`
  (when `some`), and `factorTrial f` all return the *same* canonical
  factorisation; the cost-based dispatch therefore cannot change the
  result, only the cost.
- **Dispatch soundness.** `factor f` equals the canonical factorisation
  for every `f`, independent of which tier `dispatchTier` selects and of
  any fallback taken.
- **Fallback semantics.** The trial backstop is a *correctness* backstop,
  not a silent recovery for a buggy tier: a tier returning `some` must be
  correct (it is never "rescued" by re-running), and an unexpected
  fallback on a designated fixture is a gate failure (see *Quality
  gates*).
- **Normalisation / reconstruction.** The `normalizeForFactor` →
  recombine → `reassemblePolynomialFactors` pipeline preserves the
  product and the primitive/content/sign bookkeeping (the metamorphic
  relations below are the executable shadow of these).

The dispatch-soundness and tier-equivalence theorems are discharged
together with C1 (they reduce to it: each tier, when it answers, answers
canonically, so the combinator does too). They are listed here, not as a
separate group, because they carry no new mathematical content beyond
A–C — only the new control-flow shape.

## Conformance fixtures (primary correctness mechanism)

Correctness is established primarily by **extensive differential
conformance against FLINT** plus metamorphic relations. Conformance is
*evidence toward* correctness, not correctness itself; the formal
obligations (Groups A–D) remain binding but land last (see *Quality
gates* and the design principle in
[SPEC/design-principles.md](../design-principles.md)).

The oracle does not merely compare the output multiset to FLINT. For
each input it independently checks: product reconstruction
(`∏ factors^mult · scalar = f`); each factor primitive with positive
leading coefficient; multiplicities positive and distinct factors
distinct; and each reported factor irreducible according to FLINT.

The committed corpus must span (concrete instances live in
[HexBerlekampZassenhaus/Conformance.lean](../../HexBerlekampZassenhaus/Conformance.lean)
and the JSONL fixtures, not in this spec):

- **Swinnerton-Dyer ladder** SD2–SD6 (degrees 4–64) and shifted variants
  — the dispatch stressor spanning small→large `r`; the high rungs
  exercise `factorLattice` where the classical reference explodes.
- **Mignotte coefficient-swell** inputs (a true factor whose
  coefficients dwarf `f`'s) — exercises Hensel precision; a too-low
  precision silently *misses* or *mis-lifts* factors. Highest-value
  correctness family.
- non-monic / large-content / negative-leading-coefficient (lc-scaling
  and sign normalisation); high-multiplicity `g^k · h^m` (squarefree
  decomposition + multiplicity);
- cyclotomic products / `X^n − 1` / `Φ_n` for composite and prime-power
  `n`; reciprocal / palindromic factors; two factors with identical
  modular degree profiles;
- planted-factor randomized inputs with controlled `r` (monic and
  non-monic); bad-prime-retry (discriminant divisible by the first
  several primes); Eisenstein / sparse / trinomial irreducibles; one
  large factor plus many linear/quadratic distractors;
- seeded random differential cases vs FLINT;
- the boundary cases (`0`, `±1`, constants, `X^k`, linears).

**Metamorphic relations** (no external oracle): `factor f` vs
`factor (−f)` vs `factor (content · f)` vs `factor (f(X + k))` agree up to
the documented scalar/shift bookkeeping; multiply known factors then
re-factor → same canonical multiset; re-run with a different admissible
prime → identical result.

## Quality gates

Two gates, distinct enforcement:

- **Merge-blocking conformance + counter + wall-clock gate** (the single
  ubuntu CI job, per [SPEC/CI.md](../CI.md)). On the committed adversarial
  corpus: the invariant / differential / metamorphic checks above must
  pass; every designated fixture must finish under a *generous*
  wall-clock budget (catastrophic order-of-magnitude regressions trip it
  while runner noise does not); and the `FactorTrace` counters must
  satisfy per-fixture assertions — expected tier used, **no unexpected
  `factorTrial` fallback**, size-ordered subset count under bound, no
  small-`r` case entering `factorLattice` (or vice versa). A checked-in
  baseline JSON pins the counters and a coarse timing band. This gate is
  what prevents a future change from replacing the implementation with
  something exponentially slower "so that it can be verified"; a pure
  timing gate is gameable (pass by silently falling back, or by timing
  out only off-CI), so the counter assertions are load-bearing.
- **Scheduled Isabelle ratio** (dedicated hardware, per
  [SPEC/benchmarking.md](../benchmarking.md); informational, *not*
  merge-blocking) — the fine-grained `hex/isabelle` ratio across the
  scaling ladder, where runner noise would make a strict per-PR gate
  flaky.

## External comparators

Phase 4 declares one external comparator:

- **`verified Isabelle BZ (AFP Berlekamp_Zassenhaus; Haskell extraction of factor_int_poly via Factorization_External_Interface.thy)`**. Build via a sibling of [scripts/oracle/setup_lll_isabelle.sh](https://github.com/leanprover/hex-lll/blob/main/scripts/oracle/setup_lll_isabelle.sh) targeting the AFP `Berlekamp_Zassenhaus` session: `isabelle build -b Berlekamp_Zassenhaus`, then `isabelle export` on a wrapper theory re-exporting `factor_int_poly` to Haskell, compiled `ghc -O2` against a persistent stdin/stdout driver per [SPEC/benchmarking.md](../benchmarking.md).

  **The reference is classical exhaustive recombination, not a lattice method**: `factor_int_poly` reconstructs via `zassenhaus_reconstruction` over `subseqs` of the lifted factors (`Reconstruction.thy`), with fast constants (GHC + Karatsuba). It is exponential in the modular-factor count `r` — the same class as `factorClassical`.

  **Gating goal, by regime:**
  - small/medium `r` (reference is fast; the classical tier handles it, including the Swinnerton-Dyer ladder up to where its subset budget is exceeded): **`hex/isabelle ≤ a small constant`** — a constant-factor race won by competitive arithmetic. This is the achievable target: **parity** with the reference on every input the classical tier covers. Measured on the scheduled ratio workflow.
  - extreme `r` (beyond the classical budget, reference's exhaustive search explodes): hex is **correct** via `factorLattice` (which exhaustive search cannot be — it would explode). *Strictly beating* the reference in wall-clock here additionally requires `factorLattice` terminating before the precision cap; until that optimisation lands it is correct-but-slow, so the merge gate only checks hex finishes under cap *using `factorLattice`* (not `factorTrial`), and the "strictly beats" claim is a goal, not a current guarantee.

The fpLLL/python-flint comparators that adjacent libraries declare are *informational only* at the BZ level.

### Cross-system sweep charts — refresh after any factor-path change

The multi-system comparison (hex vs FLINT, NTL, PARI, and both verified
Isabelle/AFP factorizers) lives in
[reports/hexbz-factor-sweep.md](../../reports/hexbz-factor-sweep.md), driven by
`scripts/bench/factor_sweep.py` and charted by `scripts/plots/hexbz-cactus.py`
into the committed SVGs under `reports/figures/hexbz-*.svg` (auto-published on
the Verso manual). This is a re-runnable comparator sweep, **not CI** (see
[SPEC/benchmarking.md § Cross-system comparator sweeps](../../SPEC/benchmarking.md)).

**Standing expectation for any change to a public factor entry** (`factor`,
`factorLattice`, `factorFast`, `factorClassicalNoDecline`, or the tiers beneath
them) that could move performance: re-measure the hex entries and refresh the
charts, then **show the updated charts to the requester**. The external
comparators do *not* need re-running — the plotter merges records
newest-per-system, so a fresh hex-only record plus the committed baseline gives
correct charts:

```
# 1. Re-measure only the hex entries against the current corpus (same cutoff):
python3 scripts/bench/factor_sweep.py \
    --systems hex-factor,hex-lattice,hex-fast,hex-classical-nodecline \
    --cutoff 10 --skip-unavailable
# 2. Regenerate the charts (fresh hex curves win; external curves carried over):
python3 scripts/plots/hexbz-cactus.py
# 3. Commit the new record + regenerated SVGs; surface the charts to the requester.
```

The same newest-per-system merge covers **adding a new comparator**: to bring a
system onto the charts (e.g. PARI once `cypari2` is installed), run
`--systems <that-one>` alone and commit the small record — never re-run the
whole board to "add" one system. Re-running the external comparators is wasteful,
and the two Isabelle setups rebuild AFP session heaps (many minutes each) for no
benefit. A single-system record still cross-checks that system against
`expectedFactorDegrees`, the shared oracle every other system was validated
against.

If the corpus itself changed (`gen_factor_corpus.py`), the external systems
*must* be re-measured too — the plotter refuses to merge records with mismatched
`corpus_sha256` — and only then is a full-board run correct. Both Isabelle
drivers and the NTL driver are cached on carica, so that mandatory full
re-measure is cheap after the first build.

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

### Kernel-checked irreducibility MUST be certificate-verifying

A trusted irreducibility decision — one the kernel checks, rather than
compiled evaluation — MUST verify a certificate the kernel did not build.
The certificate is prepared by *compiled* code; the kernel checks only

- the factorization identity (the factors multiply back to `f`, over `ℤ`), and
- `checkIrreducibleCert g cert = true` for each factor `g`, against the
  soundness theorem `checkIrreducibleCert f cert = true → Irreducible f`.

`factor` / `factorLattice` and the certificate construction MUST NOT run in
the kernel — that is compiled preparation. (Pratt certificates for
irreducibility: the witness is expensive to find, cheap to check.)

Why (`native_decide` is banned): kernel reduction of the recombination is
exponential, so kernel-running `factor` terminates only up to small degree.
Any decision whose Boolean predicate calls `factor` inherits that wall and
is at most a small-degree fallback — in particular a plain `Decidable`
instance consumed by `decide` cannot satisfy this requirement, since
`decide` reduces the instance in the kernel. The certifying path is
therefore a tactic (or other elaboration-time preparation) that runs
compiled `factor` + certificate generation, reifies the certificate, and
emits the kernel check. A re-runnable benchmark SHOULD measure the frontier
— the degree at which kernel `decide` on `factor` stops terminating within
a fixed budget. Downstream specs that kernel-check `Irreducible` /
`IsIrreducible` obligations (`SPEC/Libraries/hex-roots.md`,
`SPEC/Libraries/hex-number-field.md`) depend on this.

**Mod-`p` (Berlekamp layer).** Over `F_p` there is a computable *complete*
decision `ℤ` lacks: `rabinTest`, with
`rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f)`.

- Mod-`p` irreducibility MUST be decided by a computable `rabinTest`-backed
  `Decidable` instance (Rabin on the monic normalization, degree/unit cases
  handled), so `decide +kernel` works over `F_p` — never a
  noncomputable/classical instance, never kernel-run Berlekamp factorization.
- `rabinTest` computes the Frobenius chain `x^(p^i) mod f` in the kernel, so
  it too has a frontier — further out than full factorization (no
  recombination) but still bounded. Below it, kernel-compute `rabinTest`;
  above it, verify a precomputed `Berlekamp.IrreducibilityCertificate`
  (`checkIrreducibilityCertificate`) instead. These are the `factorCerts` of
  a `ZPolyIrreducibilityCertificate`'s `PrimeFactorData` — the per-factor
  case of the `ℤ` certificate.
