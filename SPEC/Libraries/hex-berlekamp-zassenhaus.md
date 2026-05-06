# hex-berlekamp-zassenhaus (the capstone)

Depends on hex-berlekamp + hex-hensel + hex-lll.

Complete factoring of univariate polynomials over `Z`.

This library should expose one stable public factoring API. The Phase 1
implementation of `recombine` is LLL-based: lifted local factors are
encoded as a lattice via `hex-lll`, short vectors recovered, and integer
factors reconstructed from those short vectors. Exhaustive subset
recombination is admissible only as a small-input fallback or as a
conformance-test oracle, never as the production code path.

The public API should accept arbitrary input polynomials and normalize
internally: extract content, remove powers of `X`, and reduce to the
primitive square-free case before running the Berlekamp-Zassenhaus
pipeline. The output is an `Array ZPoly` of primitive factors. Factor
order is operationally the array order, but the mathematical contract is
through product and membership rather than any semantic significance of
that order.

**Suggested top-level API:**
```lean
def factorWithBound (f : ZPoly) (B : Nat) : Array ZPoly
def factor (f : ZPoly) : Array ZPoly
```

`factorWithBound` is the core computational interface for conditional
correctness statements. `factor` is the default wrapper that computes and
uses the library's chosen coefficient bound internally.

**Prime selection sub-API:**
```lean
def isGoodPrime (f : ZPoly) (p : Nat) : Bool
def choosePrime (f : ZPoly) : Nat
```

`isGoodPrime` expresses the mathematical admissibility condition for the
modular reduction prime: at minimum `p ∤ lc(f)` and `f mod p` is
square-free. `choosePrime` is the default total heuristic chooser. It
should search through a small fixed number of admissible small primes,
factor `f mod p` for each, and choose the prime with the fewest modular
factors, breaking ties toward the smallest prime.

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
recombination. The LLL-based recombination needs extra internal
metadata (a basis matrix encoding the lifted factors as a sublattice
of `Z^n`, plus the short-vector results); these live in dedicated
internal helper records inside the recombination implementation,
rather than expanding `LiftData` itself.

Suggested stage helpers:
```lean
def choosePrimeData (f : ZPoly) : PrimeChoiceData
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData
def recombine (f : ZPoly) (d : LiftData) : Array ZPoly
```

`recombine` is a named public helper. Its Phase 1 implementation is
LLL-based: the lifted factors in `d.liftedFactors` are encoded as a
lattice basis (one basis row per local factor, columns indexed by
coefficient positions truncated to `p^k`), `hex-lll`'s reduction +
short-vector surface is invoked to recover candidate short vectors,
and each short vector is decoded into a candidate `ZPoly` factor whose
divisibility against the current target is verified before acceptance.
The signature of `recombine` is fixed and does not carry a strategy
parameter; an exhaustive subset path may be retained as an internal
fallback for inputs with very few local factors and as an oracle in
conformance tests, but it is not the production code path and is not
part of the public surface.

**Pipeline:**
1. Normalize `f` (content, powers of `X`, square-free part)
2. Choose a good prime `p` and factor `f mod p`
3. Hensel lift the modular factors to `mod p^k` for a sufficiently large
   bound-dependent `k` (using `multifactorLiftQuadratic` from `hex-hensel`)
4. Encode the lifted factors as a lattice basis, run `hex-lll`'s
   reduction + short-vector recovery, and decode short vectors into
   candidate integer factors of `f`, verifying divisibility before
   acceptance

The Phase 1 contract for stage 4 is the LLL-based recombination
sketched above; it is the production code path and is what Phase 4
benchmarks register as the recombination hot path. Treating LLL
recombination as "later" or as an optional optimisation is
incompatible with the polynomial-time complexity model declared for
the pipeline. An exhaustive subset fallback may be retained as an
internal small-input shortcut and as a conformance-test oracle, but
never as the production path.

**Precision selection.** The Hensel-lift target precision `k` is
chosen *adaptively*, not set once to the worst-case Mignotte bound.
The pipeline starts with a small initial `k₀` (e.g. constant or
`O(log deg f)`), invokes `multifactorLiftQuadratic` to that
precision, and calls `recombine`. If `recombineLLL?` returns `none`,
the pipeline doubles `k` and retries the lift + recombination.
Doubling continues until either recombination succeeds or `k`
exceeds the Mignotte upper bound from
`ZPoly.defaultFactorCoeffBound`, in which case the pipeline reports
the input as irreducible — the Mignotte bound being a mathematical
guarantee that no factor with smaller coefficients exists.

The conditional correctness contract `factor_product_of_bound` is
unchanged: implementations may pick any `k₀` and any escalation
schedule, provided the upper bound is the Mignotte bound and the
loop terminates. `recombineLLL?`'s `Option (Array ZPoly)` return
type is the escalation signal: `none` means "this `k` was not
sufficient, escalate".

**Conditional correctness (proved in this library, no Mathlib):**

The algorithm's correctness is proved conditionally on the coefficient
bound being valid. The key conditional theorem:
```lean
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, |g.coeff i| ≤ B) :
    Array.foldl (· * ·) 1 (factorWithBound f B) = f
```

This library should also contain the computational invariants needed by
downstream stages, for example:
- `isGoodPrime` soundness with respect to the modular square-free
  preconditions needed by hex-berlekamp
- correctness of `choosePrimeData`
- correctness of the Hensel-lift stage under the explicit bound and prime
  data
- recombination product preservation under the lifted-factor hypotheses

These are computational pipeline theorems. The heavier abstract-algebraic
results remain in `hex-berlekamp-zassenhaus-mathlib`.

**Certificate structures for Z[x] irreducibility:**
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

Suggested soundness split:
- `hex-berlekamp-zassenhaus` proves the computational soundness of the
  checker data flow and degree-obstruction computation
- `hex-berlekamp-zassenhaus-mathlib` proves
  `checkIrreducibleCert f cert = true → Irreducible f`
