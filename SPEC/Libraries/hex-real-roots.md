# hex-real-roots (real root isolation, depends on hex-poly-z)

Certified isolation of real roots of integer-coefficient polynomials.
A "real root isolation" is a dyadic interval `(a, b]` together with a
witness, dischargeable by `cbv_decide`, that exactly one simple real
root of `p ∈ ℤ[x]` lies in the interval. Initial isolation uses
Descartes' rule of signs on Möbius transforms (Uspensky's algorithm);
refinement bisects the interval and uses sign evaluation at the
midpoint plus IVT to follow the half containing the root.

The companion to [hex-roots](hex-roots.md) (complex root isolation
via BSSY): same project conventions for dyadic centres, the
`SimpleRealRoot` Quotient, the threading pattern, and Mahler/Mignotte
separation bounds — adapted for the real case (sign-variation
counting on a Möbius-transformed polynomial instead of disc-based
Pellet tests).

## Algorithm: Descartes' rule of signs + Möbius bisection (Uspensky)

Recombination is **Uspensky's algorithm**. For each candidate dyadic
interval `(a, b]` ⊆ ℝ, transform `p` by the Möbius map
`x ↦ a + (b − a)/(1 + x)` which sends `(0, ∞)` bijectively onto
`(a, b)`. The transformed
polynomial `p_M(x) := (1 + x)^(deg p) · p(a + (b − a)/(1 + x))` has
positive real roots in bijection (with multiplicity) with `p`'s real
roots in `(a, b)`. Apply Descartes' rule of signs:

```
#{ positive real roots of p_M, counted with multiplicity }
  ≤ signVariations(p_M)

#{ positive real roots of p_M, counted with multiplicity }
  ≡ signVariations(p_M)   (mod 2)
```

Reading off the count:

- `signVariations(p_M) = 0` ⟹ no real roots in `(a, b)`. Discard.
- `signVariations(p_M) = 1` ⟹ exactly one real root in `(a, b)`
  (parity argument: `0 < count ≤ 1` and `count ≡ 1 (mod 2)`).
  Emit a `RealRootIsolation`.
- `signVariations(p_M) ≥ 2` ⟹ uncertain count; bisect at the dyadic
  midpoint `m := (a + b) / 2` and recurse on `(a, m]` and `(m, b]`.

The half-open interval boundary is handled by checking `p(b) = 0`
explicitly; if `p(b) = 0`, emit `(a, b]` as an isolation with the
endpoint root, then move to subsequent intervals starting strictly
above `b`.

## Witness arithmetic is exact

For squarefree `p ∈ ℤ[x]`, the Möbius transform of `p` to the
positive ray of an integer-endpoint dyadic interval is a polynomial
in ℤ[x] (after clearing the dyadic denominators by multiplying by
`2^k · (1+x)^(deg p)`), and `signVariations` is a count of integer
sign changes through the transformed coefficient list — pure
integer arithmetic, no floats, no rationals, fully `Decidable`.
Every isolation witness in this library is a strict comparison
between integer sign-variation counts.

## Bound: LMQ

The **Local Max Quadratic (LMQ) bound** of Akritas–Strzeboński
gives an upper bound on positive real roots of `p ∈ ℤ[x]`:

```
M_LMQ(p) := 2 · max_{i : a_i < 0} (
              max_{j > i, a_j > 0}
                (−a_i / max-power-of-a_j)^{1/(j − i)}
            )
```

with the appropriate integer-arithmetic ceiling. LMQ is often an
order of magnitude tighter than the classical Cauchy bound
`1 + max_i |a_i| / |a_n|` on adversarial inputs (Mignotte clusters,
polynomials with very negative leading coefficients in low-degree
slots), which is what makes the bisection driver competitive with
Sturm-based isolation. The starting interval for the isolation
worklist is `(−M, M]` where `M := max(lmqBound p, lmqBound (p(−x)))`
— LMQ on `p` bounds positive real roots, LMQ on `p(−x)` bounds the
absolute value of negative real roots.

## Geometry: dyadic intervals on the real line

Bisection works on **dyadic intervals** `(lower, upper]` with
`lower, upper : Dyadic`, `lower < upper`. Splitting at the dyadic
midpoint `m := (lower + upper) / 2` produces two sub-intervals at
half-width.

The worklist starts with `(−M, M]` where `M` is the LMQ-derived
bound (positive part) plus the symmetric mirror (negative part).

## Contents

```lean
namespace Hex

structure DyadicInterval where
  lower : Dyadic
  upper : Dyadic
  ordered : lower < upper := by decide

structure RealRootIsolation (p : ZPoly) where
  interval : DyadicInterval
  witness  : descartesIsolatesOne p interval
  -- descartesIsolatesOne: ZPoly → DyadicInterval → Prop, decidable.
  -- True when the Möbius-transformed polynomial p_M(x) has
  -- signVariations(p_M) = 1, OR the witness extends to handle the
  -- right-endpoint case p(upper) = 0 with the strict-positive case
  -- having signVariations = 0.

/-- p has only simple real roots. Default-decidable via
    Hex.HasOnlySimpleRealRoots.decide (gcd(p, p') is a unit, so p
    is squarefree, hence has only simple roots in any extension —
    in particular, no multiple real roots). The Mathlib companion
    proves equivalence with the ℝ-coefficient version. -/
def HasOnlySimpleRealRoots (p : ZPoly) : Prop := …
instance : Decidable (HasOnlySimpleRealRoots p) := …
```

## Operations

```lean
namespace RealRootIsolation
def refine1   : RealRootIsolation p → RealRootIsolation p
def refine    : (target : Nat) → RealRootIsolation p →
                RealRootIsolation p
def refineTo  : RealRootIsolation p → (target : Nat) →
                RealRootIsolation p
end RealRootIsolation

/-- Isolate every simple real root of p (for squarefree p), bisecting
    until each interval reaches signVariations ≤ 1 or until the
    targetPrecision bound is hit. Returns `none` if any interval
    still has signVariations ≥ 2 at targetPrecision. -/
def isolate? (p : ZPoly) (h : Hex.HasOnlySimpleRealRoots p)
    (targetPrecision : Nat) : Option (Array (RealRootIsolation p))

def lmqBound    (p : ZPoly) : Dyadic   -- upper bound on positive real roots
def realRootSeparation (p : ZPoly) : Nat
```

`refine1` bisects at the dyadic midpoint `m := (a + b)/2` and uses
integer sign evaluation at endpoints + IVT to pick the half
containing the root:

- If `p(m) = 0`, the root is `m`; return `(a, m]` (half-open
  includes `m`).
- If `p(a)` and `p(m)` have opposite signs, the root is in
  `(a, m]`; return that half.
- Otherwise the root is in `(m, b]`; return that half.

`refine` and `refineTo` iterate `refine1`.

`isolate?` runs the Uspensky bisection driver: starting from the
worklist `[(−M, M]]` with `M := max(lmqBound p, lmqBound (p(−x)))`,
repeat: pop an interval; compute `signVariations(p_M)`; if 0,
discard; if 1, emit; if ≥ 2 and current precision < targetPrecision,
bisect; if ≥ 2 and precision = targetPrecision, abort with `none`.
The function terminates structurally
(`targetPrecision − currentPrecision : ℕ` strictly decreases at each
bisection). The "always-`some` at `realRootSeparation p`" guarantee
lives in `hex-real-roots-mathlib`, where the
Mahler/Mignotte real-root separation bound establishes that every
remaining interval has `signVariations ≤ 1` at that precision.

## SimpleRealRoot quotient and the threading pattern

Mirroring [hex-roots](hex-roots.md):

```lean
namespace Hex
def SimpleRealRoot (p : ZPoly) :=
    Quotient (RealRootIsolation.setoid p)

instance RealRootIsolation.setoid (p : ZPoly) :
    Setoid (RealRootIsolation p) := …

instance : DecidableEq (SimpleRealRoot p) := Quotient.decidableEq

namespace SimpleRealRoot
def mk (iso : RealRootIsolation p) : SimpleRealRoot p :=
    Quotient.mk _ iso

def out (s : SimpleRealRoot p) (prec : Nat) : RealRootIsolation p

def refine (s : SimpleRealRoot p) (target : Nat) : SimpleRealRoot p
end SimpleRealRoot
end Hex
```

Decidability of equivalence is via canonical-representative
equality, mirroring [hex-roots](hex-roots.md): canonicalise both
isolations to a fixed grid at precision `realRootSeparation p +
canonOverhead p` and compare the resulting intervals for equality.
Equivalent isolations (same root) produce the same canonical
interval; non-equivalent isolations (different roots) produce
different ones.

Note that under the half-open `(a, b]` convention, two isolations
of *distinct* roots `r₁ < r₂` can have overlapping intervals: e.g.
`iso₁ = (0.4, 0.55]` holding `r₁ = 0.5` and `iso₂ = (0.5, 0.6]`
holding `r₂ = 0.6` overlap at `(0.5, 0.55]`, with `0.5 ∉ iso₂`
(left-excluded) and `0.6 ∉ iso₁` (out of range). Equivalence is
therefore characterised by the canonicalised representatives, not
by interval overlap.

The **threading pattern** is the same as in `hex-roots`: callers
holding a `SimpleRealRoot p` should refine once and forward the
refined value rather than re-refining at each `out` call. See
[hex-roots.md §"The threading pattern"](hex-roots.md) for the
canonical exposition.

## `realRootSeparation` — sufficient `targetPrecision` for `isolate?`

```lean
def realRootSeparation (p : ZPoly) : Nat
```

For squarefree `p ∈ ℤ[x]` of degree `n` with sup-norm `‖p‖∞`, the
Mahler/Mignotte separation bound applied to *real* roots gives a
finite minimum gap between any two distinct real roots. Closed-form
integer arithmetic (uses `|disc p| ≥ 1` for squarefree integer `p`,
not the discriminant value itself).

`realRootSeparation p` is computed by the executable library so
callers can pass it as `targetPrecision` to `isolate?`. The
guarantee that `isolate? p h (realRootSeparation p) ≠ none` is a
Mathlib-bridge theorem
(`isolate?_succeeds_at_separation_precision` in
`hex-real-roots-mathlib`).

This is the analogue of [hex-roots](hex-roots.md)'s `mahlerPrec`
restricted to the real case.

## Algorithm exposition

The Uspensky bisection algorithm:

1. **Squarefree input.** Squarefreeness is a precondition,
   discharged by the `HasOnlySimpleRealRoots p` argument. `isolate?`
   does not squarefree-ify internally; callers with non-squarefree
   input compute `p_sf := p / gcd(p, p')` themselves before calling.
2. **Bound.** Compute `M := max(lmqBound p, lmqBound (p(−x)))` —
   outer bound on real-root locations.
3. **Worklist.** Initialise with `[(−M, M]]`. For each interval,
   apply Möbius transform `x ↦ a + (b − a)/(1 + x)` to get `p_M`,
   compute `signVariations(p_M)`, and dispatch:
   - `signVariations = 0`: discard.
   - `signVariations = 1`: emit a `RealRootIsolation`.
   - `signVariations ≥ 2`: bisect at `m := (a + b)/2`; push both
     halves.
   - Special case: `p(b) = 0` (right endpoint is a root of `p`).
     Emit `(a, b]` as an isolation; ensure subsequent intervals
     start strictly above `b`.
4. **Refinement.** A `RealRootIsolation` at precision `prec` is
   refined to `prec + 1` by bisecting at the midpoint `m`, evaluating
   `sign(p(m))`, and selecting the half containing the root via IVT
   (see `refine1` in §"Operations" for the decision rules).

`isolate?` terminates structurally on `targetPrecision − currentPrecision`,
which strictly decreases at each bisection; once it reaches zero, the
worklist is abandoned and the function returns `none`. Soundness of
the `some`-payload (when one is returned) is independent of the
precision budget. The Mathlib bridge separately proves that calling
`isolate?` at `targetPrecision := realRootSeparation p` is sufficient
for the worklist to drain — i.e. the result is never `none` at that
precision.

Multiple-real-root case: not supported by `isolate?`. Caller
squarefree-ifies first.

## Why Uspensky / Descartes, not Sturm

The library uses Uspensky (Descartes + Möbius bisection) rather
than the classical Sturm-sequence alternative. Several known
approaches are deliberately *not* used here:

- **Sturm's theorem + bisection.** Theoretically more robust on
  clustered roots (Sturm gives exact interval counts; Descartes
  only bounds them). Mathlib has no Sturm sequence, no Sturm
  theorem, and no subresultant pseudo-remainder chain. Mathlib
  *does* have Descartes' rule of signs
  (`Polynomial.signVariations` in
  `Mathlib.Algebra.Polynomial.RuleOfSigns`); Uspensky's bridge
  rides on existing infrastructure.
- **Vincent's theorem / VCA / VAS** (continued-fraction-based
  isolation). Faster than Uspensky in practice (used by FLINT,
  Mathematica, SageMath). Vincent's theorem is absent from
  Mathlib.
- **Speculative Newton refinement** (quadratic convergence on top
  of any bisection driver). Out of scope for this library.

## Layered file organisation

- `HexRealRoots/Basic.lean` — types: `DyadicInterval`,
  `RealRootIsolation`, `Hex.HasOnlySimpleRealRoots`. Setoid +
  Quotient `SimpleRealRoot p` + decidable equality. `mk` and `out`.
- `HexRealRoots/Mobius.lean` — Möbius transformation of polynomials:
  `mobiusTransform p a b` returns the integer polynomial
  `(1+x)^(deg p) · p(a + (b−a)/(1+x))` (after clearing dyadic
  denominators).
- `HexRealRoots/Descartes.lean` — `descartesCount p interval` =
  `signVariations(mobiusTransform p ...)`; `descartesIsolatesOne`
  predicate and `Decidable` infrastructure.
- `HexRealRoots/Bounds.lean` — `lmqBound`.
- `HexRealRoots/Separation.lean` — `realRootSeparation`.
- `HexRealRoots/Refine.lean` — `refine1`, `refine`, `refineTo`,
  `refineTo_respects_equiv`, `SimpleRealRoot.refine`. Threading-
  pattern guidance on `SimpleRealRoot.refine`'s docstring.
- `HexRealRoots/Isolate.lean` — `isolate?` driver (Option-returning,
  parametrised by `targetPrecision`; structural termination by
  precision-budget descent).
- `HexRealRoots/Conformance.lean`, `HexRealRoots/Bench.lean`,
  `HexRealRoots/EmitFixtures.lean` — standard testing trio.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md), tiered:

- *core* (Lean-only, runs on every push):
  - Linear: `x − 5` (one root at 5).
  - `x² − 1` (roots at ±1).
  - `x² + 1` (no real roots).
  - `x³ − x` (roots at −1, 0, 1).
  - `x³ − x − 1` (one real root, ≈ 1.3247).
  - Chebyshev `T_5(x) = 16x⁵ − 20x³ + 5x` (5 roots in `[−1, 1]`).
  - Cyclotomic `Φ_5` (deg 4, no real roots).
  - `(x − 1)²(x + 1)` — multiple root: `isolate?` rejects via
    `HasOnlySimpleRealRoots = false`.
- *ci* (CI, with external oracle): 30 degree-15 polynomials with
  small random integer coefficients; expected outputs from SageMath
  or python-flint.
- *local* (developer-driven): adversarial families designed to
  stress Uspensky's known weak spot — clustered-root cases:
  - **Mignotte** `xⁿ − (a·x − 1)²` for `n ∈ {10, 20}` and
    `a ∈ {1000, 10⁶}` (close real roots near `1/a`). Uspensky pays
    extra here because Descartes' bound is loose on tight clusters.
  - **Wilkinson 20** (roots at `1, 2, …, 20`; condition number
    explodes, but distinct roots so Uspensky terminates).
  - **Chebyshev** `T_n` for `n ∈ {20, 50}` (real roots cluster near
    `±1`).

External oracles: SageMath
(`R.<x> = ZZ[]; (p).real_roots()`), python-flint
(`fmpz_poly` real-root API), FLINT/Arb
(`arb_poly_isolate_real_roots`).

## Complexity contract

For Uspensky's algorithm on degree-`n` squarefree `p` with sup-norm
`‖p‖∞`:

- `lmqBound p`: `O(n²)` integer operations (the double-max).
- Möbius transform of `p` to a candidate interval: `O(n²)` integer
  multiplications; intermediate coefficient size `O(n · log ‖p‖∞)`
  per transform.
- `signVariations` on the transformed polynomial: `O(n)` integer
  sign comparisons.
- `realRootSeparation p`: `O(n · log ‖p‖∞)` integer operations.
- `isolate? p h (realRootSeparation p)` worst case: `O(n · realRootSeparation p)` Möbius+
  Descartes evaluations, dominated by the Möbius transform per
  step. Concretely, `Õ(n^4 · log² ‖p‖∞)` bit operations on benign
  inputs; potentially `Õ(n^4 · realRootSeparation²)` on Mignotte
  clusters where Descartes' bound is loose.

This is the same asymptotic class as Sturm + bisection (both are
`Õ(n^4 · h^2)`). Uspensky's actual constants are typically
*better* on benign inputs because Möbius transforms are simpler
than Sturm-sequence evaluations, but *worse* on tight clusters
because Descartes' bound stays > 1 for longer.

## Time budgets (Phase 4 validation)

Rough first guesses, refined against SageMath / Arb on the same
fixtures during Phase 4:

- Degree 10, prec 32: < 1 second.
- Degree 50, prec 64: < 10 seconds.
- Degree 100, prec 128: < 1 minute.

Adversarial Mignotte clusters may exceed these; bench will surface
the actual constants.

## References

- Descartes, R. *La Géométrie* (1637) — original sign-variation
  rule.
- Vincent, A. J. H. *Sur la résolution des équations numériques*
  (1834) — Vincent's theorem (used as the termination story for
  classical Uspensky variants; not formalised here, where
  Mignotte separation provides termination instead).
- Uspensky, J. V. *Theory of Equations* (1948) — the
  Möbius-bisection real-root isolation algorithm bears his name.
- Akritas, A. G. *Elements of Computer Algebra with Applications*
  (1989) — modern presentation of Uspensky and refinements.
- Akritas, A. G.; Strzeboński, A. W.; Vigklas, P. S. *Improving
  the performance of the continued fractions method using new
  bounds of positive roots.* Nonlinear Analysis 13 (2008) — the
  LMQ bound used here.
- Basu, S.; Pollack, R.; Roy, M.-F. *Algorithms in Real Algebraic
  Geometry.* Springer, 2nd ed., 2006. Chapter 10 covers Uspensky
  and Descartes-based isolation in detail.
