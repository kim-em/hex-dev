# hex-real-roots (real root isolation, depends on hex-poly-z)

Certified isolation of real roots of integer-coefficient polynomials.
A "real root isolation" is a dyadic interval `(a, b]` together with a
witness, dischargeable by `cbv_decide`, that exactly one simple real
root of `p ∈ ℤ[x]` lies in the interval. Refinement bisects the
interval at the dyadic midpoint, recomputes the Descartes
sign-variation count after a Möbius transform, and follows the half
containing the root.

The companion to [hex-roots](hex-roots.md) (complex root isolation
via BSSY): same project conventions for dyadic centres, the
`SimpleRealRoot` Quotient, the threading pattern, and Mahler/Mignotte
separation bounds — adapted for the real case (sign-variation
counting on a Möbius-transformed polynomial instead of disc-based
Pellet tests).

## Algorithm: Descartes' rule of signs + Möbius bisection (Uspensky)

Pinned: **Uspensky's algorithm**. For each candidate dyadic interval
`(a, b]` ⊆ ℝ, transform `p` by the Möbius map `x ↦ a + (b − a)/(1 + x)`
which sends `(0, ∞)` bijectively onto `(a, b)`. The transformed
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

## Bounds: Cauchy and LMQ

The **Cauchy bound** `M_C := 1 + max_i |a_i| / |a_n|` (rounded up to
a dyadic) bounds every real root of `p` in `[−M_C, M_C]` and is
the conservative starting interval for the worklist.

The **Local Max Quadratic (LMQ) bound** of Akritas–Strzeboński
gives a tighter upper bound on positive real roots:

```
M_LMQ(p) := 2 · max_{i : a_i < 0} (
              max_{j > i, a_j > 0}
                (−a_i / max-power-of-a_j)^{1/(j − i)}
            )
```

with the appropriate integer-arithmetic ceiling. LMQ is often an
order of magnitude tighter than Cauchy on adversarial inputs
(Mignotte clusters, polynomials with very negative leading
coefficients in low-degree slots). The library uses LMQ for the
positive-root upper bound (and `−LMQ(p(−x))` for the negative-root
lower bound), with Cauchy as the fallback / sanity bound.

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
def refine1?  : RealRootIsolation p → Option (RealRootIsolation p)
def refine?   : (target : Nat) → RealRootIsolation p →
                Option (RealRootIsolation p)
def refineTo  : RealRootIsolation p → (target : Nat) →
                RealRootIsolation p
end RealRootIsolation

/-- Isolate every simple real root of p (for squarefree p). -/
def isolate (p : ZPoly) (h : Hex.HasOnlySimpleRealRoots p)
    (atom_prec : Nat) : Array (RealRootIsolation p)

def cauchyBound (p : ZPoly) : Dyadic
def lmqBound    (p : ZPoly) : Dyadic   -- upper bound on positive real roots
def realRootSeparation (p : ZPoly) : Nat
```

`refine1?` bisects at the dyadic midpoint, runs Möbius+Descartes on
each half, and returns the half whose `signVariations` is odd
(typically `1`; the case of `≥ 3` cannot occur on a
`RealRootIsolation` by the witness invariant — the existing witness
guarantees the parent interval contained exactly one root).
`refine?` and `refineTo` iterate.

`isolate` runs the Uspensky bisection driver: starting from the
worklist `[(−M, M]]` with `M := max(lmqBound, cauchyBound)`, repeat:
pop an interval; compute `signVariations(p_M)`; if 0, discard; if 1,
emit; if ≥ 2, bisect. Termination by `realRootSeparation p`
(Mahler/Mignotte real-root bound).

### Midpoint hits a root

If the dyadic midpoint `m` happens to satisfy `p(m) = 0`, the
half-open interval convention `(a, b]` places that root in
`(a, m]` (left half) by inclusion of the right endpoint. `p(m) = 0`
is an integer-arithmetic check, so this case is detected exactly
and resolved deterministically. (For squarefree `p` this happens
only at finitely many dyadic points, so refinement always makes
progress.)

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

Decidability of equivalence: refine both isolations to precision
`realRootSeparation p`; then either intervals overlap (→ same
root) or they're disjoint (→ different roots).

The **threading pattern** is the same as in `hex-roots`: callers
holding a `SimpleRealRoot p` should refine once and forward the
refined value rather than re-refining at each `out` call. See
[hex-roots.md §"The threading pattern"](hex-roots.md) for the
canonical exposition.

## `realRootSeparation` — termination bound

```lean
def realRootSeparation (p : ZPoly) : Nat
```

For squarefree `p ∈ ℤ[x]` of degree `n` with sup-norm `‖p‖∞`, the
Mahler/Mignotte separation bound applied to *real* roots gives a
finite minimum gap between any two distinct real roots. Closed-form
integer arithmetic (uses `|disc p| ≥ 1` for squarefree integer `p`,
not the discriminant value itself).

This is the analogue of [hex-roots](hex-roots.md)'s `mahlerPrec`
restricted to the real case.

## Algorithm exposition

The Uspensky bisection algorithm:

1. **Squarefree-ify.** `p_sf := p / gcd(p, p')`. Provided as a
   precondition via `HasOnlySimpleRealRoots`; not mutated by the
   algorithm itself. (Internally `isolate` may call the gcd routine
   defensively; the SPEC contract requires squarefree input.)
2. **Bounds.** Compute `M := max(lmqBound p, cauchyBound p)` —
   conservative outer bound on real-root locations.
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
   refined to `prec + 1` by bisecting and re-running Möbius+Descartes
   on the half containing the root.

Termination by `realRootSeparation p` plus interval-halving: any
two distinct real roots are eventually placed in disjoint intervals
once interval width drops below `2^{-realRootSeparation p}`, after
which each interval has `signVariations ≤ 1`.

Multiple-real-root case: not supported by `isolate`. Caller
squarefree-ifies first.

## Why Uspensky / Descartes, not Sturm

Pinned: Uspensky (Descartes + Möbius bisection). Deliberately *not*
implemented in this round:

- **Sturm's theorem + bisection.** The classical alternative.
  Theoretically more robust on clustered roots (Sturm gives exact
  interval counts; Descartes only bounds them). Rejected because
  Mathlib has no Sturm sequence, no Sturm theorem, and no
  subresultant pseudo-remainder chain — the bridge would require
  multi-month formalisation work. Mathlib *does* have Descartes'
  rule of signs (`Polynomial.signVariations` in
  `Mathlib.Algebra.Polynomial.RuleOfSigns`), so Uspensky's bridge
  proof rides on existing infrastructure.
- **Vincent's theorem / VCA / VAS** (continued-fraction-based
  isolation). Faster than Uspensky in practice (used by FLINT,
  Mathematica, SageMath). Rejected because Vincent's theorem is
  absent from Mathlib; formalising it is a multi-month side quest
  before any tactic-level payoff.
- **Speculative Newton refinement** (quadratic convergence on top
  of any bisection driver). Worth considering as a future
  refinement; not in this SPEC.

If a future library or tactic needs reusable interval-root-count
primitives (which Sturm provides natively but Uspensky does not),
Sturm could be added then with full formalisation cost. Until that
demand exists, Uspensky's narrower payoff is the right scope.

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
- `HexRealRoots/Bounds.lean` — `cauchyBound`, `lmqBound`.
- `HexRealRoots/Separation.lean` — `realRootSeparation`.
- `HexRealRoots/Refine.lean` — `refine1?`, `refine?`, `refineTo`,
  `refineTo_respects_equiv`, `SimpleRealRoot.refine`. Threading-
  pattern guidance on `SimpleRealRoot.refine`'s docstring.
- `HexRealRoots/Isolate.lean` — `isolate` driver.
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
  - `(x − 1)²(x + 1)` — multiple root: `isolate` rejects via
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

- `cauchyBound p`: `O(n)` integer comparisons.
- `lmqBound p`: `O(n²)` integer operations (the double-max).
- Möbius transform of `p` to a candidate interval: `O(n²)` integer
  multiplications; intermediate coefficient size `O(n · log ‖p‖∞)`
  per transform.
- `signVariations` on the transformed polynomial: `O(n)` integer
  sign comparisons.
- `realRootSeparation p`: `O(n · log ‖p‖∞)` integer operations.
- `isolate p` worst case: `O(n · realRootSeparation p)` Möbius+
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
