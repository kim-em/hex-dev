# hex-real-roots (real root isolation, depends on hex-poly-z + hex-resultant)

Certified isolation of real roots of integer-coefficient polynomials.
A "real root isolation" is a dyadic interval `(a, b]` together with a
witness, dischargeable by `cbv_decide`, that exactly one simple real
root of `p ∈ ℤ[x]` lies in the interval. Refinement bisects the
interval at the dyadic midpoint, recomputes the Sturm count on each
half, and follows the half containing the root.

The companion to [hex-roots](hex-roots.md) (complex root isolation
via BSSY): same project conventions for dyadic centres, the
`SimpleRealRoot` Quotient, the threading pattern, and Mahler/Mignotte
separation bounds — adapted for the real case (sign-separation
instead of disc-separation, bisection instead of subdivision-and-
gluing).

## Witness arithmetic is exact

Sturm's theorem: for squarefree `p ∈ ℤ[x]`, the **Sturm sequence**
`s_0 := p, s_1 := p', s_{i+1} := −rem(s_{i−1}, s_i)` evaluated at
real `a` yields a sequence of values whose sign-change count
`V(a)` satisfies

```
V(a) − V(b)  =  #{ real roots of p in the interval (a, b] }
```

for any `a < b` such that `p(a) ≠ 0`, `p(b) ≠ 0`. Every `V(a) − V(b)`
in this library is computed by evaluating the Sturm sequence at
exact dyadic points and counting integer sign changes — `Decidable`
with no error budget.

## Sturm sequence via subresultants (integer arithmetic throughout)

The sequence is computed via the **subresultant pseudo-remainder
sequence** from [hex-resultant](hex-resultant.md)'s
`subresultantChain`, with Sylvester–Habicht sign-flip bookkeeping so
the chain delivers the Sturm sequence's sign-change behaviour. This
keeps every intermediate coefficient in ℤ — no rational arithmetic,
no denominator clearing, no floating point. Computing
`V(a)` reduces to evaluating each `s_i` at the dyadic point `a` (an
integer multiplied by a power of two), reading off the integer sign,
and counting flips.

Rationale: ordinary remainder Sturm sequences over ℚ require
denominator tracking; the subresultant variant absorbs the
pseudo-division blow-up into tracked scale factors with sharp bounds
(the "fundamental theorem of subresultants"), giving better
asymptotic coefficient size than naive integer pseudo-division. The
machinery exists in `hex-resultant`; the dependency is natural.

## Geometry: dyadic intervals on the real line

Bisection works on **dyadic intervals** `(lower, upper]` with
`lower, upper : Dyadic`, `lower < upper`. Splitting at the dyadic
midpoint `m := (lower + upper) / 2` produces two sub-intervals at
half-width.

The **Cauchy bound** `M := 1 + max_i |a_i| / |a_n|` (rounded up to a
dyadic) bounds every real root of `p` in `[−M, M]`; the worklist
starts with `(−M, M]`.

## Contents

```lean
namespace Hex

structure DyadicInterval where
  lower : Dyadic
  upper : Dyadic
  ordered : lower < upper := by decide

structure SimpleRealRootIsolation (p : ZPoly) where
  interval : DyadicInterval
  witness  : sturmCount p interval = 1
  -- sturmCount: ZPoly → DyadicInterval → ℕ; computed via integer
  -- subresultant chain + dyadic evaluation. The witness type is
  -- `Decidable Prop`, dischargeable by cbv_decide on a fully-
  -- elaborated SimpleRealRootIsolation value.

/-- p has only simple real roots. Default-decidable via
    Hex.HasOnlySimpleRealRoots.decide (gcd(p, p') is a unit, so p
    is squarefree, hence has only simple roots in any extension —
    in particular, no multiple real roots). The Mathlib companion
    proves equivalence with the ℝ-coefficient version. -/
def HasOnlySimpleRealRoots (p : ZPoly) : Prop := …
instance : Decidable (HasOnlySimpleRealRoots p) := …
```

`SimpleRealRootIsolation p` carries one *simple* real root in its
interval — `Simple` because the witness pins the Sturm count at 1
(not 0, not ≥ 2). For inputs with multiple roots the bisection never
satisfies the witness around the multiple root, and `isolate`
refuses such inputs (see Operations).

## Operations

```lean
namespace SimpleRealRootIsolation
def refine1?  : SimpleRealRootIsolation p → Option (SimpleRealRootIsolation p)
def refine?   : (target : Nat) → SimpleRealRootIsolation p →
                Option (SimpleRealRootIsolation p)
def refineTo  : SimpleRealRootIsolation p → (target : Nat) →
                SimpleRealRootIsolation p
end SimpleRealRootIsolation

/-- Isolate every simple real root of p (for squarefree p). -/
def isolate (p : ZPoly) (h : Hex.HasOnlySimpleRealRoots p)
    (atom_prec : Nat) : Array (SimpleRealRootIsolation p)

def cauchyBound (p : ZPoly) : Dyadic
def realRootSeparation (p : ZPoly) : Nat
```

`refine1?` bisects the current interval at the dyadic midpoint, runs
the Sturm count on each half, and returns the half whose count is 1
(the other half has count 0; the case of count 2 cannot occur on a
SimpleRealRootIsolation by the witness invariant, modulo tie-cases
at the midpoint — see "midpoint hits a root" below). `refine?` and
`refineTo` iterate to a target precision.

`isolate` runs the Sturm bisection driver: starting with the Cauchy
interval `(−M, M]`, repeatedly split intervals whose Sturm count
exceeds 1; emit intervals with count 1; discard intervals with count
0. Termination by `realRootSeparation p` (Mahler/Mignotte real-root
bound).

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
    Quotient (SimpleRealRootIsolation.setoid p)

instance SimpleRealRootIsolation.setoid (p : ZPoly) :
    Setoid (SimpleRealRootIsolation p) := …

instance : DecidableEq (SimpleRealRoot p) := Quotient.decidableEq

namespace SimpleRealRoot
def mk (iso : SimpleRealRootIsolation p) : SimpleRealRoot p :=
    Quotient.mk _ iso

def out (s : SimpleRealRoot p) (prec : Nat) : SimpleRealRootIsolation p

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
canonical exposition; the rules here are identical with `Real` /
`SimpleRealRoot` substituted for the complex names.

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

The Sturm bisection algorithm:

1. **Squarefree-ify.** `p_sf := p / gcd(p, p')`. Provided as a
   precondition via `HasOnlySimpleRealRoots`; not mutated by the
   algorithm itself. (Internally `isolate` may call the gcd routine
   defensively; the SPEC contract requires squarefree input.)
2. **Sturm sequence.** Compute the integer Sturm sequence via
   `subresultantChain` from `hex-resultant`, with Sylvester–Habicht
   sign-flip applied so the resulting sequence has the sign-change
   semantics of the classical Sturm sequence. Pre-computed once.
3. **Cauchy bound.** Compute `M := cauchyBound p` (a dyadic).
4. **Total root count.** Compute `N := V(−M) − V(M)`.
5. **Bisection driver.** Worklist initialised with `(−M, M]`. Loop:
   pop an interval `(a, b]`; compute `n := V(a) − V(b)`; if `n = 0`,
   discard; if `n = 1`, emit a `SimpleRealRootIsolation`; if `n > 1`,
   bisect at `m := (a + b) / 2` and push both halves. Terminates
   when worklist is empty.
6. **Refinement.** A `SimpleRealRootIsolation` at precision `prec`
   can be refined to `prec + 1` by bisecting and re-running the
   Sturm count on the half containing the root.

Only-simple-roots check via `HasOnlySimpleRealRoots`: `gcd(p, p')`
is a unit. Squarefree `p` ⟹ no multiple roots in any field ⟹ in
particular no multiple real roots. The converse fails (squarefree
in ℂ but with double real roots is impossible, so the converse
holds for ℝ-roots; mathlib companion makes this precise).

Multiple-real-root case: not supported by `isolate`. The bisection
would never reduce a count-2 interval below 2 around a real double
root. Caller squarefree-ifies first.

## Layered file organisation

- `HexRealRoots/Basic.lean` — types: `DyadicInterval`,
  `SimpleRealRootIsolation`, `Hex.HasOnlySimpleRealRoots`. Setoid +
  Quotient `SimpleRealRoot p` + decidable equality. `mk` and `out`.
- `HexRealRoots/Sturm.lean` — `sturmSequence` (subresultant-based
  with Sylvester–Habicht sign flip), `sturmCount` (sign-change
  difference at a dyadic interval's endpoints), and the Sturm
  count's Decidable infrastructure.
- `HexRealRoots/Cauchy.lean` — `cauchyBound`.
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
- *local* (developer-driven): adversarial families — Mignotte
  `xⁿ − (a·x − 1)²` for `n ∈ {10, 20}` and `a ∈ {1000, 10⁶}`,
  Wilkinson 20, Chebyshev `T_n` for `n ∈ {20, 50}`.

External oracles: SageMath
(`R.<x> = ZZ[]; (p).real_roots()`), python-flint
(`fmpz_poly` real-root API), FLINT/Arb (`arb_poly_isolate_real_roots`).

## Complexity contract

- `cauchyBound p`: `O(n)` integer comparisons + one division.
- `sturmSequence p`: `O(n)` polynomial pseudo-division steps via
  `hex-resultant.subresultantChain`; coefficient size bounded by
  the subresultant theorem's `O(n · log ‖p‖∞)`.
- `sturmCount p (a, b)`: `O(n)` polynomial evaluations at two
  dyadic points + `O(n)` integer sign comparisons.
- `realRootSeparation p`: `O(n · log ‖p‖∞)` integer operations.
- `isolate p (atom_prec)` for degree-`n` squarefree `p` with
  well-separated roots: heuristically `O(n³ · atom_prec)` integer
  operations. Worst case bounded by `realRootSeparation`, which is
  exponential in `n` for arbitrary-coefficient inputs but
  polynomial in `‖p‖∞` for fixed `n`.

## Time budgets (Phase 4 validation)

Rough first guesses, refined against SageMath / Arb on the same
fixtures during Phase 4:

- Degree 10, prec 32: < 1 second.
- Degree 50, prec 64: < 10 seconds.
- Degree 100, prec 128: < 1 minute.

## References

- Sturm, J. C. F. *Mémoire sur la résolution des équations
  numériques.* Bull. Sci. Math. 11 (1829) 419–425. The original
  theorem.
- Sylvester, J. J. *On a theory of the syzygetic relations of two
  rational integral functions.* Phil. Trans. R. Soc. London 143
  (1853) 407–548. Sign-modified subresultant chain.
- Habicht, W. *Eine Verallgemeinerung des Sturmschen
  Wurzelzählverfahrens.* Comment. Math. Helv. 21 (1948) 99–116.
  Generalises Sturm to subresultant-based chains.
- Marden, M. *Geometry of Polynomials.* AMS Math. Surveys 3, 2nd
  ed., 1966. Modern textbook treatment of Sturm.
- Basu, S.; Pollack, R.; Roy, M.-F. *Algorithms in Real Algebraic
  Geometry.* Springer, 2nd ed., 2006. Comprehensive: Sturm + sign
  matrices + cylindrical decomposition. **The reference** for this
  library and its sibling `hex-sturm`.
- Geddes, K. O.; Czapor, S. R.; Labahn, G. *Algorithms for Computer
  Algebra.* Kluwer, 1992. §8 covers Sturm with subresultants and
  the standard root-isolation drivers.
