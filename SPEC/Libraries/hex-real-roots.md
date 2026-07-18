# hex-real-roots (real root isolation, depends on hex-poly-z)

Certified isolation of the real roots of integer-coefficient
polynomials. A real root isolation is a half-open dyadic interval
`(lower, upper]` together with a witness, dischargeable by `decide`,
that exactly one real root of `p ∈ ℤ[x]` lies in the interval. The
witness is a **Sturm count**: the sign-variation difference of the
Sturm chain of `p` evaluated at the two endpoints, which counts the
roots in the interval exactly.

Isolation runs two engines over the same output type:

- a **Descartes search** (Collins-Akritas bisection: Descartes' rule
  of signs applied to Möbius transforms of `p`), which is fast but
  whose termination bound is not certified here, and
- a **Sturm search** (bisection on exact Sturm counts), which is
  slower per node but provably terminates at a computable depth.

Every emitted isolation carries a Sturm-count witness regardless of
which engine found it, and every full output is checked against the
exact total root count. The Descartes engine therefore contributes
speed and no trust. The correctness and completeness theorems in
[hex-real-roots-mathlib](hex-real-roots-mathlib.md) rest on Sturm
counts alone.

The companion library to [hex-roots](hex-roots.md) (complex root
isolation): the same conventions for dyadic data, exact witness
arithmetic, fueled `Option`-valued drivers, and the
quotient-by-overlap identity of a root.

## Exact witness arithmetic

A `ZPoly` evaluated at a dyadic point by Horner's rule yields an
exact `Dyadic` value, so the sign of `p(x)` at dyadic `x` is exact.
Every witness is an equality or comparison between integer counts,
and is `Decidable`: no floats, no interval arithmetic, no error
budget. The one rational computation in the library is hex-poly-z's
`SquareFreeRat` test in the drivers; witnesses never contain
rational data.

**Sign variations.** For a list of exact values, `signVar` counts the
sign changes of the nonzero entries, skipping zeros: the variation
count of `(+, 0, −)` is 1. All variation counts below use this
zero-skipping convention.

## The Sturm chain

```lean
namespace Hex

/-- The Sturm chain of `p`: `s₀ = primitivePart p`,
    `s₁ = primitivePart p'`, and
    `s_{i+1} = −primitivePart (spem s_{i−1} s_i)` while the remainder
    is nonzero, where `spem` is the pseudo-remainder with its
    multiplier forced positive. Each element is a positive rational
    multiple of the classical signed-remainder chain of `(p, p')`
    over `ℚ`, which is the invariant the counting theorem needs. -/
def sturmChain (p : ZPoly) : Array ZPoly
```

The sign-managed pseudo-remainder `spem f g` computes the standard
pseudo-remainder `prem f g = (lc g)^δ · f mod g` with
`δ = deg f − deg g + 1`, then negates the result when `(lc g)^δ < 0`.
The output is a positive integer multiple of the rational remainder
`f mod g`, so dividing by the (positive) content and negating gives
the next chain element with the correct sign. Coefficients stay in
`ℤ` throughout, and the content division keeps them as small as any
pseudo-remainder scheme allows.

The last chain element is a nonzero constant exactly when `p` is
squarefree (of positive degree).

**Input contract.** The drivers do not take hypotheses; they classify
every input explicitly:

- `p = 0`: `none`. (`SquareFreeRat 0` holds vacuously through the
  gcd size test, so the drivers check `p ≠ 0` separately.)
- `p` a nonzero constant: `some` with an empty isolation array,
  matching `rootCount p = 0`.
- `p` of positive degree, not `SquareFreeRat`: `none`. Callers use
  `Hex.ZPoly.squareFreeCore` first.
- `p` of positive degree and squarefree: complete isolation.

`sturmChain`, `rootBound`, `sepPrec`, and `isolationDepth` are total
functions. For `deg p ≤ 0` they return the empty chain, `1`, `0`,
and `depthSlack` respectively, and no theorem reads those values.

## Sturm counts

```lean
/-- Zero-skipping sign variations of the chain evaluated at a dyadic
    point. Exact Horner evaluation of every chain element. -/
def sturmVarAt (chain : Array ZPoly) (x : Dyadic) : Nat

/-- Variations at −∞ and +∞, read off the leading coefficients and
    the degree parities. No evaluation. -/
def sturmVarNegInf (chain : Array ZPoly) : Nat
def sturmVarPosInf (chain : Array ZPoly) : Nat

/-- The number of real roots of `p` in `(I.lower, I.upper]`, as
    certified by the Sturm chain. An `Int` by definition. The
    companion proves it equals the root count (in particular, that it
    is nonnegative) for squarefree `p`. -/
def sturmCount (p : ZPoly) (I : DyadicInterval) : Int :=
  sturmVarAt (sturmChain p) I.lower − sturmVarAt (sturmChain p) I.upper

/-- The total number of real roots of `p`. -/
def rootCount (p : ZPoly) : Nat :=
  sturmVarNegInf (sturmChain p) − sturmVarPosInf (sturmChain p)
```

The zero-skipping convention makes the count match the half-open
interval exactly: a root at `upper` is counted (the variation between
`s₀` and `s₁` that exists just left of the root disappears at it),
and a root at `lower` is not. This is why isolations are half-open on
the left: interval arithmetic, bisection, and counting all agree on
`(lower, upper]` with no endpoint case analysis in the drivers.

The drivers compute the chain once per polynomial and memoise
`sturmVarAt` per endpoint, and bisection reuses each endpoint's
variation count in both child intervals.

## Contents

```lean
structure DyadicInterval where
  lower : Dyadic
  upper : Dyadic
  lt    : lower < upper

/-- Exactly one real root of `p` lies in `(interval.lower,
    interval.upper]`. -/
structure RealRootIsolation (p : ZPoly) where
  interval  : DyadicInterval
  count_one : sturmCount p interval = 1

/-- A complete isolation run: pairwise-disjoint isolations, in
    increasing order, one per real root of `p`. Both invariants are
    decidable data, so for squarefree `p` the structure certifies
    itself no matter which engine produced it. -/
structure RealRootIsolations (p : ZPoly) where
  isolations : Array (RealRootIsolation p)
  ordered    : ∀ i j : Fin isolations.size, i < j →
                 isolations[i].interval.upper ≤
                   isolations[j].interval.lower
  complete   : isolations.size = rootCount p

end Hex
```

`ordered` gives pairwise disjointness for free: half-open intervals
that touch at an endpoint are still disjoint as sets. `complete` is
the completeness certificate: `count_one` puts exactly one root in
each interval, the intervals are disjoint, and there are exactly
`rootCount p` of them, so every real root is captured. The companion
turns these three decidable facts, under `SquareFreeRat p`, into the
semantic statement. No theorem about either search engine is
involved.

## Bounds and depths

```lean
/-- A power of two strictly exceeding the Cauchy root bound
    `1 + max |a_i| / |a_n|`. All real roots lie in
    `(−rootBound p, rootBound p]`. Integer arithmetic only. -/
def rootBound (p : ZPoly) : Dyadic

/-- Separation precision: for any two distinct complex roots
    `z₁ ≠ z₂` of `p`, `2^{−sepPrec p} < ‖z₁ − z₂‖ / 4`. The contract
    is pairwise, so it is vacuous when `p` has fewer than two roots
    (degree ≤ 1), which is exactly when nothing needs it. Closed-form
    integer arithmetic from the Mahler bound, using `|disc p| ≥ 1`
    for squarefree `p` and Landau's inequality, never the
    discriminant value itself. The same closed form as hex-roots'
    `mahlerPrec`. -/
def sepPrec (p : ZPoly) : Nat

/-- The bisection depth at which both engines stop: enough halvings
    to take the initial interval `(−rootBound p, rootBound p]` to
    width below `2^{−sepPrec p}`, plus a fixed slack. -/
def isolationDepth (p : ZPoly) : Nat :=
  sepPrec p + ceilLog2Dyadic (2 * rootBound p) + depthSlack
```

with `depthSlack := 8`. `sepPrec` bounds the distance between *all*
pairs of distinct complex roots, which serves both engines: the Sturm
engine's termination proof needs the bound only for real pairs, and
the Descartes engine's classical termination analysis needs the
complex pairs too (see "Termination" below). The depth is a stopping bound, not a refinement target, so
`depthSlack` can be generous at almost no cost: both engines stop
subdividing an interval the moment its count resolves.

## The Sturm engine

```lean
def isolateSturm? (p : ZPoly) : Option (RealRootIsolations p)
```

Worklist bisection from `(−rootBound p, rootBound p]`. For each
interval, compute the Sturm count:

- count `0`: discard;
- count `1`: emit (the count is the witness, via `if h : _`);
- count `≥ 2`: bisect at the dyadic midpoint, unless the interval has
  reached `isolationDepth p`, in which case return `none`.

After the worklist drains, assemble the emitted isolations in
increasing order and check `complete` (via `if h : _`). A failed
check also returns `none`. A `none` from this engine has one precise
meaning: an interval at separation depth still reported two or more
roots, or the totals disagreed. The companion proves both impossible
for squarefree input, so `isolateSturm?` is total in the sense that
matters. The `Option` is the same fuel discipline as hex-roots'
drivers.

## The Descartes engine

```lean
/-- The integer Möbius transform of `p` relative to `(a, b]`: the
    numerator of `(1 + x)^{deg p} · p((a + bx)/(1 + x))` after
    clearing the dyadic denominators (a positive power of two). Its
    positive real roots correspond bijectively, with multiplicity, to
    the real roots of `p` in the open interval `(a, b)`. -/
def mobiusTransform (p : ZPoly) (I : DyadicInterval) : ZPoly

/-- Sign variations of the coefficient list. -/
def descartesVar (p : ZPoly) : Nat

def isolateDescartes? (p : ZPoly) : Option (RealRootIsolations p)
```

The search runs the same worklist, dispatching on
`V := descartesVar (mobiusTransform p I)` and the exact test
`p(b) = 0`:

| `V` | `p(b) = 0` | action                        |
|-----|------------|-------------------------------|
| 0   | no         | discard                       |
| 0   | yes        | candidate (root is `b` itself)|
| 1   | no         | candidate                     |
| 1   | yes        | bisect (two roots in `(a, b]`)|
| ≥ 2 | either     | bisect                        |

Descartes' rule makes the discard row sound (`V = 0` means no roots
in the open interval) and the candidate rows plausible, but the
engine trusts neither: every candidate is certified by computing its
Sturm count, and a candidate whose count is not `1` aborts the engine
with `none`. Bisection past `isolationDepth p` also returns `none`,
as does a failed final `complete` check. The classical analysis says
none of these happen (see "Termination"), but nothing here depends on
that: the Descartes engine is a search heuristic wrapped in Sturm
certificates, and it carries **no proof obligations** in the
companion beyond the deferred termination statement.

The per-node cost is one Möbius transform (`O(n²)` integer
operations via Taylor shift) against the Sturm engine's full chain
evaluation, which is why this engine runs first.

## The driver

```lean
def isolate? (p : ZPoly) : Option (RealRootIsolations p) :=
  isolateDescartes? p <|> isolateSturm? p
```

The companion proves `isolate? p ≠ none` for squarefree `p` (through
the Sturm engine). Downstream libraries that need a total function
(hex-rcf) obtain one by combining `isolate?` with that theorem.

## Termination

Both engines terminate structurally: each worklist entry carries its
remaining depth budget, bisection decreases it, and no analytic input
is required. What the depth budget *suffices for* differs:

- **Sturm engine.** At depth `isolationDepth p` every interval has
  width below `2^{−sepPrec p} < sep(p)/4`, so it contains at most one
  real root, so its exact count is `0` or `1` and the worklist
  drains. This is a theorem of the companion
  (`isolateSturm?_isSome`).
- **Descartes engine.** The classical termination analysis (the
  Obreshkoff two-circle theorem; Krandick-Mehlhorn 2006) shows that
  once an interval's width is below a constant multiple of `sep(p)`
  (the minimum distance between distinct complex roots), its
  variation count is `0` or `1`, so `isolateDescartes? p ≠ none` for
  squarefree `p` at this depth. The mechanism is the *λ-graded* sector
  bound (not a general count bound — the reading "variation count ≤
  number of roots in the two-circle region" is false): at most `λ`
  roots outside the half-angle-`π/(λ+2)` sector force at most `λ` sign
  variations. A short interval's two-circle region is too small to hold
  two roots, and a lone non-real root there is excluded because the
  region is symmetric about the real axis (conjugate pairs), so the
  outside-sector count stays `≤ 1` and hence the variation count `≤ 1`.
  This is now a theorem of the companion
  (`isolateDescartes?_isSome`): it retires the Sturm fallback from the
  runtime story, though no other theorem depends on it and the driver's
  completeness never waited for it.

Note the separation quantity is over **complex** roots in both cases.
A real-gap bound is not enough for the Descartes engine: a conjugate
pair close to the real axis, as in `(x − 1)² + ε²`, keeps the
variation count at 2 on every interval around its real part until the
width shrinks to the order of `ε`, even though the polynomial has no
real roots at all.

## Refinement

```lean
namespace Hex.RealRootIsolation

/-- Bisect at the dyadic midpoint and keep the half whose Sturm count
    is 1: one chain evaluation at the midpoint decides. Returns the
    input unchanged in the (impossible for squarefree `p`, proven in
    the companion) case that neither half certifies. -/
def refine1 (iso : RealRootIsolation p) : RealRootIsolation p

/-- Iterate `refine1` until the interval width is at most
    `2^{−target}`. Fueled by the width gap; total. -/
def refineTo (iso : RealRootIsolation p) (target : Int) :
    RealRootIsolation p

end Hex.RealRootIsolation
```

Because the witness is a count, refinement has no endpoint case
analysis: a root exactly at the midpoint `m` lands in the left half
`(a, m]` by the half-open convention, and the counts say so. The
width-halving guarantee is the companion theorem
`refine1_isolates_same`, conditional on squarefree `p`. On data that
violates the isolation semantics the fallback branch returns the
input unchanged and `refineTo` stops when its fuel runs out; neither
function can loop.

## `SimpleRealRoot`: identity of a root, up to isolation

```lean
namespace Hex

/-- An isolation refined to separation precision. At width below
    `sep(p)/4`, two refined isolations isolate the same root exactly
    when their intervals overlap. -/
def RefinedRealIsolation (p : ZPoly) :=
  {iso : RealRootIsolation p //
     iso.interval.upper − iso.interval.lower ≤ twoPow (−(sepPrec p : Int))}

/-- The half-open intervals intersect:
    `max lower₁ lower₂ < min upper₁ upper₂`. One dyadic comparison. -/
def Overlaps (i₁ i₂ : RefinedRealIsolation p) : Prop := …
instance : Decidable (Overlaps i₁ i₂) := …

/-- The identity of a real root, independent of which isolation
    witnessed it. -/
def SimpleRealRoot (p : ZPoly) := Quot (Overlaps (p := p))

def SimpleRealRoot.mk (iso : RefinedRealIsolation p) : SimpleRealRoot p :=
  Quot.mk _ iso

/-- Boolean form of `Overlaps`, used for equality tests on data
    containing roots. -/
def RefinedRealIsolation.sameRoot (i₁ i₂ : RefinedRealIsolation p) : Bool := …

/-- Refine an isolation to separation precision and package it as a
    `RefinedRealIsolation`: `refineTo (sepPrec p)`, then the width check.
    `none` only on data violating the isolation semantics (unreachable
    for squarefree `p`, per the companion's `refine1_isolates_same`).
    The entry point of the threading pattern: call once, thread the
    refined value forward. -/
def RealRootIsolation.refined (iso : RealRootIsolation p) :
    Option (RefinedRealIsolation p)

end Hex
```

Why the width bound is part of the type: without it, a coarse
isolation overlapping several fine ones would relate distinct roots
and the quotient would collapse them. With both widths below
`sep(p)/4`, two overlapping intervals contain points within
`sep(p)/2` of both roots, forcing the roots to coincide. Conversely,
two isolations of the same root both contain it, so they overlap.
That argument is semantic, so this library takes the quotient with
`Quot` (which needs no equivalence proof) and provides no
`DecidableEq (SimpleRealRoot p)`. The companion proves that
`Overlaps` restricted to `RefinedRealIsolation` is an equivalence
relation whose classes are exactly the real roots, and hence that
`sameRoot` decides equality in the quotient. Code in the Mathlib-free
layer compares roots with `sameRoot` directly.

The threading pattern for representatives is the same as in
hex-roots: refine once, pass the refined value forward, never
re-refine from a stored coarse representative. See
[hex-roots.md](hex-roots.md) §"The threading pattern".

## Design choices not taken

- **A single engine.** Sturm alone is provably complete but pays a
  full chain evaluation per bisection node. Descartes alone is fast,
  but its termination proof needs the unformalised two-circle
  theorem. Running Descartes inside Sturm certificates takes the
  speed of one and the theorems of the other, at the cost of one
  extra (cheap) certification per emitted root.
- **The Sylvester-Habicht / subresultant chain.** Computing the chain
  through hex-resultant's subresultant sequence would avoid the
  content gcds, at the price of the sign-management bookkeeping and a
  dependency. The primitive chain's coefficients are already minimal
  among pseudo-remainder schemes, and the chain is computed once per
  polynomial, so the content gcds are not on the hot path.
- **Tighter root bounds (Akritas-Strzeboński's LMQ).** Mathlib
  already has `Polynomial.cauchyBound` with its root-bound theorem. A
  tighter start bound would save only the top few bisection levels
  and would add a fresh analytic proof obligation.
- **Vincent / continued-fraction search (VCA, VAS).** Faster than
  bisection in some regimes, but Vincent's theorem is formalised
  nowhere and the search does not change the certificate story.
- **Newton refinement.** Out of scope: `refine1` bisection is enough
  for the consumers in this repository. hex-roots' speculative Newton
  pattern would port if profiling ever demands it.

## File organisation

- `HexRealRoots/Basic.lean`: `DyadicInterval`, exact dyadic Horner
  evaluation, sign helper.
- `HexRealRoots/Chain.lean`: `spem`, `sturmChain`.
- `HexRealRoots/Var.lean`: `signVar`, `sturmVarAt`, the `±∞`
  variants, `sturmCount`, `rootCount`, `RealRootIsolation`,
  `RealRootIsolations`.
- `HexRealRoots/Prec.lean`: `sepPrec`, `isolationDepth`,
  `rootBound`.
- `HexRealRoots/Mobius.lean`: `mobiusTransform` (Taylor shift based),
  `descartesVar`.
- `HexRealRoots/IsolateSturm.lean`: the Sturm engine.
- `HexRealRoots/IsolateDescartes.lean`: the Descartes engine.
- `HexRealRoots/Isolate.lean`: `isolate?`.
- `HexRealRoots/Refine.lean`: `refine1`, `refineTo`.
- `HexRealRoots/SimpleRealRoot.lean`: `RefinedRealIsolation`,
  `Overlaps`, `SimpleRealRoot`, `sameRoot`; the threading-pattern
  guidance lives here as a docstring.
- `conformance/HexRealRoots/{Conformance,EmitFixtures}.lean` and
  `bench/HexRealRoots/Bench.lean`: the conformance and bench drivers,
  in the shared sub-projects.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md), fixtures are tiered into
`core` / `ci` / `local`.

- *core* (Lean-only, runs on every push):
  - Linear: `x − 5`.
  - `x² − 1` (roots at `±1`), `x² + 1` (no real roots), `x³ − x`
    (roots at `−1, 0, 1`), `x³ − x − 1` (one real root).
  - Dyadic-root edge cases: `(2x − 1)(x − 2)` (a root that bisection
    midpoints hit exactly), `x(x − 1)` (adjacent isolations sharing
    an endpoint).
  - Chebyshev `T₅` (five roots in `[−1, 1]`), cyclotomic `Φ₅` (no
    real roots).
  - Non-squarefree rejection: `(x − 1)²(x + 1)` returns `none` from
    both engines, and its `squareFreeCore` isolates.
- *ci* (CI, with external oracle): 30 degree-15 polynomials with
  small coefficients from a deterministic seed. Expected isolations
  from SageMath or python-flint.
- *local* (developer-driven): Mignotte `xⁿ − (a·x − 1)²` for
  `n ∈ {10, 20}` and `a ∈ {1000, 10⁶}` (a close real root pair, the
  known worst case for Descartes variation counts), the Wilkinson
  polynomial of degree 20, Chebyshev `T₂₀` and `T₅₀` (roots
  clustering near `±1`).

External oracles, in role order: SageMath (`real_roots`),
python-flint (`fmpz_poly` real root API), FLINT/Arb.

**Descartes-engine checks (retired).** While
`isolateDescartes?_isSome` was open, the conformance suite asserted on
every fixture that `isolateDescartes?` returns `some` and agrees with
`isolate?`, standing in for the theorem. Now that
`isolateDescartes?_isSome` is proven in the companion, those stand-ins
are retired: the theorem carries the claim, and re-testing it per
fixture is noise. The suite keeps only the ordinary input-contract
checks — the `isolateDescartes? = none` rejection of the zero and
non-squarefree inputs (which test the engine's classification of
inadmissible input, not the termination theorem) — and the executable
`mobiusTransform`/`descartesVar` transform tests. `EmitFixtures` emits
from `isolate?` alone; the cross-engine agreement check it once carried
is removed with the same change.

## Complexity contract

Write `n = deg p` and `h = log ‖p‖∞`.

- `sturmChain p`: `O(n)` pseudo-divisions, each `O(n²)` coefficient
  operations, plus the content gcds. Primitive-chain coefficient
  growth is `O(n·h)` bits per element. Computed once per polynomial.
- `sturmVarAt`: one exact Horner evaluation per chain element,
  `O(n²)` dyadic operations per queried point, memoised per endpoint.
- `mobiusTransform`: `O(n²)` integer operations per node.
- `sepPrec p`, `rootBound p`: `O(n · h)` integer operations.
- `isolate?`: the bisection tree has `O(n)` unresolved intervals per
  level and depth at most `isolationDepth p = O(n·(h + log n))`, so
  `O(n² · (h + log n))` Möbius transforms in the worst case,
  dominated by Mignotte-style clustered inputs. Mignotte inputs
  dominate through the *depth* factor (the close pair's separation
  is exponentially small in `n`, growing with `a`); the `O(n)`
  width factor additionally requires `Θ(n)` real roots, so at fixed
  `a` the Mignotte family realises `O(1)` width × `O(n·h)` depth =
  `O(n·h)` transforms, i.e. `O(n³)` integer operations at fixed `a`.
  Well-separated roots resolve in `O(n + log(rootBound/gap))`
  levels.

## Time budgets (Phase 4 validation)

Rough first guesses, to be measured against SageMath and Arb on the
same fixtures during Phase 4:

- Degree 10, well-separated roots: under 1 second.
- Degree 50: under 10 seconds.
- Degree 100: under 1 minute.

Mignotte clusters at `a = 10⁶` may exceed these. Bench will surface
the constants and whether the Descartes engine's node cost advantage
holds where it should.

## References

- Sturm. *Mémoire sur la résolution des équations numériques.*
  Bulletin de Férussac 11 (1829); Mémoires présentés par divers
  savants 6 (1835). The counting theorem.
- Collins, Akritas. *Polynomial real root isolation using Descartes'
  rule of signs.* SYMSAC 1976. The bisection search implemented by
  the Descartes engine (often misattributed to Uspensky).
- Obreschkoff. *Verteilung und Berechnung der Nullstellen reeller
  Polynome.* VEB Deutscher Verlag der Wissenschaften, 1963. The
  two-circle theorem behind the Descartes engine's classical
  termination bound.
- Krandick, Mehlhorn. *New bounds for the Descartes method.* J.
  Symbolic Computation 41 (2006) 49-66. The modern form of the
  termination analysis.
- Eigenwillig. *Real root isolation for exact and approximate
  polynomials using Descartes' rule of signs.* PhD thesis, Saarland
  University, 2008. Survey of the Descartes method's correctness and
  termination story.
- Basu, Pollack, Roy. *Algorithms in Real Algebraic Geometry.*
  Springer, 2nd ed., 2006. Chapter 2 (Sturm), Chapter 10 (isolation).
- Mahler. *An inequality for the discriminant of a polynomial.*
  Michigan Math. J. 11 (1964) 257-262. The separation bound behind
  `sepPrec`.
- Mignotte. *Some useful bounds.* In *Computer Algebra: Symbolic and
  Algebraic Computation*, Springer, 1982. The textbook form used by
  the closed-form computation.
