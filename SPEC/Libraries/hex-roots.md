# hex-roots (complex root isolation, depends on hex-poly-z)

Certified isolation of complex roots of integer-coefficient
polynomials. A root isolation is a square in the complex plane with
Gaussian-dyadic centre and power-of-two half-width, together with a
witness, dischargeable by `decide`, that the square's circumscribed
disc contains exactly one simple root (an *atom*) or exactly `k` roots
counted with multiplicity (a *cluster*). Refinement combines
speculative Newton iteration (using `Dyadic.invAtPrec` from the Lean
standard library) with subdivision and component gluing as the
fallback, following the hybrid algorithm of Becker, Sagraloff, Sharma,
and Yap, *J. Symbolic Computation* 86 (2018) 51-96 (arXiv:1509.06231;
"BSSY" below).

## Exact witness arithmetic

A `ZPoly` evaluated at a Gaussian-dyadic point `a + b·i` yields Taylor
coefficients

```
cₖ = Σ_{j ≥ k} binomial(j,k) · aⱼ · (a + b·i)^{j−k}
```

each term an integer times a Gaussian-dyadic power, so
`cₖ ∈ Dyadic[i]` *exactly*.

The Pellet inequalities compare absolute values `|cₖ|` against sums of
absolute values, and `|cₖ|` is irrational in general. The witnesses
therefore replace each absolute value by an exact dyadic bound on the
correct side:

- lower bound `lo(c) := max(|Re c|, |Im c|)`, with
  `lo(c) ≤ |c| ≤ √2 · lo(c)`;
- upper bound `hi(c) := |Re c| + |Im c|`, with
  `|c| ≤ hi(c) ≤ √2 · |c|`;
- the factor `√2` in disc radii (below) is bounded by the dyadic
  rationals `181/128 < √2 < 1449/1024`, each within `10⁻³` of `√2`.

Every witness in this library is a strict comparison between two exact
dyadics: `Decidable`, with no error budget and no interval-arithmetic
infrastructure. The bounds cost slack: a witness holds only when the
true Pellet inequality holds with a factor-2 margin (each side loses
at most `√2`, plus the negligible slack from the rational `√2`
bounds). Soundness is unaffected, since a witness implies the true
inequality. The slack only tightens the isolation ratio a disc must
reach before the witness fires, and it is carried through the
completeness analysis in the Mathlib companion. The Newton step itself
uses the approximate `Dyadic.invAtPrec`, but the witness re-check
after Newton uses the new exact dyadic centre and is again exact.

## Geometry: dyadic squares and circumscribed discs

Subdivision works on dyadic squares (they partition cleanly 4-ways);
Pellet tests run on the **circumscribed disc** of a square. For a
square of half-width `2^{−prec}` the circumscribed disc has radius
`2^{−prec} · √2`. In witnesses that radius appears only through its
dyadic bounds `2^{−prec} · 181/128` and `2^{−prec} · 1449/1024`.

`prec` is an `Int`, not a `Nat`: the initial square from the Cauchy
bound has half-width `2^{−prec}` with `prec` negative whenever the
root bound exceeds 1.

Distances between centres are compared through their squares, which
are exact dyadics. In particular "the discs of two squares intersect"
is a single dyadic comparison: with radii `rᵢ = √2·2^{−pᵢ}`,

```
(r₁ + r₂)² = 2·4^{−p₁} + 2·4^{−p₂} + 4·2^{−p₁−p₂}
```

is exact, and so is the squared distance between the two
Gaussian-dyadic centres.

## Pellet witnesses

```lean
/-- Strong Pellet witness: with `(c₀, …, c_n)` the exact Taylor
    coefficients of `p` at the centre of `s`, and `ρlo, ρhi` the dyadic
    bounds on the circumscribed radius `2^{−s.prec}·√2`, the inequality

      `lo(c_k) · ρlo^k > Σ_{i ≠ k} hi(c_i) · ρhi^i`

    holds at the base radius and at 2 and 4 times the base radius.
    Implies (Mathlib companion): `p` has exactly `k` roots, with
    multiplicity, in each of the three discs. -/
def witness (p : ZPoly) (s : DyadicSquare) (k : Nat) : Prop := …
instance : Decidable (witness p s k) := …
```

The three-radius form is BSSY's condition for Newton readiness, and it
makes an atom interchangeable with a one-square cluster (both carry
the same witness shape). "No roots on the boundary circles" follows
from the strict inequality and is exposed as a derived lemma in the
Mathlib companion.

## Contents

```lean
namespace Hex

structure DyadicSquare where
  re   : Dyadic
  im   : Dyadic
  prec : Int
  -- half-width 2^{−prec}; circumscribed disc radius 2^{−prec}·√2

/-- An atom: one square whose circumscribed disc contains exactly one
    simple root. -/
structure DyadicRootIsolation (p : ZPoly) where
  square  : DyadicSquare
  witness : witness p square 1

/-- A certified cluster: an edge-connected set of grid squares at a
    common `prec`, whose enclosing disc contains exactly `k` roots
    with multiplicity. The component squares are the data that
    *refinement* operates on; subdividing the enclosing square
    instead would stall (it can equal the parent square when a root
    sits on a grid line, even as the component squares themselves
    shrink). The Pellet certificate, by contrast, is attached to the
    circumscribed disc of `encSquare squares`. This is an *output*
    type; the refinement worklist holds uncertified `Component`
    values. -/
structure DyadicRootCluster (p : ZPoly) where
  squares   : Array DyadicSquare     -- nonempty, common prec, edge-connected
  k         : Nat
  k_pos     : 0 < k
  witness   : witness p (encSquare squares) k

/-- An uncertified component in the refinement worklist: an
    edge-connected set of grid squares at a common `prec`, plus the
    root count of its most recently certified ancestor. `candidateK`
    only selects the order of the speculative Newton step; it is never
    trusted, since every output is re-certified. -/
structure Component where
  squares    : Array DyadicSquare    -- nonempty, common prec, edge-connected
  candidateK : Nat

/-- The smallest square with power-of-two half-width and centre at the
    component's bounding-box centre that contains every square of the
    component. All witness tests run on its circumscribed disc. -/
def encSquare (squares : Array DyadicSquare) : DyadicSquare := …

/-- A complex ball with dyadic data, the output type of numerical
    evaluation here and in hex-number-field. -/
structure DyadicComplexBall where
  re     : Dyadic
  im     : Dyadic
  radius : Dyadic

/-- `p` has only simple complex roots. Decided by casting `p` and `p'`
    to `DensePoly Rat` and testing whether HexPoly's Euclidean gcd is
    constant. The Mathlib companion proves equivalence with
    `Squarefree (toPolynomial p)`. -/
def HasOnlySimpleRoots (p : ZPoly) : Prop := …
instance : Decidable (HasOnlySimpleRoots p) := …
```

## Operations

```lean
namespace Component
/-- One subdivision round: split every square into 4 children one bit
    finer, discard children whose disc certifiably contains no root
    (the `T_0` test; a child whose `T_0` test fails to certify is
    kept, which is always sound), and glue the survivors into
    edge-connected components. Total: no certification is required
    during refinement. -/
def refine1 : Component → Array Component

/-- Try to certify the component as a cluster: a speculative Newton
    recentring first, then the strong witness on the enclosing
    square's disc, with `k = candidateK` first and then the remaining
    `k ≤ deg p`. -/
def certify? (p : ZPoly) : Component → Option (DyadicRootCluster p)

/-- The starting component: a single square centred at 0 covering the
    Cauchy root bound, with `candidateK = deg p`. -/
def cauchy (p : ZPoly) (h : 0 < p.degree?.getD 0) : Component
end Component

/-- Repackage a certified `k = 1` cluster as an atom. Total: the
    cluster's witness already lives on the enclosing square's disc,
    which is the atom's square. -/
def DyadicRootCluster.atomize (c : DyadicRootCluster p) (h : c.k = 1) :
    DyadicRootIsolation p

/-- Refine to `target` precision: speculative Newton steps, falling
    back to subdivision of the atom's square as a one-square
    component. `none` only if certification has not reappeared by
    `stopDepth p target` (see below). -/
def DyadicRootIsolation.refineTo? (iso : DyadicRootIsolation p)
    (target : Int) : Option (DyadicRootIsolation p)

/-- Refine every component until certified at prec ≥ target, with the
    certified discs pairwise disjoint (see "Separation of the output"
    below). `none` only if this has not happened by
    `stopDepth p target`. -/
def isolateAll? (p : ZPoly) (target : Int) (worklist : Array Component) :
    Option (Array (DyadicRootCluster p))

/-- All-atoms output for polynomials with only simple roots: run
    `isolateAll?` from `Component.cauchy` with
    `target := max atom_prec (separationDepth p)`, then `atomize`
    every cluster. `none` if `isolateAll?` fails or (impossible for
    squarefree `p`, proven in the companion) some cluster reports
    `k ≥ 2`. -/
def isolate (p : ZPoly) (h : Hex.HasOnlySimpleRoots p) (atom_prec : Int) :
    Option (Array (DyadicRootIsolation p))
```

The speculative Newton step computes `x' = x − k · c₀/c₁` (with
`k = 1` for atoms; the k-order step for clusters is BSSY §5), places a
much smaller square at `x'`, and re-runs the witness. If the witness
certifies, the step gains quadratic precision. If not, the result is
discarded and subdivision proceeds. There is no a-priori "Newton
ready" precondition. The Gaussian inversion `1/c₁ = c̄₁ / |c₁|²` uses
`Dyadic.invAtPrec` for the single real reciprocal `1/|c₁|²`, which
both the real and imaginary components reuse. That is why the
implementation calls `invAtPrec` rather than two separate
`Dyadic.divAtPrec` divisions.

**Termination.** Termination is structural, with no analytic input.
Write `gap(c) := stopDepth p target − prec(c)` for a component `c` in
the worklist. One `refine1` round replaces a component of `s` squares
at gap `g` by components at gap `g − 1` totalling at most `4s`
squares, so the measure

```
Φ(worklist) := Σ_c (#squares of c) · 5^(gap c)
```

strictly decreases per round (`4s · 5^{g−1} < s · 5^g`). Newton steps
only jump precision further. What is *not* structural is
certification: `certify?` can fail at any single depth. The drivers
therefore keep subdividing past `target`, attempting certification at
each depth, and give up at

```
stopDepth p target := max target (separationDepth p) + stopSlack
```

with `stopSlack := 8`. The degree-dependent part of the required
depth lives inside `separationDepth` (below); `stopSlack` is only a
fixed margin on top, and it can be generous at almost no cost:
overshooting costs a few extra subdivision rounds in the rare case
certification had not already happened, and nothing else. The completeness analysis
certifies the pinned value (or shows a smaller one suffices). A
`none` from the drivers has one precise meaning: *a Pellet witness
failed to appear at separation depth*. The Mathlib
companion's completeness development
([hex-roots-mathlib.md](hex-roots-mathlib.md)) is expected to prove
this impossible for squarefree inputs. Until it does, the soundness
theorems (which are conditional on a `some` result) are unaffected,
and the conformance suite checks that `none` does not occur on the
committed fixtures.

**Separation of the output.** Certification alone does not prevent
double-counting. A component whose squares contain no root (its
`T_0` tests merely failed to certify at this depth) can still pass
`certify?` with `k = 1` when its enclosing disc overlaps a
neighbouring component and captures the neighbour's root. The driver
therefore emits a set of certified clusters only when their witness
discs are **pairwise disjoint** (one dyadic comparison per pair, as
in the `SimpleRoot` intersection test); components violating the
check keep subdividing. Disjoint discs count disjoint root sets, and
the retained squares cover all roots, so the output `k` values add up
to exactly the root count. This is the analogue of the separation
condition in BSSY §4. Rootless components die on their own: once
every square of such a component is `T_0`-certified empty, the
component disappears from the worklist.

Roots that sit exactly on a dyadic grid point are not a problem for
atomization: the Newton step recentres the square on the root itself
(the arithmetic is exact at Gaussian-dyadic points), after which the
one-square witness certifies. Roots on a grid *line* keep a two-square
or four-square component under pure subdivision. Newton recentring is
what turns those into single-square atoms.

For polynomials with multiple roots there is no `isolate` analogue.
Use `isolateAll?` directly: a multiple root never atomizes (the `k = 1`
witness requires `c₁` bounded away from 0, and `c₁ → 0` near a
multiple root), so it appears in the output as a cluster with its
`k ≥ 2` field.

## `mahlerPrec`: separation precision

```lean
def mahlerPrec (p : ZPoly) : Nat
```

For squarefree `p ∈ ℤ[x]` of degree `n`, the Mahler separation bound
gives

```
sep(p) := min_{i ≠ j} |αᵢ − αⱼ| ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}
```

Combined with `|disc p| ≥ 1` (the discriminant of a squarefree integer
polynomial is a nonzero integer) and Landau's
`M(p) ≤ √(n+1) · ‖p‖∞`, this bounds `sep(p)` from below in terms of
`n` and `‖p‖∞` alone. `mahlerPrec p` is a `Nat` such that the
circumscribed-disc radius at that precision is strictly below
`sep(p)/4`:

```
2^{−mahlerPrec p} · 1449/1024 < sep(p) / 4
```

The `/4` margin is what the `SimpleRoot` intersection test below
needs. The computation is pure integer arithmetic on the closed-form
bound (logarithms by repeated squaring). No discriminant is computed
at runtime; only the constant lower bound `|disc p| ≥ 1` is used. The
Mahler bound concerns *distinct* roots, so `mahlerPrec` is meaningful
even for non-squarefree `p`: if `p_sf` is the squarefree part then
`M(p_sf) ≤ M(p)` and `|disc p_sf| ≥ 1`, so the same closed form
applies. The Mathlib companion proves correctness; see
[hex-roots-mathlib.md](hex-roots-mathlib.md).

```lean
def separationDepth (p : ZPoly) : Nat :=
  mahlerPrec p + ceilLog2 (max 2 (p.degree?.getD 0)) + sepSlack
```

with `sepSlack := 8`. `separationDepth` is the depth at which the
completeness analysis says every Pellet witness certifies. Past
`mahlerPrec p` each component's disc contains at most one distinct
root, and its isolation ratio doubles with every further level. How
large a ratio the witness needs is *degree-dependent*: for a disc of
radius `ρ` around a simple root at distance `d` from the other
roots, the higher Taylor coefficients collect contributions from all
`n − 1` remote roots, and the ratio of the right side of the `T_1`
inequality to the left is bounded by `(1 + ρ/d)^{n−1} − 1`, so the
witness needs `ρ/d` of order `1/n`. That is what the
`ceilLog2 (deg p)` term buys, one doubling at a time. (This is the
price of omitting Graeffe iteration; the fixed-ratio test Graeffe
enables would make this term a constant.) The remaining `sepSlack`
covers the fixed factors: one level for the factor-2 witness slack,
at most two for the enclosing square of a multi-square component,
one for the circumscribed `√2`, and margin. The completeness
analysis certifies the formula; overshoot costs only extra
subdivision rounds on inputs where certification had not already
happened. It is the depth bound used by `stopDepth` above.

## `SimpleRoot`: identity of a root, up to isolation

```lean
namespace Hex

/-- An isolation refined at least to separation precision. At this
    precision the disc radius is below `sep(p)/4`, so two refined
    isolations isolate the same root exactly when their discs
    intersect. -/
def RefinedIsolation (p : ZPoly) :=
  {iso : DyadicRootIsolation p // (mahlerPrec p : Int) ≤ iso.square.prec}

/-- The circumscribed discs intersect. A single exact dyadic
    comparison (squared centre distance against squared radius sum). -/
def Intersects (i₁ i₂ : RefinedIsolation p) : Prop := …
instance : Decidable (Intersects i₁ i₂) := …

/-- The identity of a simple root, independent of which isolation
    witnessed it. -/
def SimpleRoot (p : ZPoly) := Quot (Intersects (p := p))

def SimpleRoot.mk (iso : RefinedIsolation p) : SimpleRoot p := Quot.mk _ iso

/-- Boolean form of `Intersects`, used for equality tests on data
    containing roots (see hex-number-field). -/
def RefinedIsolation.sameRoot (i₁ i₂ : RefinedIsolation p) : Bool := …

end Hex
```

Why the radius bound is part of the type: without it, a coarse
isolation whose disc overlaps several fine isolations would relate
distinct roots, and the quotient would collapse them. With every disc
strictly smaller than `sep(p)/4`, two intersecting discs contain
points within `sep(p)` of both roots, forcing the roots to coincide.
That argument is semantic, so this library takes the quotient with
`Quot` (which needs no equivalence proof) and provides no
`DecidableEq (SimpleRoot p)`. The Mathlib companion proves that
`Intersects` restricted to `RefinedIsolation` is an equivalence
relation whose classes are exactly the simple roots, and hence that
`sameRoot` decides equality in the quotient. Code in the Mathlib-free
layer compares roots with `sameRoot` directly.

### The threading pattern

`SimpleRoot p` values carry no usable computational content in this
layer (nothing lifts out of the `Quot` here). Numerical work happens
on `RefinedIsolation` representatives, which are plain data. A
function that repeatedly needs high-precision approximations of the
same root should refine its representative once and pass the refined
value forward:

```lean
-- DON'T: each use re-refines from the stored representative
def slow (r : RefinedIsolation p) : Foo :=
  let a := (r.1.refineTo? 32).map …
  let b := (r.1.refineTo? 64).map …   -- repeats the work up to 32
  …

-- DO: refine once, thread the refined representative forward
def fast (r : RefinedIsolation p) : Option (RefinedIsolation p × Foo) := do
  let r' ← r.refineTo? 64
  …                                   -- both uses read r' directly
  return (r', …)                      -- caller stores r' going forward
```

`refineTo?` preserves the root (`sameRoot r r' = true`, proved
meaningful in the companion), so callers can substitute the refined
representative wherever the original was used. Structures that contain
a representative (such as `AlgebraicNumber` in `hex-number-field`)
should store the refined value on return, so downstream consumers
inherit the precision.

## Differences from BSSY

- **No Graeffe iteration.** Deferred as a future optimisation. Without
  it the witness needs an isolation ratio of order `deg p` before it
  certifies (every remote root contributes to the higher Taylor
  coefficients), which costs the `ceilLog2 (deg p)` term in
  `separationDepth`. Graeffe iteration would let a fixed ratio
  suffice and reduce that term to a constant.
- **No squarefree preprocessing.** A multiple root fails the `k = 1`
  witness at every radius, so it stays a `k ≥ 2` cluster and is
  reported as such. Squarefree inputs atomize. Non-squarefree inputs
  yield the multiple roots as clusters.
- **Squares partition, discs test.** Squares partition the plane
  without overlap; circumscribed discs overlap slightly, but the
  `T_0` discard and the component gluing recover the exact root
  distribution (BSSY §4).
- **Speculative Newton.** No precondition is checked before a Newton
  step; the step is taken and the witness re-run on the result.
  Certification success is the only acceptance criterion.

## File organisation

- `HexRoots/Basic.lean`: `DyadicSquare`, `DyadicComplexBall`,
  `DyadicRootIsolation`, `DyadicRootCluster`, `Component`,
  `encSquare`, `Hex.HasOnlySimpleRoots`.
- `HexRoots/Taylor.lean`: exact Gaussian-dyadic Taylor expansion of a
  `ZPoly` at a Gaussian-dyadic centre, returning
  `Array (Dyadic × Dyadic)`.
- `HexRoots/Pellet.lean`: the dyadic bounds `lo`/`hi`, the rational
  `√2` constants with their `decide`-checked defining inequalities,
  the `witness` predicate and its `Decidable` instance.
- `HexRoots/MahlerPrec.lean`: the closed-form `mahlerPrec` and
  `separationDepth`.
- `HexRoots/Cauchy.lean`: `Component.cauchy`.
- `HexRoots/Newton.lean`: the speculative Newton step (atom and
  k-order component forms) using `Dyadic.invAtPrec`.
- `HexRoots/Bisection.lean`: 4-way subdivision, `T_0` discard,
  component gluing: `Component.refine1` and `Component.certify?`.
- `HexRoots/Refine.lean`: `DyadicRootIsolation.refineTo?`, the Φ
  termination measure, `stopDepth`.
- `HexRoots/IsolateAll.lean`: `isolateAll?`, `atomize`, `isolate`.
- `HexRoots/SimpleRoot.lean`: `RefinedIsolation`, `Intersects`,
  `SimpleRoot`, `sameRoot`; the threading-pattern guidance lives here
  as a docstring.
- `conformance/HexRoots/{Conformance,EmitFixtures}.lean` and
  `bench/HexRoots/Bench.lean`: the conformance and bench drivers, in
  the shared sub-projects.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md), fixtures are tiered into
`core` / `ci` / `local`. Deterministic adversarial families matter
more than random samples here, because random small-coefficient
polynomials rarely have clustered roots.

- *core* (Lean-only, runs on every push):
  - Polynomials with rational roots: `(x−1)(x−2)(x+3)`, `x³ − x`.
  - Cyclotomic `Φ_n` for `n ∈ {5, 7, 12}`: roots are roots of unity.
  - Chebyshev `T_n` for `n ∈ {5, 10}`: roots at known
    `cos((2k−1)π/(2n))`.
  - Small Mignotte `xⁿ − (a·x − 1)²` for `n = 5`, `a = 100`: one
    close root pair.
  - Multiple-root case `(x²+1)·(x−5)²`: checks that the `k = 2`
    cluster around `5` does not atomize.
- *ci* (CI, with external oracle when available):
  - 50 degree-20 polynomials with deterministic seed `0xC0FFEE` and
    coefficients in `[−10, 10]`. Expected outputs serialised from a
    local oracle run during fixture emission.
- *local* (developer-driven):
  - Adversarial families cross-checked against MPSolve: Mignotte
    `(n, a)` for `n ∈ {10, 20}` and `a ∈ {1000, 10⁶}`, the Wilkinson
    polynomial of degree 20, and products of two Mignotte polynomials
    with different parameters (close root pairs at two scales).

External oracles, in role order: MPSolve (primary), FLINT/Arb
(secondary, for cases where MPSolve's precision is in doubt), SageMath
(fallback).

## Complexity contract

Write `n = deg p` and `B = prec + n · log ‖p‖∞` for the working
bit-length at precision `prec`.

- `mahlerPrec p` runs in `O(n · log ‖p‖∞)` integer operations.
- One witness check costs `O(n²)` exact-dyadic operations (the Taylor
  shift dominates) on `B`-bit values, so `O(n² · B²)` bit operations
  with schoolbook arithmetic.
- One Newton step costs the same order as one witness check, plus a
  single `Dyadic.invAtPrec` call.
- `isolate` for degree `n`, well-separated roots, target precision
  `prec`: heuristically `O(n³ · B²)` bit operations. Tight root
  clusters add subdivision depth up to `O(mahlerPrec p)`.

## Time budgets (Phase 4 validation)

Rough first guesses, to be measured against MPSolve on the same
fixtures during Phase 4:

- Degree 10, prec 32: under 1 second.
- Degree 50, prec 64: under 10 seconds.
- Degree 100, prec 128: under 1 minute.

## References

- Becker, Sagraloff, Sharma, Yap. *A near-optimal subdivision
  algorithm for complex root isolation based on the Pellet test and
  Newton iteration.* J. Symbolic Computation 86 (2018) 51-96.
  arXiv:1509.06231. The algorithm implemented here, with the
  deviations listed above.
- Imbach, Pan, Yap. *Implementation of a near-optimal complex root
  clustering algorithm (Ccluster).* ICMS 2018, LNCS 10931. The C/Arb
  implementation, including the soft-Pellet filter optimisations.
- Pellet. *Sur un mode de séparation des racines des équations et la
  formule de Lagrange.* Bull. Sci. Math. 5 (1881). Origin of the
  `T_k` test.
- Mahler. *An inequality for the discriminant of a polynomial.*
  Michigan Math. J. 11 (1964) 257-262. The separation bound.
- Mignotte. *Some useful bounds.* In *Computer Algebra: Symbolic and
  Algebraic Computation*, Springer, 1982. The textbook form of the
  bound used by `mahlerPrec`.
