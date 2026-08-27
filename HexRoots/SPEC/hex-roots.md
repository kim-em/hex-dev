# hex-roots (complex root isolation, depends on hex-poly-z)

Certified isolation of complex roots of integer-coefficient
polynomials. A root isolation is a square in the complex plane with
Gaussian-dyadic centre and power-of-two half-width, together with a
structural certificate that a certified region around
the square contains exactly one simple root (an *atom*) or exactly
`k` roots counted with multiplicity (a *cluster*). Atoms carry one
of two certificate forms, tried in a configurable order: a
Newton-Kantorovich contraction witness, whose certified region is
the square itself, or a Pellet witness, whose certified region is
the square's circumscribed disc. Checker-produced certificates remain
dischargeable by `decide`; exact polynomial and square transformations retain
their source certificate as explicit provenance instead of rerunning a
checker. Clusters carry Pellet witnesses on
the circumscribed disc. Refinement combines speculative Newton
iteration (using `Dyadic.invAtPrec` from the Lean standard library)
with subdivision and component gluing as the fallback, following the
hybrid algorithm of Becker, Sagraloff, Sharma, and Yap, *J. Symbolic
Computation* 86 (2018) 51-96 (arXiv:1509.06231; "BSSY" below).

## Exact witness arithmetic

A `ZPoly` evaluated at a Gaussian-dyadic point `a + b·i` yields Taylor
coefficients

```
cₖ = Σ_{j ≥ k} binomial(j,k) · aⱼ · (a + b·i)^{j−k}
```

each term an integer times a Gaussian-dyadic power, so
`cₖ ∈ Dyadic[i]` *exactly*.

The exact Taylor array remains the fallback certificate kernel. The fast
front end instead encloses coefficients of the locally scaled polynomial
`p(c + hX)`, `h = 2^(−s.prec)`, in `CoeffBall`s: a Gaussian-dyadic centre
and a nonnegative dyadic `L¹` error radius. Centres are rounded to a requested
number of significant bits and every radius is rounded outward. Addition,
subtraction, multiplication, and Taylor accumulation transport the error
radius exactly, so coefficient magnitude is decoupled from the working
mantissa length without introducing floating-point trust.

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

Every accepted witness in this library is a strict comparison between exact
dyadics: `Decidable`, with no floating-point error budget. On the soft path the
comparison uses outward-rounded ball endpoints; a failed comparison is
inconclusive and falls back to the exact Taylor kernel. On the exact route,
the `lo`/`hi` bounds require a factor-2 margin (each side loses at most `√2`,
plus the negligible slack from the rational `√2` bounds). The soft route
additionally needs the current coefficient-ball radii to fit within that
margin; the significant-bit ladder shrinks this extra slack. Soundness is
unaffected, since either accepted route implies the true root-count
condition. The slack only tightens the isolation ratio a disc must reach
before the witness fires. The Newton step itself
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

Membership of a Gaussian-dyadic point in one closed circumscribed disc is
likewise exact:

```lean
def DyadicSquare.discContains (s : DyadicSquare) (z : GaussDyadic) : Bool
```

It compares the squared centre distance with `2·4⁻ᵖ`, including boundary
contact. Downstream exact-number libraries use this primitive rather than
reimplementing the geometry.

## Pellet witnesses

```lean
/-- Strong Pellet witness accepted by the exact or outward-rounded Graeffe
    route. Implies (Mathlib companion): exactly `k` roots, with multiplicity,
    in the base, doubled, and quadrupled discs, and none on their boundaries. -/
def witness (p : ZPoly) (s : DyadicSquare) (k : Nat) : Prop := …
instance : Decidable (witness p s k) := …
```

The three-radius form is BSSY's condition for Newton readiness, and it
makes an atom interchangeable with a one-square cluster (both carry
the same witness shape). On the exact route, with `(c₀, …, c_n)` the exact
Taylor coefficients and `ρlo, ρhi` the radius bounds, each comparison is

```
lo(c_k) · ρlo^k > Σ_{i ≠ k} hi(c_i) · ρhi^i.
```

The soft route proves the corresponding strict comparison on an enclosing
coefficient array after zero or more root-squaring transforms. The companion
transports the count back to the original radii. Either route also proves no
root lies on any of the three boundary circles.

For sufficiently large inputs, the executable candidate check scans every
count through a shared Graeffe orbit. One Graeffe step forms
`E(X)² - X O(X)²` from
`p(X) = E(X²) + X O(X²)`; roots and all three radius intervals are squared
together. Repeated squaring amplifies modulus separation, so a constant
isolation ratio can resolve the Pellet comparison. Shallow centres seed the
balls from one exact Taylor shift at 64 bits; deeper centres use a fully soft
Taylor fold at 64, 128, then 256 bits. The individual combined check keeps the
exact cached comparison first below precision 32 and soft-first above it. A
soft success implies the ordinary `witness` proposition. Failure at every tier
invokes the exact cached-shift test and has no semantic meaning.

## Newton-Kantorovich atom witnesses

Atoms admit a second certificate form, carried alongside the Pellet
form as a deliberate experiment: the two routes are implemented,
conformance-checked, and benchmarked side by side, and the choice of
a single route (if any) is deferred until the measurements and the
Mathlib companion's soundness development are in. The two forms have
complementary strengths. The Pellet form counts roots with
multiplicity (it is the only cluster certificate) and its soundness
rests on Rouché's theorem on circles, the heaviest analytic
development in the companion. The Newton-Kantorovich form certifies
only `k = 1`, but its certified region is the square itself in the
sup norm (no circumscribed `√2` on the certified region), its
first-order bounds are exact rather than `lo`/`hi`-bounded, and its
soundness rests on the Banach fixed-point theorem
(`ContractingWith`, already in Mathlib) with no complex analysis.
Mehta and Macbeth have formalised exactly the required
Newton-Kantorovich theorem over Mathlib (see References); the
companion ports it.

Identify ℂ with ℝ² carrying the sup norm, so that the closed ball of
radius `r` about a Gaussian-dyadic centre is the closed square of
half-width `r`. Multiplication by `ζ`, transported to ℝ², is the
matrix `[[Re ζ, −Im ζ], [Im ζ, Re ζ]]`, whose sup-operator norm is
the maximum absolute row sum, which is `hi(ζ)` exactly. This is the
fact that makes the Newton-Kantorovich hypotheses exact-dyadic
comparisons.

With `(c₀, …, c_n)` the exact Taylor coefficients of `p` at the
centre `m` of `s` and `r := 2^{−s.prec}` the half-width, the witness
data is:

- `u := invFloor (normSq c₁) q`, the floor of `1/normSq c₁` on the
  `2^{−q}` grid, with the pinned precision
  `q := 8 + max 0 (ceilLog2 (normSq c₁))`, and
  `w := conj(c₁) · u`, a Gaussian dyadic approximating `1/c₁`.
  For `x = n·2^{−k}` with `n` odd positive the floor is the single
  integer division `⌊2^{q+k}/n⌋·2^{−q}`; this agrees with
  `Dyadic.invAtPrec` on positive arguments but, unlike it,
  kernel-reduces (`invAtPrec` routes through `Rat` normalisation,
  whose `Nat.gcd` well-founded recursion `decide` cannot unfold), so
  the witness stays dischargeable by `decide`. Soundness does not
  depend on the quality of `w` (the quantities below are exact
  functions of whatever `w` is), so `w` is recomputed
  deterministically inside the witness rather than stored; only the
  completeness analysis uses the floor's rounding contract, through
  `1 − w·c₁ = (1/normSq c₁ − u)·normSq c₁ ∈ [0, 2⁻⁸)`.
- `dₖ := w · cₖ` for `k = 0, …, n`, exact Gaussian dyadics.
- `y := max |Re d₀| |Im d₀|`, exactly the sup norm of the Newton
  residual `A(p(m))`.
- `z₁ := hi(1 − d₁)`, exactly the sup-operator norm of
  `1 − A∘p'(m)`.
- `ρ := 1449 · 2^{−s.prec−10}` (that is, the dyadic upper bound
  `(1449/1024)·r` for `√2·r`, the largest modulus in the sup ball),
  and `z₂ := 2 · Σ_{k=2}^{n} k · hi(dₖ) · ρ^{k−2}`, a radial
  Lipschitz bound for `A∘(p'(·) − p'(m))` on the ball: for
  `|δ| ≤ √2·r`,

  ```
  hi(w·(p'(m+δ) − p'(m))) = hi(Σ_{k≥2} k·dₖ·δ^{k−1})
    ≤ √2 · Σ_{k≥2} k·|dₖ|·|δ|^{k−2} · |δ|
    ≤ 2 · (Σ_{k≥2} k·hi(dₖ)·(√2 r)^{k−2}) · ‖δ‖_sup .
  ```

  Only here does a `√2` enter, and only multiplying second-order
  terms; the radial form (differences from the centre, not a
  Lipschitz bound between arbitrary pairs) is what
  Newton-Kantorovich needs, so there is no `k(k−1)` mean-value
  factor.

```lean
/-- Newton-Kantorovich contraction witness on the closed square `s`
    itself (sup norm), with `r = 2^{−s.prec}` the half-width and
    `y, z₁, z₂` the exact dyadic bounds above:

      `0 < normSq c₁  ∧  y + z₁·r + z₂·r²/2 < r  ∧  z₁ + z₂·r < 1`.

    Implies (Mathlib companion): `p` has exactly one root in the
    closed square, it is simple, and it lies in the open square. -/
def nkWitness (p : ZPoly) (s : DyadicSquare) : Prop := …
instance : Decidable (nkWitness p s) := …
```

All three comparisons are strict comparisons of exact dyadics
(`r² = 4^{−prec}` and halving are exact). The soundness sketch: the
inequalities force `w ≠ 0` (`w = 0` would give `z₁ = hi(1) = 1`), so
`A` is invertible and fixed points of `T(x) = x − A(p(x))` are
exactly roots of `p`; strictness in the middle inequality maps the
closed ball strictly inside itself, placing the unique fixed point
in the open square; and `z₁ + z₂·r < 1` makes `A∘p'` invertible at
the fixed point, hence `p'` nonzero there, which is simplicity. A
multiple root can never certify: `c₁ = 0` forces `z₁ = 1`.

Because the certified region is the square with no margin, a root
hugging the component's boundary could never certify at the
component's own enclosing square. `certify?` therefore evaluates
`nkWitness` on the square concentric with `encSquare` one level
coarser (half-width doubled), which guarantees relative sup-margin
`1/2` for any root covered by the component, and the *stored* atom
square is that doubled square. All downstream geometry
(`Intersects`, `mahlerPrec`, separation) reads the stored square, so
nothing else changes; reaching a given stored precision costs one
extra subdivision level, absorbed by `stopSlack`.

The two checker forms remain packaged as the decidable `atomWitness`
proposition. Stored atoms use an indexed structural certificate so exact root
reflection and primitive-sign normalization can transport existing evidence
without assuming that either checker fires again:

```lean
/-- An atom certificate: either certificate form for "exactly one
    simple root in the certified region". -/
def atomWitness (p : ZPoly) (s : DyadicSquare) : Prop :=
  nkWitness p s ∨ witness p s 1
instance : Decidable (atomWitness p s) := …

inductive AtomCertificate : (p : ZPoly) → (s : DyadicSquare) → Type
  | nk (h : nkWitness p s) : AtomCertificate p s
  | pellet (h : witness p s 1) : AtomCertificate p s
  | neg (hprim : ZPoly.Primitive p) (h : AtomCertificate p s) :
      AtomCertificate p.negRoots s.neg
  | normalize (h : AtomCertificate p s) :
      AtomCertificate (ZPoly.normalizePrimitiveSign p) s

def AtomCertificate.ofWitness : atomWitness p s → AtomCertificate p s
def AtomCertificate.isNK : AtomCertificate p s → Bool

/-- Which atom certificates `certify?` attempts, and in which order.
    `nkThenPellet` is the default; the singleton strategies exist for
    the side-by-side comparison. -/
inductive AtomStrategy | nk | pellet | nkThenPellet
```

Note the two disjuncts certify different regions (the closed square
for `nkWitness`, the circumscribed disc for the Pellet form). Every
consumer below needs only the shared consequences: the root lies in
the stored square's circumscribed disc, and it is the only root
there that the isolation's own component covered. In particular the
`SimpleRoot` quotient argument needs only "each root lies in its own
disc", which both forms give.

## Contents

```lean
namespace Hex

structure DyadicSquare where
  re   : Dyadic
  im   : Dyadic
  prec : Int
  -- half-width 2^{−prec}; circumscribed disc radius 2^{−prec}·√2

/-- An atom: one square whose certified region (the square itself for
    the Newton-Kantorovich disjunct, the circumscribed disc for the
    Pellet disjunct) contains exactly one simple root. -/
structure DyadicRootIsolation (p : ZPoly) where
  square  : DyadicSquare
  witness : AtomCertificate p square

/-- A certified cluster: an edge-or-corner-connected set of grid squares at a
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
  squares   : Array DyadicSquare     -- nonempty, common prec, grid-connected
  k         : Nat
  k_pos     : 0 < k
  witness   : witness p (encSquare squares) k

/-- An uncertified component in the refinement worklist: an
    edge-or-corner-connected set of grid squares at a common `prec`, plus the
    root count of its most recently certified ancestor. `candidateK`
    only selects the order of the speculative Newton step; it is never
    trusted, since every output is re-certified. -/
structure Component where
  squares    : Array DyadicSquare    -- nonempty, common prec, grid-connected
  candidateK : Nat

/-- The result of certifying one component: an atom (either atom
    certificate) or a `k ≥ 1` Pellet cluster. -/
inductive Certified (p : ZPoly) where
  | atom    (iso : DyadicRootIsolation p)
  | cluster (cl : DyadicRootCluster p)

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

def DyadicComplexBall.zero : DyadicComplexBall
def DyadicComplexBall.add (a b : DyadicComplexBall) : DyadicComplexBall
def DyadicComplexBall.mul (a b : DyadicComplexBall) : DyadicComplexBall
def DyadicComplexBall.ofRat (q : Rat) (prec : Int) : DyadicComplexBall

/-- `p` has only simple complex roots. Decided by casting `p` and `p'`
    to `DensePoly Rat` and testing whether HexPoly's Euclidean gcd is
    constant. The Mathlib companion proves equivalence with
    `Squarefree (toPolynomial p)`. -/
def HasOnlySimpleRoots (p : ZPoly) : Prop := …
instance : Decidable (HasOnlySimpleRoots p) := …
```

## Operations

The generic ball algebra is owned here for reuse by numerical consumers.
`add` is the Minkowski sum. For centres `aₜ`, `bₜ` and radii `rₐ`, `rᵇ`,
`mul` uses the exact centre product and radius
`hi(aₜ) * rᵇ + hi(bₜ) * rₐ + rₐ * rᵇ`. `ofRat q prec` rounds downward
to `q.toDyadic prec`, with radius zero when that dyadic is exact and otherwise
one ulp `2^(-prec)`.

```lean
namespace Component
/-- One subdivision round: split every square into 4 children one bit
    finer, discard children whose disc certifiably contains no root
    (the `T_0` test; a child whose `T_0` test fails to certify is
    kept, which is always sound), and glue the survivors into
    edge-or-corner-connected components. Total: no certification is required
    during refinement. -/
def refine1 (p : ZPoly) : Component → Array Component

/-- Try to certify the component. Per `strategy`, first the
    Newton-Kantorovich atom witness on the doubled enclosing square
    (with a speculative Newton recentring attempted first), then the
    Pellet witness on the enclosing square's disc with
    `k = candidateK` first and then the remaining `k ≤ deg p`.
    The Pellet route uses the all-count soft Graeffe filter first, then
    rechecks the selected count through the cached combined certifier so the
    same guarded Newton candidate is available; exact candidate scanning is
    the fallback. A `k = 1` success is returned as an atom via `atomize`.
    Speculative Newton results are accepted only under the coverage
    guard (see "Speculative Newton" below). -/
def certify? (p : ZPoly) (strategy : AtomStrategy := .nkThenPellet) :
    Component → Option (Certified p)

/-- The starting component: a single square centred at 0 covering the
    Cauchy root bound, with `candidateK = deg p`. -/
def cauchy (p : ZPoly) (h : 0 < p.degree?.getD 0) : Component
end Component

/-- Repackage a certified `k = 1` cluster as an atom (the Pellet
    constructor of `AtomCertificate`). Total: the cluster's witness already
    lives on the enclosing square's disc, which is the atom's
    square. -/
def DyadicRootCluster.atomize (c : DyadicRootCluster p) (h : c.k = 1) :
    DyadicRootIsolation p

/-- Refine to `target` precision. First try a bounded lineage-local
    speculative pass; if it does not produce exactly one target-ready
    atom, restart from the input under the globally reglued complete
    loop. `none` only if the fallback has not emitted by
    `stopDepth p target` (see below). -/
def DyadicRootIsolation.refineTo? (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    Option (DyadicRootIsolation p)

/-- Refine every component until certified at prec ≥ target, with the
    certified stored squares' discs pairwise disjoint (see
    "Separation of the output" below). `none` only if this has not
    happened by `stopDepth p target`. -/
def isolateAll? (p : ZPoly) (target : Int) (worklist : Array Component)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (Array (Certified p))

/-- All-atoms output for polynomials with only simple roots: run
    `isolateAll?` from `Component.cauchy` with
    `target := max atom_prec (separationDepth p)`, and require every
    result to be an atom. `none` if `isolateAll?` fails or
    (impossible for squarefree `p`, proven in the companion) some
    result is a `k ≥ 2` cluster. `HasOnlySimpleRoots` does not force
    positive degree, so the degenerate inputs are pinned here: a
    nonzero constant returns `some #[]` (no roots to isolate), and
    the zero polynomial returns `none`. -/
def isolate (p : ZPoly) (h : Hex.HasOnlySimpleRoots p) (atom_prec : Int)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (Array (DyadicRootIsolation p))

/-- Start a local search from `seed`, return the first simple root certified,
    and refine it to at least `max atomPrec (mahlerPrec p)`. The result need
    not remain geometrically inside the seed. -/
def isolateOne? (p : ZPoly) (atomPrec : Int) (seed : DyadicSquare)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (RefinedIsolation p)
```

`certify?` computes one exact Taylor shift at its enclosing-square centre and
passes the same coefficient array to the exact witness and Newton kernels. The
soft Pellet scan tests every requested root count against each coefficient-ball
array before performing the next Graeffe transform; after a soft success, the
chosen count passes through the combined per-count kernel, retaining the
cached exact shift for an exact fallback and for its guarded Newton candidate.
The exact candidate-list fallback likewise shares one shift across every
failed `k`; only a speculative recentred candidate that reaches its witness
re-check needs a new shift. In the default Newton-then-Pellet route, the widened
Pellet square is concentric with the Newton enclosure, so an exact
centre-equality guard reuses the same shift across the strategy boundary as
well (and recomputes if that equality ever fails). A proof field indexes each
cached array by its polynomial and centre, so no exact coefficient-level
kernel can receive coefficients from another centre.

The speculative Newton step computes `x' = x − k · c₀/c₁` (with
`k = 1` for atoms; the k-order step for clusters is BSSY §5), places a
much smaller square at `x'`, and re-runs the witness. If the witness
certifies, the step gains quadratic precision. If not, the result is
discarded and subdivision proceeds. There is no a-priori "Newton
ready" precondition. The Gaussian inversion `1/c₁ = c̄₁ / |c₁|²` uses
`Dyadic.invAtPrec` for the single real reciprocal `1/|c₁|²`, which
both the real and imaginary components reuse. That is why the
implementation calls `invAtPrec` rather than two separate
`Dyadic.divAtPrec` divisions. The recentred components are rounded
down to precision `prec' + 3` (a quarter of the reciprocal's error
budget): certification never trusts the centre's provenance, so the
rounding is harmless, and it pins the working bit-length to the
complexity contract's `B`. Without it exact recentring compounds,
multiplying the centre's bit-length by roughly `2·deg p` per
accepted jump.

**Coverage guard.** The witness re-check alone is not a sufficient
acceptance criterion for a speculative Newton result. The separation
argument below counts on "the retained squares cover all roots", and
an unguarded jump can break that invariant silently: a recentred
square can certify `k` roots *elsewhere* while the roots the
component actually covered drift out of every retained region, and
pairwise disjointness cannot detect roots that are simply lost.
`certify?` therefore accepts a Newton result only when (a) the
component's own base region certifies the same count without the
jump, using the same certificate form, and (b) the recentred
certified region is contained in the base one. Because the recentred
attempt reuses the base form, the containment check compares like
regions, and each is one exact dyadic comparison: disc in disc
(radius difference squared against squared centre distance, the
same shape as the intersection test) for the Pellet form, square in
square (`max |Δre| |Δim| + r_new ≤ r_base`) for the
Newton-Kantorovich form. Same count plus containment makes the
sub-region's roots exactly the base region's roots, and coverage is
preserved. The guard costs one extra witness evaluation and never
blocks the intended use (sharpening an already certified region); a
jump whose base region fails to certify is discarded, and
subdivision proceeds as usual.

Acceptance is not the whole story: when a certified result re-enters
the worklist (its precision is still below target), the component
must retain a square that *covers* the certified region, not merely
the certified square itself. Refinement preserves exactly the roots
that lie in the retained squares (children partition the square and
the `T₀` discard is sound), while a Pellet certificate counts roots
in the stored square's circumscribed disc; a root in the disc but
outside the square would be silently lost by the next subdivision.
Repeated Newton-jump adoptions of a many-root cluster make this
concrete: the jumped disc keeps counting all `k` roots while
shrinking toward the cluster's Newton centroid, until far roots sit
in the disc but outside the retained square and vanish. Re-entry
therefore retains the doubled stored square (half-width
`2·2^{−prec}`, which contains the disc of radius `√2·2^{−prec}`),
costing one precision level, which the strictly-finer adoption rule
still absorbs.

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
depth lives inside `separationDepth` (below). Before

```
completenessDepth p target := max target (separationDepth p) + 5
```

each non-emitting driver round globally subdivides and reglues the complete
survivor set. Under either Pellet-bearing strategy, an opportunistic finisher
may emit earlier when every current attempt is an atom: it locally refines each
atom to `target`, then accepts the array only if every refinement succeeds and
the resulting discs are pairwise disjoint. Failure of any local refinement or
the final disjointness check returns to the unchanged global path. The NK-only
strategy retains its direct early emission when every current attempt is
already a target-ready atom with pairwise-disjoint discs. At the
normalized depth, every component is
root-bearing; the Mathlib companion proves that all three strategies
certify it as an atom and that the atom discs are pairwise disjoint.
Thus `isolate` returns `some` for every nonzero squarefree input.
`stopSlack` leaves three further rounds for the general driver and
non-squarefree inputs. A `none` from a driver means only that its full
emission condition was not reached within the fixed fuel bound; it does
not mean that no individual certificate appeared. Soundness remains
conditional on a `some` result for arbitrary inputs.

`isolateOne?` is the local counterpart for clients that need one certified
simple root rather than a complete root family. It starts from the caller's
untrusted seed, subdivides and certifies components until it finds an atom,
then refines that atom to `max atomPrec (mahlerPrec p)`. It tries every atom
certified in a round before subdividing again, so failure to refine one
candidate does not discard another. The returned `AtomCertificate` is a
self-contained proof that its certified region contains exactly one simple
root; soundness therefore does not require pairwise separation from atoms
outside that region. The seed chooses the initial search, not a containment
postcondition: survivor squares and their certified discs can extend outside
it. This weaker output is sufficient for `SimpleRoot.mk` and avoids refining
all roots merely to select one.

The one-atom `DyadicRootIsolation.refineTo?` wrapper first spends a fixed small
budget on the lineage-local transition, preserving the logarithmic precision
doubling of successful speculative Newton steps. That result is accepted only
when it is exactly one target-ready atom. If the pass exhausts its budget or
splits into an unsuitable worklist, refinement restarts from the original atom
under the globally reglued loop. Even a one-square start can subdivide into
sibling survivor lineages, including rootless halos, so this global fallback
is the completeness boundary. The Mathlib companion proves that the default
mixed strategy reaches the emission condition for every already refined
isolation, using local simplicity of the represented root; repeated roots
elsewhere in the ambient polynomial are permitted.

**Separation of the output.** Certification alone does not prevent
double-counting. A component whose squares contain no root (its
`T_0` tests merely failed to certify at this depth) can still pass
`certify?` with `k = 1` when its certified region overlaps a
neighbouring component and captures the neighbour's root. The driver
therefore emits a set of certified results only when the
circumscribed discs of their stored squares are **pairwise
disjoint** (one dyadic comparison per pair, as in the `SimpleRoot`
intersection test). Before normalization, the Pellet-bearing all-atoms
finisher starts only when the current atom discs are pairwise disjoint, then
requires every local refinement to reach `target` and the resulting discs to
remain pairwise disjoint; components failing that optional path return to
global subdivision. The NK-only route may directly emit an
already-ready all-atoms array. Components violating the ordinary check keep subdividing,
while a component already certified at target with a disc disjoint
from every other certified disc holds its position (continuing to
refine while waiting would double its precision every round through
Newton adoption, blowing the working bit-length whenever a sibling
is slow, e.g. a tight cluster forced down to its separation depth).
Every certified region is contained in its stored square's
circumscribed disc (the square itself for the Newton-Kantorovich
form, the enclosing disc for the Pellet form), so disjoint discs
count disjoint root sets. And the certified regions jointly cover
all roots: the `T_0` discard preserves coverage of every root by
the retained squares, a directly certified component's retained
squares lie inside its base certified region, and a
speculative-Newton region is accepted only when the coverage guard
proves it contains exactly the base region's roots. So the output
counts add up to exactly the root count. This is the
analogue of the separation condition in BSSY §4. During the uniform
global-refinement prefix, all retained squares are reglued together each
round. Consequently every component at `completenessDepth` contains its
associated root: a rootless survivor halo is adjacent to the component
containing that root and is glued into it. Only after this invariant has
been established may a non-emitting ready and disjoint component hold its
position; an all-atom worklist can instead emit early.

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

For the squarefree part of a nonzero `p ∈ ℤ[x]` of degree `n`, the Mahler
separation bound gives

```
sep(p) := min_{i ≠ j} |αᵢ − αⱼ| ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}
```

The integral radical has nonzero integer discriminant, hence absolute value at
least one; its Mahler measure is at most that of `p`. Combined with Landau's
`M(p) ≤ √(n+1) · ‖p‖∞`, this bounds the distance between distinct roots of
`p` from below in terms of `n` and `‖p‖∞` alone. `mahlerPrec p` is a `Nat`
such that the
circumscribed-disc radius at that precision is strictly below
`sep(p)/4`:

```
2^{−mahlerPrec p} · 1449/1024 < sep(p) / 4
```

The `/4` margin is what the `SimpleRoot` intersection test below
needs. The computation is pure integer arithmetic on the closed-form
bound (logarithms by repeated squaring). No discriminant is computed
at runtime; only the constant lower bound for the radical's discriminant is
used. Thus `mahlerPrec` is meaningful for every nonzero polynomial, including
a polynomial with repeated roots: multiplicities disappear in the integral
radical while its distinct roots are unchanged. The Mathlib companion proves
correctness; see
[hex-roots-mathlib.md](../../HexRootsMathlib/SPEC/hex-roots-mathlib.md).

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
conservative exact-fallback requirement; a successful Graeffe pass instead
needs only a fixed ratio.) The remaining `sepSlack`
covers the fixed factors: one level for the factor-2 witness slack,
at most two for the enclosing square of a multi-square component,
one for the circumscribed `√2`, and margin. The completeness
analysis certifies the formula without assuming a bounded-precision filter
succeeds, because soft failure is inconclusive. Consequently the static
worst-case depth retains the degree term. In ordinary runs, successful Graeffe
comparisons and the all-atoms finisher exit before this conservative global
depth. The remaining overshoot costs only extra subdivision rounds on inputs
where soft certification has not appeared. It is the depth bound used by
`stopDepth` above.

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

/-- A represented simple root forces its defining polynomial to have positive
    degree. -/
theorem SimpleRoot.posDegree (x : SimpleRoot p) :
    0 < p.degree?.getD 0

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

The committed refined-level operation is

```lean
def RefinedIsolation.refineTo? (r : RefinedIsolation p) (target : Int)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option {r' : RefinedIsolation p // SimpleRoot.mk r' = SimpleRoot.mk r}
```

which floors the target at `mahlerPrec p` (so the subtype re-wrap
always succeeds on a `some`) and derives the identity proof from the
decidable `Intersects` re-check via `Quot.sound`; and
`DyadicRootIsolation.toRefined?` records that an `isolate` output
meets the separation precision. `refineTo?` preserves the root
(`sameRoot r r' = true`, proved meaningful in the companion), so
callers can substitute the refined representative wherever the
original was used. Structures that contain
a representative (such as `AlgebraicNumber` in `hex-number-field`)
should store the refined value on return, so downstream consumers
inherit the precision. For the default `.nkThenPellet` strategy the companion
also proves that this option is always `some`; no corresponding totality claim
is made here for pure Pellet refinement of a non-squarefree ambient polynomial.

## Differences from BSSY

- **Bounded-precision Graeffe front end.** Graeffe iteration uses
  outward-rounded dyadic coefficient balls and a fixed significant-bit ladder,
  then falls back to the exact cached Taylor check. This gives the fixed-ratio
  behaviour of BSSY when the balls resolve the comparison while keeping the
  public witness a decidable exact-dyadic proposition. The conservative
  completeness depth still retains `ceilLog2 (deg p)` for the fallback path.
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
  Certification success plus the coverage guard is the acceptance
  criterion.
- **Dual atom certificates.** BSSY certify atoms with the same
  `T_1` test used for clusters. Here atoms additionally admit the
  Newton-Kantorovich contraction witness, and the two routes are
  carried side by side (strategy knob, shared conformance cases, a
  benchmark comparison group) until measurements and the companion's
  soundness development justify retiring one. Krawczyk-style
  contraction certificates have precedent in complex root isolation
  (Macaulay2 uses them); Newton-Kantorovich is the affine-invariant
  general form.

## File organisation

- `HexRoots/Basic.lean`: `DyadicSquare`, `DyadicComplexBall`,
  `Component`, `encSquare`, `Hex.HasOnlySimpleRoots`, and the small
  dyadic helpers (`abs`, `min`, `max`, ceiling log2) the rest of the
  library uses.
- `HexRoots/Taylor.lean`: exact Gaussian-dyadic Taylor expansion of a
  `ZPoly` at a Gaussian-dyadic centre, returning
  `Array (Dyadic × Dyadic)`.
- `HexRoots/SoftPellet.lean`: outward-rounded coefficient balls, locally
  scaled Taylor construction, Graeffe transforms with transported radii, and
  all-count soft Pellet / `T₀` scans.
- `HexRoots/Pellet.lean`: the dyadic bounds `lo`/`hi`, the rational
  `√2` constants with their `decide`-checked defining inequalities,
  the `witness` predicate and its `Decidable` instance,
  `DyadicRootCluster` (whose field mentions `witness`), and the ball
  view: `DyadicSquare.toBall`, the generic exact ball algebra, rational
  enclosure, the sound polynomial enclosure `evalBall`, and the ball tests
  `excludesZero`/`meets`/`meetsBall` that consumers
  (hex-number-field's disambiguation loops) use instead of re-deriving
  the `√2` radius bookkeeping.
- `HexRoots/Kantorovich.lean`: `nkWitness` with its `Decidable`
  instance, the decidable `atomWitness` checker proposition,
  `AtomCertificate` and its exact transport constructors, `AtomStrategy`, the
  certificate-indexed `DyadicRootIsolation`, `Certified`, and
  `atomize`, and `certifyAtom?` (certify an arbitrary candidate
  square, deciding both disjuncts fresh; the documented constructor
  for re-certification after a square transform).
- `HexRoots/MahlerPrec.lean`: the closed-form `mahlerPrec` and
  `separationDepth`.
- `HexRoots/Cauchy.lean`: `Component.cauchy`.
- `HexRoots/Newton.lean`: the speculative Newton step (atom and
  k-order component forms) using `Dyadic.invAtPrec`.
- `HexRoots/Bisection.lean`: 4-way subdivision, `T_0` discard,
  component gluing: `Component.refine1` and `Component.certify?`.
- `HexRoots/Refine.lean`: the shared fuel-based driver loops over the
  worklist, including the local first-refinable-atom search, `stopDepth`, the
  Φ termination measure discussion, and `DyadicRootIsolation.refineTo?` as a
  thin wrapper.
- `HexRoots/IsolateAll.lean`: `isolateAll?`, `isolate`, and the local
  `isolateOne?` entry point as thin wrappers over the shared driver loops, and
  the refined threading operation `RefinedIsolation.refineTo?` (below).
- `HexRoots/SimpleRoot.lean`: `RefinedIsolation`, `Intersects`,
  `SimpleRoot`, `sameRoot`, and the constructor
  `DyadicRootIsolation.toRefined?`; the threading-pattern guidance
  lives here as a docstring.
- `conformance/HexRoots/{Conformance,EmitFixtures}.lean` and
  `bench/HexRoots/Bench.lean`: the conformance and bench drivers, in
  the shared sub-projects.

## Conformance fixtures

Per [SPEC/testing.md](../../SPEC/testing.md), fixtures are tiered into
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
    coefficients in `[−10, 10]`, cross-checked against the python-flint
    oracle (below), plus the six curated atom/cluster cases retained for
    explicit simple/multiple-root coverage. Fresh emission of the full stream
    takes about 5.2 minutes on `chungus2`; at degree 20 the all-atoms local
    finisher supplies the speedup, while the size-gated soft front end is idle.
- *local* (developer-driven):
  - Adversarial families cross-checked against MPSolve: Mignotte
    `(n, a)` for `n ∈ {10, 20}` and `a ∈ {1000, 10⁶}`, the Wilkinson
    polynomial of degree 20, and products of two Mignotte polynomials
    with different parameters (close root pairs at two scales).

External oracles. The ci-tier oracle is
**[python-flint](https://github.com/flintlib/python-flint)**
(`fmpz_poly.complex_roots()`, which returns certified Arb balls with
multiplicities); it is already in the CI dependency set, consistent
with the standing oracle doctrine in
[SPEC/testing.md](../../SPEC/testing.md), and FLINT 3 subsumes Arb, so this
is also the "FLINT/Arb" role.
[MPSolve](https://github.com/robol/MPSolve) remains the local-tier correctness
oracle for the adversarial corpus; it is not a Phase-4 performance comparator
and is not wired into merge-facing CI. SageMath is not used (per
SPEC/testing.md's Sage policy).

For Phase 4 python-flint is classified `informational` (per
[SPEC/benchmarking.md §Comparator classification](../../SPEC/benchmarking.md#comparator-classification-gating-vs-informational)):
python-flint `fmpz_poly.complex_roots` is a multiprecision ball engine
computing approximate root inclusions, structurally different from this
library's decidable exact-integer Pellet / Newton-Kantorovich certificates,
so its ratios orient but do not gate, and the yardstick is the "Time budgets"
targets above rather than a constant-factor goal. It is scoped to the
whole-polynomial `runIsolate` and `runIsolateAll` surfaces. Separation-bound
calculation (`runMahlerPrec`), Taylor shift, witness checks, Newton steps,
component refinement/certification, refined-atom operations, and the individual
strategy routes are declared
**no-comparable-surface-in-named-comparator**: FLINT uses analogous kernels
internally but does not expose them as callable performance surfaces. The
classification and rationale are mirrored in
`libraries.yml: HexRoots.phase4.comparators`.

## Complexity contract

Write `n = deg p` and `B = prec + n · log ‖p‖∞` for the working
bit-length at precision `prec`.

- `mahlerPrec p` runs in `O(n · log ‖p‖∞)` integer operations.
- One exact witness check costs `O(n²)` exact-dyadic operations (the Taylor
  shift dominates) on `B`-bit values, so `O(n² · B²)` bit operations
  with schoolbook arithmetic. A soft pass costs `O(n²)` bounded-mantissa ball
  operations per Graeffe level; the number of levels is
  `O(log log n)`, and all candidate counts share each level. The fixed
  64/128/256-bit ladder therefore decouples a successful soft check from `B`;
  worst-case failure still pays the exact bound. The Newton-Kantorovich check has the
  same shape and cost, plus one `Dyadic.invAtPrec` call, and tests
  one radius where the Pellet form tests three.
- One Newton step costs the same order as one witness check, plus a
  single `Dyadic.invAtPrec` call. Within `certify?`, the witness and
  Newton kernels share one Taylor shift; the Pellet candidate-count
  search likewise pays one base shift rather than one per attempted
  count, and the default Newton-to-Pellet fallback reuses it because
  the two base squares are concentric. This does not change the
  asymptotic bound, but removes the repeated dominant `O(n²)` shift
  from those paths.
- `isolate` for degree `n`, well-separated roots, target precision
  `prec`: heuristically `O(n³ · B²)` bit operations. Tight root
  clusters add subdivision depth up to `O(mahlerPrec p)`.

## Time budgets (Phase 4 validation)

Regression ceilings anchored to measured reality (`chungus2`, AMD EPYC 9455,
96 logical CPUs with substantial idle capacity, Lean 4.32.0-rc1). Every pinned row runs the compiled expression
`isolateAll? (seededPoly degree) target #[Component.cauchy ...]`; this avoids
`isolate`'s higher `separationDepth` target and makes the stated precision the
actual driver target. Degree 10 and 20 use three measured cold calls with no
discarded warmup, degree 50 uses two, and degree 100 uses one. The direct
driver prints and checks the returned atom count; unlike the canonical fixed
benchmarks, the one- and two-call large rows have no five-repeat digest sample:

- Degree 10, prec 32: under 0.3 seconds (median 0.130 s, range
  0.129–0.131 s).
- Degree 20, prec 32: under 7 seconds (median 3.433 s, range
  3.421–3.436 s). This is the scale `hex-number-field` consumes.
- Degree 50, prec 64: under 105 seconds (range 52.234–52.289 s).
- Degree 100, prec 128: under 21 minutes (measured 630.421 s,
  10.51 minutes).

These are ceilings for regression detection, not aspirations. The original
rough first guesses (1 s / 10 s / 1 min) remain stretch targets; degree 10 is
now comfortably below its aspiration, while the larger rows retain roughly
2× regression margin over the measurements. Issue
https://github.com/kim-em/hex-dev/issues/8751
records the Graeffe, soft-Pellet, Taylor-reuse, and local-finisher ratchet. Any
later improvement re-measures the table and tightens the ceilings again rather
than accumulating slack.
MPSolve remains a local correctness oracle. The declared informational
performance comparator is python-flint, whose measured ratios are recorded in
[`reports/hex-roots-performance.md`](../../reports/hex-roots-performance.md).

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
- Kantorovich, Akilov. *Functional Analysis*, 2nd ed., Pergamon,
  1982, §XVIII. The Newton-Kantorovich theorem behind `nkWitness`.
- Mehta, Macbeth. Newton-Kantorovich over Mathlib, in
  https://github.com/xgenereux/certifying-lmfdb-data
  (`CertifyingLmfdbData/Polynomial/NewtonKantorovich.lean`,
  Apache 2.0). The formalisation the Mathlib companion ports for
  the `nkWitness` soundness theorem.
