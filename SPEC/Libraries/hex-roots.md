# hex-roots (complex root isolation, depends on hex-poly-z)

Certified isolation of complex roots of integer-coefficient
polynomials. A "root isolation" is a Gaussian-dyadic centre and a
dyadic-power-of-two radius together with a witness, dischargeable by
`cbv_decide`, that the disc contains exactly one simple root (atom) or
exactly `k` roots with multiplicity (cluster). Refinement combines
speculative Newton iteration (using `Dyadic.invAtPrec` from the Lean
standard library) with subdivision-and-component-gluing as the
bootstrap phase, following the hybrid algorithm of Becker–Sagraloff–
Sharma–Yap, *J. Symbolic Computation* 86 (2018) 51–96 (arXiv:1509.06231;
"BSSY" hereafter).

## Witness arithmetic is exact

A `ZPoly` evaluated at a Gaussian-dyadic point `(a + b·i)` yields
Taylor coefficients

```
cₖ = Σ_{j ≥ k} binomial(j,k) · aⱼ · (a + b·i)^{j−k}
```

each term an integer times a Gaussian-dyadic power, hence
`cₖ ∈ Dyadic[i]` *exactly*. `|cₖ|² = (Re cₖ)² + (Im cₖ)²` is then an
exact dyadic. Every witness in this library is a strict comparison
between two exact dyadics — `Decidable` with no error budget. The
Newton step itself uses `Dyadic.invAtPrec` and is approximate, but the
witness re-check after Newton uses the new exact dyadic centre and is
again exact. This eliminates an entire category of "interval
arithmetic" infrastructure that one might naïvely expect.

## Geometry: dyadic squares, circumscribed discs, squared radii

Subdivision works on dyadic squares (4-way clean partition); Pellet
tests live on the **circumscribed disc** of each square. For a square
of half-width `r = 2^{-prec}`, the circumscribed disc has radius `r·√2`.
To keep all arithmetic dyadic, **every appearance of a radius in a
witness is replaced by the squared form**. The `T_k`-inequality
becomes `|cₖ|² · (r²·2)^k > S²` rather than `|cₖ|·(r·√2)^k > S`. The
strong-witness `2·`-radius and `4·`-radius checks become `8r²` and
`32r²` respectively. A single named lemma
`circumscribed_radius_squared : (r·√2)² = 2·r²` is checked once;
afterwards no `√2` appears.

## Contents

```lean
namespace Hex

structure DyadicSquare where
  re   : Dyadic
  im   : Dyadic
  prec : Nat
  -- half-width is 2^{-prec}; circumscribed disc has radius² = 2 · 4^{-prec}

structure DyadicRootIsolation (p : ZPoly) where
  square  : DyadicSquare
  witness : witness₁ p square    -- T_1 squared form on the circumscribed disc

structure DyadicRootCluster (p : ZPoly) where
  square  : DyadicSquare
  k       : Nat                  -- ≥ 1
  k_pos   : 0 < k
  witness : witnessₖ p square k  -- strong T_k on disc, on 2·-radius, on 4·-radius

/-- p has only simple complex roots. Default-decidable via
`Hex.HasOnlySimpleRoots.decide` (gcd(p, p') is a unit). The Mathlib
companion proves equivalence with `Squarefree (toPolynomial p)`. -/
def HasOnlySimpleRoots (p : ZPoly) : Prop := …
instance : Decidable (HasOnlySimpleRoots p) := …
```

Both `witness₁` and `witnessₖ` are `Decidable` Props built directly
from dyadic comparisons; the structure-level `cbv_decide` on a fully-
elaborated `DyadicRootIsolation p` value can prove the witness
holds. The "no roots on the boundary circle" property of every
isolation and cluster is implicit in the strict inequality and
exposed as a derived lemma in the Mathlib companion.

## Operations

```lean
namespace DyadicRootIsolation
def refine1?  : DyadicRootIsolation p → Option (DyadicRootIsolation p)
def refine?   : (target : Nat) → DyadicRootIsolation p → Option (DyadicRootIsolation p)
end DyadicRootIsolation

namespace DyadicRootCluster
def refine1? : DyadicRootCluster p → Option (Array (DyadicRootCluster p ⊕ DyadicRootIsolation p))
def cauchy   : (p : ZPoly) → DyadicRootCluster p
def atomize  : (c : DyadicRootCluster p) → c.k = 1 → DyadicRootIsolation p
end DyadicRootCluster

/-- Refine every cluster in the worklist until each has prec ≥ target. -/
def isolateAll? (target : Nat) (worklist : Array (DyadicRootCluster p)) :
    Option (Array (DyadicRootCluster p))

/-- All-atoms output for polynomials with no multiple roots. Implementation:
    take target := max atom_prec (mahlerPrec p), then atomize. -/
def isolate (p : ZPoly) (h : Hex.HasOnlySimpleRoots p) (atom_prec : Nat) :
    Option (Array (DyadicRootIsolation p))
```

`refine1?` (both atom and cluster) tries a speculative Newton step
first, then falls back to bisection on failure. Newton uses
`Dyadic.invAtPrec` for the Gaussian inversion `1/c₁ = c̄₁ / |c₁|²`;
**we explicitly use `invAtPrec` rather than a hypothetical
`divAtPrec`** because both the real and imaginary components of
`c̄₁ / |c₁|²` reuse the same real reciprocal `1/|c₁|²`, so a
precomputed reciprocal beats two separate divisions. The new candidate
disc is recertified by re-running the witness; on failure (witness
fails for the candidate disc), bisection is the fallback.

Bisection 4-way-partitions a square into sub-squares of one bit higher
precision, runs the `T_0` (no-roots) and `T_1` / `T_k` (`k`-roots)
tests on each sub-square's circumscribed disc, discards `T_0`-positive
sub-squares, and glues the remaining undecided / positive sub-squares
into edge-connected components (BSSY, §4). The cluster-level test
runs on the disc circumscribing the connected-component square.

`refine?` for a single isolation terminates by `target − iso.prec : Nat`
(strictly decreasing). `isolateAll?` terminates by

```
Φ(W) := Σ_{c ∈ W, c.prec < target} (4^(target − c.prec) − 1)
```

which strictly decreases by at least 3 per `refine1?` step (a cluster
at prec `p` is replaced by at most 4 children at prec `p+1`; the
contribution changes from `4^(target−p) − 1` to at most
`4 · (4^(target−p−1) − 1) = 4^(target−p) − 4`). `isolate` is a thin
wrapper over `isolateAll?` and inherits termination.

`isolate` returns `none` only if some primitive `refine1?` step has
returned `none`. The Mathlib companion proves: under
`Hex.HasOnlySimpleRoots`, the result is always `some` and contains
exactly the simple-root set of `p` as atoms refined to ≥ `atom_prec`.

For polynomials with multiple roots, there is no `isolate` analog.
Use `isolateAll?` directly; multiple-root clusters never atomise (the
`T_1` witness fails identically because `c₁ → 0` near a multiple root)
and surface in the output with their `k ≥ 2` field.

## `mahlerPrec` — termination bound for atomisation

```lean
def mahlerPrec (p : ZPoly) : Nat
```

For squarefree `p ∈ ℤ[x]` of degree `n` with sup-norm `‖p‖∞`, the
Mahler/Mignotte separation bound says

```
min_{i ≠ j} |αᵢ − αⱼ| ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}
```

Combined with `|disc p| ≥ 1` (nonzero integer for squarefree `p`) and
Landau's `M(p) ≤ √(n+1) · ‖p‖∞`, this gives a closed-form lower bound
on root separation in terms of `n` and `‖p‖∞` only. `mahlerPrec`
returns a `Nat` such that bisecting to half-width `2^{-mahlerPrec p}`
suffices to separate any two distinct roots. Pure integer arithmetic;
no discriminant computation at runtime (we only need the lower bound
`|disc p| ≥ 1`, not `disc p` itself). The Mathlib companion proves
correctness — see [hex-roots-mathlib.md](hex-roots-mathlib.md).

## `SimpleRoot` quotient and the `refine`/`out` threading pattern

The Mathlib-free quotient type:

```lean
namespace Hex
def SimpleRoot (p : ZPoly) := Quotient (DyadicRootIsolation.setoid p)

/-- Two isolations are equivalent iff they isolate the same simple
    root of `p`. Generated by direct disc containment; symmetric and
    transitive closure. Decidable via the Mahler separation bound. -/
instance DyadicRootIsolation.setoid (p : ZPoly) :
    Setoid (DyadicRootIsolation p) := …

instance : DecidableEq (SimpleRoot p) := Quotient.decidableEq

namespace SimpleRoot
def mk (iso : DyadicRootIsolation p) : SimpleRoot p := Quotient.mk _ iso
end SimpleRoot
end Hex
```

Decidability of the equivalence: refine both isolations to precision
`mahlerPrec p`; then either one disc strictly contains the other (→
equivalent) or the discs are disjoint (→ not equivalent). `mahlerPrec
p` is finite for any `p ∈ ℤ[x]` — note that the Mahler bound on
*distinct* roots applies even when `p` itself is not squarefree, since
`p_sf | p` gives `M(p_sf) ≤ M(p)` and `|disc p_sf| ≥ 1`.

### Computable `out` via canonicalisation

```lean
def SimpleRoot.out (s : SimpleRoot p) (prec : Nat) : DyadicRootIsolation p
```

The canonicalisation: refine the underlying iso to precision
`max prec (mahlerPrec p + canonOverhead p)` (where `canonOverhead p`
shifts away from dyadic boundaries — `log₂ ‖p‖∞ + 1` suffices, since
real dyadic roots `a/2^k` of `p ∈ ℤ[x]` have `2^k | lc(p)` by the
rational root theorem, hence `k ≤ log₂ ‖p‖∞`), then round each
coordinate down to a multiple of `2^{−prec}`, then re-check the
witness on the resulting (coarser) disc. The construction is
deterministic on the equivalence class — different equivalent isos
produce the same dyadic centre after canonicalisation, so `out` is
well-defined as a `Quotient.lift`.

### `refineTo`, `refine`, and the threading pattern

For efficiency: if the underlying iso is already at precision ≥
target, the canonicalisation's refinement loop should short-circuit.
Two new operations support this:

```lean
def DyadicRootIsolation.refineTo (iso : DyadicRootIsolation p)
    (target : Nat) : DyadicRootIsolation p :=
  if iso.prec ≥ target then iso else <do refinement work>

theorem refineTo_respects_equiv {iso₁ iso₂ : DyadicRootIsolation p} (target : Nat)
    (h : iso₁ ≈ iso₂) : iso₁.refineTo target ≈ iso₂.refineTo target

def SimpleRoot.refine (s : SimpleRoot p) (target : Nat) : SimpleRoot p :=
  Quotient.map (·.refineTo target) refineTo_respects_equiv s
```

Key facts:

- `s.refine target = s` *propositionally*, by `Quotient.sound` plus
  `refineTo_respects_equiv`. Refining never changes the abstract
  identity of the simple root.
- The internal *computational* representative of `s.refine target`
  is `iso.refineTo target`. When that's already at precision ≥
  target, this is the identity (zero work).
- `Quotient.lift_mk`'s definitional reduction guarantees that calls
  to `s.out prec` operate on the underlying representative directly,
  so when the rep has precision ≥ `mahlerPrec p + canonOverhead p`,
  `out`'s canonicalisation is *just* a round-down + witness re-check
  — no refinement loop.

**Performance contract.** If the internal representative of `s` has
precision ≥ `mahlerPrec p + canonOverhead p`, then `s.out prec` runs
in `O(deg p · prec²)` bit operations regardless of `prec`. If the
internal representative is below that threshold, `out` does
refinement work that scales with the gap.

### The threading pattern

`SimpleRoot` is a Quotient, so `s.refine t = s` propositionally.
But the value Lean computes with is *the refined representative*.
Code that holds a `SimpleRoot` and may call `out` repeatedly should
refine once and thread the refined value forward:

```lean
-- DON'T: each `out` call re-does refinement
def slow (s : SimpleRoot p) : Foo :=
  let a := s.out 32
  let b := s.out 64    -- re-refines if rep is small
  ...

-- DO: refine once, thread refined value forward
def fast (s : SimpleRoot p) : SimpleRoot p × Foo :=
  let s' := s.refine (mahlerPrec p + canonOverhead p)
  let a := s'.out 32   -- cheap (rep is already refined)
  let b := s'.out 64   -- cheap
  (s', ...)            -- caller stores `s'` going forward
```

Because `s' = s` propositionally, callers can transparently
substitute the refined value wherever the original was used.
Functions producing data that contains a `SimpleRoot` field (e.g.
`AlgebraicNumber` in `hex-number-field`) should set that field to
the refined value, so downstream consumers automatically benefit.

## Algorithm exposition

The library implements the BSSY hybrid `subdivide → glue → speculative
Newton` loop, restricted to simple `T_1` witnesses for atoms and `T_k`
witnesses for clusters. Specific differences from BSSY:

- **No Graeffe iteration.** Deferred as a future optimisation; without
  it, `T_k` requires the disc to be `(2√2/3, 4/3)`-isolating, which is
  brittle for very tight clusters but adequate for typical inputs.
- **No squarefree preprocessing.** Honest multiple roots cannot satisfy
  the `T_1` simplicity-implying inequality at any radius (because
  `c₁ → 0`), so they correctly stay as `k ≥ 2` clusters. Squarefree
  inputs atomise; non-squarefree inputs surface the multiple roots as
  clusters.
- **Squares for partition; circumscribed discs for tests.** Squares
  4-way partition without overlap; circumscribed discs harmlessly
  over-count, but discarding via `T_0` and component-gluing recovers
  the exact root distribution. (BSSY §4.)
- **Speculative Newton, then re-test.** No a priori `newtonReady`
  precondition; we just take the Newton step and re-run the witness on
  the result. If it certifies, we earned quadratic convergence; if
  not, we fall back to bisection.

## Layered file organisation

- `HexRoots/Basic.lean` — types: `DyadicSquare`, `DyadicRootIsolation`,
  `DyadicRootCluster`, `Hex.HasOnlySimpleRoots`. Also defines the
  setoid for the equivalence on `DyadicRootIsolation`, the quotient
  `SimpleRoot p`, decidable equality, `mk`, and `out`.
- `HexRoots/Refine.lean` — `DyadicRootIsolation.refineTo` (with
  short-circuit), `refineTo_respects_equiv`, `SimpleRoot.refine`,
  and the `s.refine target = s` lemma. The threading-pattern
  guidance lives here as a docstring on `SimpleRoot.refine`.
- `HexRoots/Taylor.lean` — exact Gaussian-dyadic Taylor expansion of
  a `ZPoly` at a Gaussian-dyadic centre. Returns the array
  `(c₀, c₁, ..., c_n) : Array (Dyadic × Dyadic)`.
- `HexRoots/Pellet.lean` — `T_0`, `T_1`, `T_k` squared-form witness
  predicates and their `Decidable` instances.
- `HexRoots/MahlerPrec.lean` — the closed-form `mahlerPrec` function.
- `HexRoots/Cauchy.lean` — `DyadicRootCluster.cauchy` constructor.
- `HexRoots/Newton.lean` — speculative Newton step using
  `Dyadic.invAtPrec`; `DyadicRootIsolation.refine1?` and `refine?`.
- `HexRoots/Bisection.lean` — 4-way subdivision, component gluing,
  `DyadicRootCluster.refine1?`.
- `HexRoots/IsolateAll.lean` — `isolateAll?` driver and the `isolate`
  convenience wrapper.
- `HexRoots/Conformance.lean`, `HexRoots/Bench.lean`,
  `HexRoots/EmitFixtures.lean` — the standard testing trio.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md), fixtures are tiered into
`core` / `ci` / `local`. **Adversarial deterministic families take
precedence over random samples** because random small-coefficient
polynomials are weak at exposing clustered-root pathologies.

- *core* (Lean-only, runs on every push):
  - Sanity polynomials with rational roots: `(x−1)(x−2)(x+3)`, `x³ − x`.
  - Cyclotomic Φ_n for `n ∈ {5, 7, 12}` — roots are roots of unity.
  - Chebyshev T_n for `n ∈ {5, 10}` — roots at known `cos((2k−1)π/(2n))`.
  - Small Mignotte `xⁿ − (a·x − 1)²` for `n = 5`, `a = 100`.
  - Multiple-root case `(x²+1)·(x−5)²` — verifies that the `k = 2`
    cluster around `5` does not atomise.
- *ci* (CI, with external oracle when available):
  - 50 degree-20 polynomials with deterministic seed `0xHEC0FFEE` and
    coefficients in `[−10, 10]`. Expected outputs serialised from
    a local oracle run during fixture emission.
- *local* (developer-driven):
  - MPSolve-driven adversarial families: Mignotte `(n, a)` for
    `n ∈ {10, 20}` and `a ∈ {1000, 10⁶}`, Wilkinson 20, Bring
    quintics, Smale-pathological products.

External oracles (in role order): MPSolve (primary, Brew-installable);
FLINT/Arb (secondary, for cases where MPSolve precision is suspect);
SageMath (fallback).

## Complexity contract

- `mahlerPrec p` runs in `O(n · log ‖p‖∞)` integer operations
  (logarithm by repeated squaring on the closed-form bound).
- One `T_k` witness check at squared half-width `2^{-prec}` costs
  `O(n²)` exact-dyadic operations on coefficients of bit-length
  `O(prec + n · log ‖p‖∞)`, i.e. `O(n²·B²)` bit operations
  schoolbook.
- One Newton step costs the same order as one witness check, plus a
  single `Dyadic.invAtPrec` call.
- `isolate` for degree `n`, well-separated roots, target precision
  `prec`: heuristically `O(n³ · B²)` bit operations. For tight
  clusters add a `log(1/separation)` factor, bounded by
  `mahlerPrec p` in the worst case.

## Time budgets (Phase 4 validation)

These are rough first guesses, to be refined against MPSolve on the
same fixtures during Phase 4:

- Degree 10, prec 32: < 1 second.
- Degree 50, prec 64: < 10 seconds.
- Degree 100, prec 128: < 1 minute.

## References

- Becker, Sagraloff, Sharma, Yap. *A near-optimal subdivision
  algorithm for complex root isolation based on the Pellet test and
  Newton iteration.* J. Symbolic Computation 86 (2018) 51–96.
  arXiv:1509.06231. **The reference**; pseudocode for everything in
  this library traces back to this paper.
- Imbach, Pan, Yap. *Implementation of a near-optimal complex root
  clustering algorithm (Ccluster).* ICMS 2018, LNCS 10931. The C/Arb
  implementation paper, with the soft-Pellet filter optimisations.
- Pellet. *Sur un mode de séparation des racines des équations et la
  formule de Lagrange.* Bull. Sci. Math. 5 (1881) — origin of `T_k`.
- Mahler. *On some inequalities for polynomials in several variables.*
  J. London Math. Soc. 37 (1962) — original separation bound.
- Mignotte. *Some useful bounds.* Computer Algebra: Symbolic and
  Algebraic Computation, 1982. Standard textbook simplification of
  Mahler.
