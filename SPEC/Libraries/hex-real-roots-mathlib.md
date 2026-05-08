# hex-real-roots-mathlib (depends on hex-real-roots + hex-poly-z-mathlib + hex-resultant-mathlib + Mathlib)

Mathlib bridge for [hex-real-roots](hex-real-roots.md). Proves
correctness of the certified real root isolation against Mathlib's
`Polynomial ℤ` and `ℝ`-root semantics.

## What we cite from Mathlib (no work)

- `Polynomial.IsRoot`, `Polynomial.roots`, `Polynomial.aroots`.
- `Polynomial.derivative`, `Polynomial.gcd`, `Polynomial.Squarefree`.
- The cast `Polynomial.eval₂` from `Polynomial ℤ` to `ℝ`-valued
  evaluation.
- `Real`'s ordered-field structure (signs, comparisons,
  Intermediate Value Theorem).
- `EuclideanDomain.gcd` over `ℤ[x]`.

## Bridging theorems

### `SimpleRealRoot p` semantics

```lean
/-- The real number corresponding to a real-root isolation: any
    point in the interval, made canonical by refinement to a target
    precision and centred-residue choice. The Mathlib version does
    *not* depend on the specific refinement; it picks out the
    unique real root in the isolation's interval. -/
def SimpleRealRoot.toReal {p : ZPoly} (s : SimpleRealRoot p) : ℝ

theorem SimpleRealRoot.toReal_isRoot {p : ZPoly} (s : SimpleRealRoot p)
    (hp : Hex.HasOnlySimpleRealRoots p) :
    (toPolynomial p).aeval s.toReal = 0
  -- s.toReal is a real root of (toPolynomial p)

theorem SimpleRealRoot.toReal_in_interval
    {p : ZPoly} (s : SimpleRealRoot p) (prec : Nat) :
    let iso := s.out prec
    (iso.interval.lower : ℝ) < s.toReal ∧ s.toReal ≤ (iso.interval.upper : ℝ)

theorem SimpleRealRoot.injective_to_real
    {p : ZPoly} (hp : Hex.HasOnlySimpleRealRoots p) :
    Function.Injective (SimpleRealRoot.toReal (p := p))
```

### Sturm's theorem

If Mathlib already has Sturm's theorem in a usable form, cite it.
Otherwise, prove it inline (with attribution to any open Mathlib
PR that's in flight). The contract:

```lean
theorem sturm_count_eq_real_root_count
    (p : ZPoly) (hp : Hex.HasOnlySimpleRealRoots p)
    (a b : Dyadic) (ha : (toPolynomial p).aeval (a : ℝ) ≠ 0)
    (hb : (toPolynomial p).aeval (b : ℝ) ≠ 0) (hab : a < b) :
    sturmCount p ⟨a, b, hab⟩ =
      ((toPolynomial p).roots.filter
          (fun r => (a : ℝ) < r ∧ r ≤ (b : ℝ))).card
  -- The integer Sturm count over (a, b] equals the number of real
  -- roots in (a, b], counted with multiplicity (which is 1 for
  -- squarefree p).
```

Status of Mathlib's existing Sturm infrastructure should be checked
at activation time. If absent, port inline per
[PLAN/Conventions.md §"Library placement"](../../PLAN/Conventions.md)'s
"inline with attribution" rule.

### `cauchyBound` correctness

```lean
theorem cauchyBound_bounds_real_roots (p : ZPoly) :
    ∀ r : ℝ, (toPolynomial p).aeval r = 0 →
        |r| ≤ (Hex.cauchyBound p : ℝ)
  -- |any real root of p| ≤ cauchyBound p
```

Standard Cauchy-bound proof: if `|r| > 1 + max|a_i|/|a_n|`, the
leading term dominates and `p(r) ≠ 0`.

### `realRootSeparation` correctness

```lean
theorem realRootSeparation_bounds_min_gap
    (p : ZPoly) (hp : Hex.HasOnlySimpleRealRoots p) :
    ∀ r₁ r₂ : ℝ, (toPolynomial p).aeval r₁ = 0 →
                 (toPolynomial p).aeval r₂ = 0 → r₁ ≠ r₂ →
        (2 : ℝ)^(-(Hex.realRootSeparation p : ℝ)) ≤ |r₁ - r₂|
```

Mahler/Mignotte bound applied to real roots. Mathlib has Mahler
measure infrastructure in `Mathlib.Analysis.Polynomial.MahlerMeasure`;
Landau's inequality wraps as `mahlerMeasure_le_l2norm`.

### `isolate` correctness

```lean
theorem isolate_correct
    (p : ZPoly) (hp : Hex.HasOnlySimpleRealRoots p) (prec : Nat) :
    let isolations := Hex.isolate p hp prec
    -- (1) every real root of p has exactly one isolation:
    (∀ r : ℝ, (toPolynomial p).aeval r = 0 →
        ∃! iso ∈ isolations.toList,
          (iso.interval.lower : ℝ) < r ∧ r ≤ (iso.interval.upper : ℝ)) ∧
    -- (2) every isolation contains a real root of p:
    (∀ iso ∈ isolations.toList,
      ∃ r : ℝ, (toPolynomial p).aeval r = 0 ∧
               (iso.interval.lower : ℝ) < r ∧ r ≤ (iso.interval.upper : ℝ)) ∧
    -- (3) isolations are pairwise disjoint:
    isolations.toList.Pairwise (fun a b => Disjoint a.interval b.interval)
```

Bijection between the isolation array and the (finite) set of real
roots of `p`. Follows from `sturm_count_eq_real_root_count` plus the
bisection-driver's invariants.

### Refinement correctness

```lean
theorem refine_eq (s : SimpleRealRoot p) (target : Nat) :
    s.refine target = s
  -- propositional equality; the underlying representative changes
  -- but the abstract identity is unchanged.

theorem out_real_eq (s : SimpleRealRoot p) (prec₁ prec₂ : Nat) :
    s.toReal = s.toReal
  -- toReal does not depend on the precision used by out.
```

## Mathlib gap analysis

To verify when drafting; first-cut estimate from the theorem
statements above:

**Cite directly (no work expected):**
- `Polynomial.IsRoot`, `Polynomial.roots` over `ℝ` and `ℤ`.
- `Polynomial.derivative`, `Polynomial.gcd`.
- Mahler measure infrastructure (`mahlerMeasure_le_l2norm`).

**Possibly build (verify status at activation time):**
- A direct version of Sturm's theorem connecting integer-Sturm-
  sequence sign counts to real-root counts. Mathlib may have
  fragments; full theorem may need assembly.
- The `realRootSeparation` bound: like `mahlerPrec` in
  `hex-roots-mathlib`, this is a paper result (Mahler 1962 /
  Mignotte 1982) restricted to real roots; Mathlib likely doesn't
  have the closed form; port inline with attribution.

## Layered file organisation

```
HexRealRootsMathlib/
  Basic.lean        — toReal, Quotient bridge
  Sturm.lean        — sturm_count_eq_real_root_count
  Cauchy.lean       — cauchyBound_bounds_real_roots
  Separation.lean   — realRootSeparation_bounds_min_gap
  Isolate.lean      — isolate_correct
  Conformance.lean  — fixture-based checks
```

## References

- Sturm 1829, Marden 1966, Basu-Pollack-Roy 2006 — see
  [hex-real-roots](hex-real-roots.md) §"References".
- For the Mahler/Mignotte bounds restricted to real roots: same
  sources as [hex-roots-mathlib](hex-roots-mathlib.md)'s `mahlerPrec`
  proof, applied to the real subset.
