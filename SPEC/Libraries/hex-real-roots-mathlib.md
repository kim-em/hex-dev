# hex-real-roots-mathlib (depends on hex-real-roots + hex-poly-z-mathlib + Mathlib)

Mathlib bridge for [hex-real-roots](hex-real-roots.md). Proves
correctness of the certified real-root isolation against Mathlib's
`Polynomial ℤ` and `ℝ`-root semantics. Uspensky's algorithm
(Descartes + Möbius bisection) — the bridge rides on Mathlib's
existing `Polynomial.signVariations` infrastructure rather than
formalising Sturm's theorem from scratch.

## What we cite from Mathlib (no work)

- `Polynomial.IsRoot`, `Polynomial.roots`, `Polynomial.aroots`.
- `Polynomial.derivative`, `Polynomial.gcd`, `Polynomial.Squarefree`.
- `Polynomial.eval₂` for `Polynomial ℤ → ℝ`-valued evaluation.
- `Polynomial.signVariations` and the main theorem
  `Polynomial.roots_countP_pos_le_signVariations` from
  `Mathlib.Algebra.Polynomial.RuleOfSigns`.
- `Polynomial.comp` for polynomial composition (used to express
  Möbius transforms).
- `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau)
  and `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`
  (Mignotte) from `Mathlib.Analysis.Polynomial.MahlerMeasure`.
- `Real`'s ordered-field structure and Intermediate Value Theorem
  (`intermediate_value_Icc` etc.).

## Bridging theorems

### `SimpleRealRoot p` semantics

```lean
/-- The real number corresponding to a real-root isolation. The
    Mathlib version does *not* depend on the specific refinement; it
    picks out the unique real root in the isolation's interval. -/
def SimpleRealRoot.toReal {p : ZPoly} (s : SimpleRealRoot p) : ℝ

theorem SimpleRealRoot.toReal_isRoot {p : ZPoly} (s : SimpleRealRoot p)
    (hp : Hex.HasOnlySimpleRealRoots p) :
    (toPolynomial p).aeval s.toReal = 0

theorem SimpleRealRoot.toReal_in_interval
    {p : ZPoly} (s : SimpleRealRoot p) (prec : Nat) :
    let iso := s.out prec
    (iso.interval.lower : ℝ) < s.toReal ∧ s.toReal ≤ (iso.interval.upper : ℝ)

theorem SimpleRealRoot.injective_to_real
    {p : ZPoly} (hp : Hex.HasOnlySimpleRealRoots p) :
    Function.Injective (SimpleRealRoot.toReal (p := p))
```

### Descartes' rule of signs on Möbius transforms

The core bridge theorem connecting `signVariations` of the
Möbius-transformed polynomial to the real-root count of `p` in the
interval.

```lean
/-- The integer Möbius transform of p relative to (a, b]:
    p_M(x) := (1+x)^(deg p) · p(a + (b-a)/(1+x)) cleared of dyadic
    denominators. -/
def mobiusTransform (p : ZPoly) (a b : Dyadic) : ZPoly := …

/-- Möbius transform sends positive reals to (a, b) bijectively, with
    multiplicities. Stated as a multiset equality on real roots: the
    positive real roots of `p_M` (with multiplicity) correspond, via
    `s ↦ (b − s)/(s − a)`, to the real roots of `p` in `(a, b)` (with
    multiplicity). -/
theorem mobiusTransform_root_correspondence
    (p : ZPoly) (a b : Dyadic) (hab : a < b) :
    let pℝ  := (toPolynomial p).map (Int.castRingHom ℝ)
    let pMℝ := (toPolynomial (mobiusTransform p a b)).map (Int.castRingHom ℝ)
    pMℝ.roots.filter (0 < ·)
      = (pℝ.roots.filter (fun s => (a : ℝ) < s ∧ s < (b : ℝ))).map
          (fun s => ((b : ℝ) - s) / (s - (a : ℝ)))
```

### Descartes count → exact-1 corollary

Mathlib's `roots_countP_pos_le_signVariations` is stated for
`Polynomial R` over a linearly ordered ring `R`; instantiated at
`R = ℤ` it counts integer roots, but for the bridge we need real
roots. The corollaries are stated over `q.map (Int.castRingHom ℝ)`:

```lean
theorem signVariations_eq_one_implies_one_positive_real_root
    (q : Polynomial ℤ) (hsv : q.signVariations = 1) :
    ((q.map (Int.castRingHom ℝ)).roots.filter (0 < ·)).card = 1
  -- Proof: signVariations is preserved by the cast (auxiliary
  -- lemma below), so `(q.map ...).signVariations = 1`. Mathlib's
  -- `roots_countP_pos_le_signVariations` over ℝ gives count ≤ 1.
  -- The parity strengthening (count ≡ signVariations mod 2) gives
  -- count = 1.

theorem signVariations_eq_zero_implies_no_positive_real_roots
    (q : Polynomial ℤ) (hsv : q.signVariations = 0) :
    ((q.map (Int.castRingHom ℝ)).roots.filter (0 < ·)).card = 0
  -- Mathlib over ℝ: count ≤ 0, plus signVariations cast-invariance.
```

Two auxiliary lemmas these depend on:

- **`signVariations` cast-invariance**: `(q.map (Int.castRingHom ℝ)).signVariations = q.signVariations`.
  `signVariations` reads off the sign sequence of nonzero
  coefficients; `Int.castRingHom ℝ` is sign-preserving and
  injective, so the two sequences agree. If Mathlib has a generic
  `signVariations_map` for sign-preserving ring homs, cite directly;
  otherwise local lemma.
- **Parity strengthening**: `count ≡ signVariations (mod 2)`. The
  standard companion to Descartes' rule; if Mathlib's
  `RuleOfSigns.lean` has it, cite directly, otherwise local.

### LMQ bound correctness

```lean
theorem lmqBound_bounds_positive_real_roots (p : ZPoly) :
    ∀ r : ℝ, (toPolynomial p).aeval r = 0 → 0 < r →
        r ≤ (Hex.lmqBound p : ℝ)
  -- Akritas–Strzeboński 2008 LMQ bound, stated for positive reals.
```

Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound` is the closest
upstream analogue; LMQ is independent of it (sharper, with a
different proof) and the bridge does not factor through Cauchy.

### `realRootSeparation` correctness

```lean
theorem realRootSeparation_bounds_min_gap
    (p : ZPoly) (hp : Hex.HasOnlySimpleRealRoots p) :
    ∀ r₁ r₂ : ℝ, (toPolynomial p).aeval r₁ = 0 →
                 (toPolynomial p).aeval r₂ = 0 → r₁ ≠ r₂ →
        (2 : ℝ)^(-(Hex.realRootSeparation p : ℝ)) ≤ |r₁ - r₂|
```

Mahler/Mignotte bound applied to real roots. Mathlib has the Mahler
infrastructure (`mahlerMeasure_le_sqrt_sum_sq_norm_coeff`,
`norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`);
the real-root specialisation combines Mahler with the
discriminant/resultant lower bound.

### `isolate?` correctness and termination

Two theorems. `isolate?` is the executable, `Option`-returning
driver from `hex-real-roots`; the bridge proves both that it
returns `some` at sufficient precision and that the `some` payload
is the correct isolation set.

```lean
/-- At `targetPrecision ≥ realRootSeparation p`, `isolate?` always
    succeeds. Bisection cannot stall at signVariations ≥ 2 once the
    interval width drops below the real-root separation bound. -/
theorem isolate?_succeeds_at_separation_precision
    (p : ZPoly) (hp : Hex.HasOnlySimpleRealRoots p) :
    Hex.isolate? p hp (Hex.realRootSeparation p) ≠ none

/-- Every real root of p is isolated by exactly one returned
    interval, every returned interval contains a real root, and the
    intervals are pairwise disjoint. -/
theorem isolate?_correct
    (p : ZPoly) (hp : Hex.HasOnlySimpleRealRoots p)
    (targetPrecision : Nat) (isolations : Array (RealRootIsolation p))
    (hsome : Hex.isolate? p hp targetPrecision = some isolations) :
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

The first follows from `realRootSeparation_bounds_min_gap`: at
precision `realRootSeparation p`, every interval is narrower than
the minimum gap between distinct real roots, so each interval can
contain at most one root, so `signVariations ≤ 1` for each, so the
worklist drains. The second follows from
`mobiusTransform_root_correspondence` +
`signVariations_eq_one_implies_one_positive_real_root` (and the
zero-variations corollary) + the bisection driver's invariants.

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

**Cite directly (no work expected):**
- `Polynomial.IsRoot`, `Polynomial.roots` over `ℝ` and `ℤ`.
- `Polynomial.derivative`, `Polynomial.gcd`, `Polynomial.comp`.
- `Polynomial.cauchyBound` + bound-on-roots theorem.
- `Polynomial.signVariations` + `roots_countP_pos_le_signVariations`
  (Descartes' rule).
- Mahler measure infrastructure (Landau + Mignotte coefficient bound).

**Build (verify status at activation time):**
- The Möbius-transform-correspondence theorem
  (`mobiusTransform_root_correspondence`). Uses `Polynomial.comp`
  and standard substitution machinery.
- `signVariations` cast-invariance: `(q.map (Int.castRingHom ℝ)).signVariations = q.signVariations`.
  Local lemma if Mathlib lacks a generic
  sign-preserving-ring-hom version.
- The exact-1-from-signVariations parity corollary, stated over the
  real-cast polynomial.
- `lmqBound_bounds_positive_real_roots`. New theorem (Mathlib has
  Cauchy but not LMQ).
- `realRootSeparation_bounds_min_gap`. Wraps Mahler measure
  infrastructure with the discriminant/resultant lower bound.
- `isolate?_correct` and `isolate?_succeeds_at_separation_precision`.
  The main bridge theorems, assembled from the above components
  plus the bisection driver's invariants.

**Deliberately not built:**
- Sturm's theorem and the Sturm sequence. Mathlib has neither.
  Avoided by the algorithm choice (Uspensky uses Descartes, which
  Mathlib does have).
- Vincent's theorem (would be needed for VCA/VAS algorithm
  variants, which are out of scope).

## Layered file organisation

```
HexRealRootsMathlib/
  Basic.lean        — toReal, Quotient bridge
  Mobius.lean       — mobiusTransform_root_correspondence
  Descartes.lean    — exact-1 parity corollary; sign-variation count
                      ↔ root count theorems
  Bounds.lean       — cauchyBound + lmqBound correctness
  Separation.lean   — realRootSeparation_bounds_min_gap
  Isolate.lean      — isolate?_correct + isolate?_succeeds_at_separation_precision
  Conformance.lean  — fixture-based checks
```

## References

- Descartes, Uspensky, Akritas–Strzeboński 2008 (LMQ) — see
  [hex-real-roots](hex-real-roots.md) §"References".
- For the Mahler/Mignotte bounds restricted to real roots: same
  sources as [hex-roots-mathlib](hex-roots-mathlib.md)'s `mahlerPrec`
  proof, applied to the real subset.
