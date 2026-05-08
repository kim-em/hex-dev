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

/-- Möbius transform sends positive reals to (a, b) bijectively
    (preserving multiplicity for polynomial roots). -/
theorem mobiusTransform_root_correspondence
    (p : ZPoly) (a b : Dyadic) (hab : a < b) :
    ∀ r : ℝ,
      (toPolynomial (mobiusTransform p a b)).aeval r = 0 ∧ 0 < r
        ↔ ∃ s : ℝ, (a : ℝ) < s ∧ s < (b : ℝ) ∧
                   (toPolynomial p).aeval s = 0
                   -- with multiplicity preserved
```

### Descartes count → exact-1 corollary

Mathlib's `roots_countP_pos_le_signVariations` gives `≤`; we need
the parity argument to derive `signVariations = 1 ⟹ count = 1`.

```lean
theorem signVariations_eq_one_implies_one_positive_root
    (q : Polynomial ℤ) (hsv : q.signVariations = 1) :
    q.roots.countP (0 < ·) = 1
  -- Proof: count ≤ 1 (Mathlib), count ≡ 1 (mod 2) (parity, also
  -- in `roots_countP_pos_le_signVariations`'s context), so count = 1.

theorem signVariations_eq_zero_implies_no_positive_roots
    (q : Polynomial ℤ) (hsv : q.signVariations = 0) :
    q.roots.countP (0 < ·) = 0
  -- Mathlib: count ≤ 0.
```

The parity lemma `count ≡ signVariations (mod 2)` is the standard
strengthening of Descartes' rule; if Mathlib's
`RuleOfSigns.lean` has it, cite directly; otherwise this is a small
local lemma (~30 lines) building on
`roots_countP_pos_le_signVariations` and standard parity arguments
on sign sequences.

### LMQ bound correctness

```lean
theorem lmqBound_bounds_positive_real_roots (p : ZPoly) :
    ∀ r : ℝ, (toPolynomial p).aeval r = 0 → 0 < r →
        r ≤ (Hex.lmqBound p : ℝ)
  -- Akritas–Strzeboński 2008 LMQ bound, stated for positive reals.
  -- The proof follows the original paper; a couple of pages of
  -- elementary algebra.
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
the real-root specialisation needs a small wrapper combining Mahler
with the discriminant/resultant lower bound. Days-to-week wrapper.

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
roots of `p`. Follows from `mobiusTransform_root_correspondence` +
`signVariations_eq_one_implies_one_positive_root` (and the
zero-variations corollary) + the bisection driver's invariants +
`realRootSeparation_bounds_min_gap` for termination.

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
  (`mobiusTransform_root_correspondence`). Likely a few pages of
  proof; uses `Polynomial.comp` and standard substitution machinery.
- The exact-1-from-signVariations parity corollary if not already
  in Mathlib. Small wrapper.
- `lmqBound_bounds_positive_real_roots`. New theorem (Mahlib has
  Cauchy but not LMQ). Few pages.
- `realRootSeparation_bounds_min_gap`. Small wrapper on Mahler
  measure infrastructure.
- `isolate_correct`. The main bridge theorem, assembled from the
  above components plus the bisection driver's invariants.

**Deliberately not built:**
- Sturm's theorem and the Sturm sequence. Mathlib has neither;
  formalising would be a multi-month side quest. Avoided by the
  algorithm choice (Uspensky uses Descartes, which Mathlib does
  have).
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
  Isolate.lean      — isolate_correct
  Conformance.lean  — fixture-based checks
```

## References

- Descartes, Uspensky, Akritas–Strzeboński 2008 (LMQ) — see
  [hex-real-roots](hex-real-roots.md) §"References".
- For the Mahler/Mignotte bounds restricted to real roots: same
  sources as [hex-roots-mathlib](hex-roots-mathlib.md)'s `mahlerPrec`
  proof, applied to the real subset.
