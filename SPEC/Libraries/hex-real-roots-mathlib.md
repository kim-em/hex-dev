# hex-real-roots-mathlib (depends on hex-real-roots + hex-poly-z-mathlib + Mathlib)

Mathlib companion for [hex-real-roots](hex-real-roots.md). Proves
**soundness** of the certified isolations (a `RealRootIsolation`
witness implies a unique real root in its half-open interval, and a
`RealRootIsolations` value captures every real root exactly once) and
**completeness** of the driver (`isolate? p ≠ none` for squarefree
`p`, through the Sturm engine). One theorem is deferred: that the
Descartes engine alone never falls back. It is stated here, its
prerequisite is named, and nothing else depends on it.

**Scope.** The theorem everything rests on is **Sturm's theorem**,
which Mathlib does not have (it is on the 1000+-theorems target
list). The formalisation is well-trodden elsewhere: Isabelle has
Eberl's Sturm entry and Li's Sturm-Tarski entry in the AFP, and
Coq/MathComp has the Cohen-Mahboubi real-closed-field development.
The proof is elementary real analysis over `ℝ[X]`: local sign
behaviour of the chain at finitely many points, with no complex
analysis anywhere in the load-bearing path. The development is
organised as a self-contained slice over `Polynomial ℝ` with no
`HexRealRoots` dependence, so it can be contributed to Mathlib once
exercised here.

Mathlib's Descartes material
(`Mathlib.Algebra.Polynomial.RuleOfSigns`) is deliberately **not**
cited: the Descartes engine is an uncertified search wrapped in Sturm
certificates, so no Descartes soundness statement is an obligation of
this library.

## What we cite from Mathlib (no work)

All names checked against the current Mathlib revision:

- `Polynomial.roots`, `Polynomial.IsRoot`, `Polynomial.aeval`,
  `Polynomial.derivative`, `Polynomial.Squarefree`,
  `Polynomial.eval₂` for `ℤ → ℝ` evaluation.
- `Polynomial.cauchyBound` and
  `Polynomial.IsRoot.norm_lt_cauchyBound`
  (`Mathlib.Analysis.Polynomial.CauchyBound`), for `rootBound`.
- `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau) and
  `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`
  (Mignotte) from `Mathlib.Analysis.Polynomial.MahlerMeasure`, for
  the separation development.
- The intermediate value theorem (`intermediate_value_Icc` and
  variants) and continuity of polynomial evaluation
  (`Polynomial.continuous_aeval`).
- `Polynomial ℚ` gcd theory (`EuclideanDomain.gcd`) through
  hex-poly-z-mathlib's existing correspondence for `toRatPoly`,
  `SquareFreeRat`, and `squareFreeCore`.

## Sturm development (self-contained, upstreamable)

Stated for `Polynomial ℝ`, with no reference to Hex types.

```lean
/-- A generalised Sturm chain for `p`: the sign axioms that the
    counting argument actually uses, as explicit fields.

    - the chain is nonempty and its head is `p`;
    - at every real root `r` of `p`, the second element is nonzero,
      and `p * chain[1]` is negative on a punctured left
      neighbourhood of `r` and positive on a punctured right
      neighbourhood;
    - consecutive elements have no common real zero;
    - whenever an interior element vanishes at a point, its two
      neighbours are nonzero there and have opposite signs;
    - the last element is nonzero and has no real zero. -/
structure IsSturmChain (p : Polynomial ℝ) (chain : List (Polynomial ℝ)) : Prop

/-- Zero-skipping sign variations of the chain at a point. -/
def sturmVar (chain : List (Polynomial ℝ)) (x : ℝ) : ℕ
```

### Theorem chain

1. `sturmVar` is locally constant on any interval containing no zero
   of any chain element (continuity plus sign persistence).
2. Crossing a zero of an interior chain element does not change
   `sturmVar`: the flanking elements have opposite signs there, so
   the local sign pattern `(±, 0, ∓)` contributes one variation
   before, at, and after the crossing.
3. Crossing a simple zero `r` of `p` decreases `sturmVar` by exactly
   one, and with the zero-skipping convention the decrease registers
   exactly at `r`: the variation between the first two elements is
   present for `x < r`, already absent at `x = r`.
4. **Sturm's theorem, half-open form.** For `p ≠ 0` squarefree and a
   generalised Sturm chain of `p`:
   `sturmVar chain a − sturmVar chain b` equals the number of roots
   of `p` in `(a, b]`, for any `a < b`.
5. **Line form.** With variations at `±∞` defined through leading
   coefficients and degree parities: the total number of real roots
   of `p` equals `sturmVar₋∞ − sturmVar₊∞`.

Steps 1-3 are the standard local lemmas; the theorem is a telescoping
sum over the finitely many zeros of the chain elements in `(a, b]`.
The half-open convention in step 3 is the one design-sensitive point,
and it is what makes the executable `sturmCount` match hex-real-roots'
half-open intervals with no endpoint hypotheses.

## Chain correspondence

Connects the executable chain to the abstract development.

```lean
/-- Each element of `Hex.sturmChain p` is a positive rational
    multiple of the corresponding element of the signed remainder
    sequence of `(p, p')` over `ℝ`, and the mapped chain satisfies
    `IsSturmChain`. Induction on the `spem` identity
    `spem f g = c · (f mod g)` with `c > 0`. -/
theorem sturmChain_isSturmChain (p : ZPoly) (hp : SquareFreeRat p) :
    IsSturmChain (toPolyℝ p) ((Hex.sturmChain p).toList.map toPolyℝ)

/-- Positive scaling of chain elements does not change sign
    variations, so the executable counts compute the abstract ones. -/
theorem sturmVarAt_eq (p : ZPoly) (x : Dyadic) : …

/-- `SquareFreeRat p ↔ Squarefree (toPolyℚ p)` (hex-poly-z-mathlib's
    executable gcd correspondence), and squarefreeness transfers to
    `ℝ`. -/
theorem squareFreeRat_iff : …
```

`toPolyℝ` abbreviates the `hex-poly-z-mathlib` cast composed with
`Polynomial.map (Int.castRingHom ℝ)`.

### Consequences for the executable counts

```lean
theorem sturmCount_eq_card_roots (p : ZPoly) (hp : SquareFreeRat p)
    (I : DyadicInterval) :
    Hex.sturmCount p I =
      ((toPolyℝ p).roots.filter (fun r => I.lower < r ∧ r ≤ I.upper)).card

theorem rootCount_eq_card_roots (p : ZPoly) (hp : SquareFreeRat p) :
    Hex.rootCount p = (toPolyℝ p).roots.card
```

## Isolation semantics

Everything below consumes only the decidable fields of the output
structures plus the `SquareFreeRat p` hypothesis, so it holds for any
`RealRootIsolations p` value, no matter which engine produced it.

```lean
/-- The witness means what it says: exactly one real root in the
    half-open interval. -/
theorem RealRootIsolation.exists_unique_root
    (hp : SquareFreeRat p) (iso : RealRootIsolation p) :
    ∃! r : ℝ, (toPolyℝ p).IsRoot r ∧
      (iso.interval.lower : ℝ) < r ∧ r ≤ (iso.interval.upper : ℝ)

/-- A complete run captures every real root exactly once. -/
theorem RealRootIsolations.isolates
    (hp : SquareFreeRat p) (out : RealRootIsolations p) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! iso ∈ out.isolations.toList,
        (iso.interval.lower : ℝ) < r ∧ r ≤ (iso.interval.upper : ℝ)
```

The second follows from the first plus `ordered` (disjointness) and
`complete` (counting): the isolations hold `rootCount p` distinct
roots among them, and that is all the roots there are.

## Bounds and depths

```lean
theorem rootBound_bounds_roots (p : ZPoly) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r → |r| < (Hex.rootBound p : ℝ)
  -- via Polynomial.IsRoot.norm_lt_cauchyBound and the power-of-two
  -- rounding.

theorem sepPrec_separates (p : ZPoly) (hp : SquareFreeRat p) :
    ∀ z₁ z₂ : ℂ, (toPolyℂ p).IsRoot z₁ → (toPolyℂ p).IsRoot z₂ →
      z₁ ≠ z₂ → (2 : ℝ)^(−(Hex.sepPrec p : ℤ)) < ‖z₁ − z₂‖ / 4
  -- Pairwise, hence vacuous for degree ≤ 1, where no consumer needs
  -- it. Mahler's bound with |disc p| ≥ 1 and Landau's inequality.
  -- toPolyℂ is the ℂ-cast analogue of toPolyℝ.
```

The separation development is the same closed form as
hex-roots-mathlib's (§"Discriminant / separation development" there),
and like the Sturm slice it has no dependence on the executable
library. When both root libraries are active the proof should be
hosted once, in hex-poly-z-mathlib (a dependency of both companions),
and cited from each. Neither companion should carry a private copy.

## Driver completeness

```lean
/-- The Sturm engine succeeds on squarefree input: at
    `isolationDepth p` every interval is narrower than `sep(p)/4`,
    hence narrower than any gap between real roots, hence has Sturm
    count 0 or 1, so the worklist drains and the totals match. -/
theorem isolateSturm?_isSome (p : ZPoly) (hp : SquareFreeRat p) :
    (Hex.isolateSturm? p).isSome

theorem isolate?_isSome (p : ZPoly) (hp : SquareFreeRat p) :
    (Hex.isolate? p).isSome
```

Note this argument needs only the real-pair instances of
`sepPrec_separates` (distinct real roots are at least
`4 · 2^{−sepPrec p}` apart). Exact
counts are what make the real-gap quantity sufficient. The Descartes
engine's variation counts are also disturbed by nearby non-real
roots, which is why its termination statement (deferred, below) needs
the two-circle theorem rather than this argument.

## Refinement and root identity

```lean
theorem refine1_isolates_same (hp : SquareFreeRat p)
    (iso : RealRootIsolation p) :
    -- the unique roots of `iso` and `iso.refine1` coincide, and the
    -- width strictly halves (the fallback branch is unreachable).
    …

/-- `Overlaps` on `RefinedRealIsolation` is an equivalence relation
    whose classes are exactly the real roots. -/
theorem overlaps_iff_same_root (hp : SquareFreeRat p)
    (i₁ i₂ : RefinedRealIsolation p) :
    Hex.Overlaps i₁ i₂ ↔ theRoot i₁ = theRoot i₂

def SimpleRealRoot.toReal (hp : SquareFreeRat p) :
    SimpleRealRoot p → ℝ
  -- lifts `theRoot` through the quotient; well-defined by
  -- `overlaps_iff_same_root`.

theorem SimpleRealRoot.toReal_isRoot … : (toPolyℝ p).IsRoot (s.toReal hp)
theorem SimpleRealRoot.toReal_injective … : Function.Injective (toReal hp)
theorem sameRoot_iff (hp) (i₁ i₂) :
    RefinedRealIsolation.sameRoot i₁ i₂ = true ↔
      SimpleRealRoot.mk i₁ = SimpleRealRoot.mk i₂
```

`theRoot` is the unique root delivered by
`RealRootIsolation.exists_unique_root`.

## Deferred: Descartes engine termination

```lean
theorem isolateDescartes?_isSome (p : ZPoly) (hp0 : p ≠ 0)
    (hp : SquareFreeRat p) : (Hex.isolateDescartes? p).isSome
```

Prerequisite: the **Obreshkoff two-circle theorem**. For an interval
`(a, b)`, the variation count of the Möbius-transformed polynomial is
at least the number of roots in the one-circle region (the open disc
with diameter `(a, b)`) and at most the number of roots in the
two-circle region (the union of the two discs through `a` and `b`
whose centres lie at `(a+b)/2 ± i·(b−a)/(2√3)`), counted with
multiplicity. Consequences: a short interval far from all roots has
count 0, and a short interval whose two-circle region contains one
simple real root has count 1, so at `isolationDepth p` the Descartes
worklist drains and every candidate certifies.

Status and boundaries:

- The two-circle theorem has no formalisation in any proof assistant
  that we know of. The classical proof (Obreschkoff 1963; modern
  treatment in Krandick-Mehlhorn 2006 and Eigenwillig 2008) is an
  induction on multiplying in linear and conjugate-quadratic factors,
  with sector inequalities on coefficient sequences. Elementary but
  long, and the effort is genuinely uncertain.
- **Nothing else waits for it.** `isolate?_isSome`, all soundness
  theorems, and hex-rcf's decision procedure are complete without it.
  Its value is to retire the Sturm fallback path from the trusted
  runtime story and to delete the conformance assertions described in
  [hex-real-roots.md](hex-real-roots.md) §"Conformance fixtures"
  (the PR that proves this theorem must delete those assertions).
- Like the Sturm slice, it should be developed against
  `Polynomial ℝ` (and `ℂ` for the regions) with no `HexRealRoots`
  dependence, as a Mathlib contribution in its own right.

## File organisation

```
HexRealRootsMathlib/
  SturmChainDefs.lean  -- IsSturmChain, sturmVar over Polynomial ℝ
  SturmTheorem.lean    -- the counting theorem and the line form
  ChainCorrespond.lean -- sturmChain_isSturmChain, sturmVarAt_eq,
                          squareFreeRat_iff, sturmCount_eq_card_roots
  Separation.lean      -- sepPrec_separates (until hosted in
                          hex-poly-z-mathlib), rootBound_bounds_roots
  Isolations.lean      -- exists_unique_root, isolates
  Drivers.lean         -- isolateSturm?_isSome, isolate?_isSome,
                          refine1_isolates_same
  SimpleRealRoot.lean  -- overlaps_iff_same_root, toReal, sameRoot_iff
  TwoCircle.lean       -- the deferred development
```

`conformance/HexRealRootsMathlib/Conformance.lean`: `#guard`-style
checks that the executable counts match Mathlib root counts on the
committed fixtures.

## References

- Sturm 1829/1835, Collins-Akritas 1976, Obreschkoff 1963,
  Krandick-Mehlhorn 2006, Eigenwillig 2008, Mahler 1964, Mignotte
  1982: see [hex-real-roots.md](hex-real-roots.md) §"References".
- Basu, Pollack, Roy. *Algorithms in Real Algebraic Geometry.*
  Springer, 2nd ed., 2006. Chapter 2: the generalised-chain form of
  Sturm's theorem used here.
- Eberl. *Sturm's Theorem.* Archive of Formal Proofs, 2014. The
  Isabelle formalisation, a useful map of the lemma structure.
- Li. *The Sturm-Tarski Theorem.* Archive of Formal Proofs, 2014.
  The Tarski-query generalisation, relevant if hex-rcf ever moves
  its sign determination to Tarski queries.
- Cohen, Mahboubi. *Formal proofs in real algebraic geometry: from
  ordered fields to quantifier elimination.* Logical Methods in
  Computer Science 8(1), 2012. The Coq/MathComp development.
