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

/-- A terminal-constant Sturm chain forces `SquareFreeRat` — the reverse
    of the terminal-unit step in `sturmChain_isSturmChain`, walked back to
    coprime seeds. Lets a concrete `SquareFreeRat p` be discharged by
    `by decide` on the chain. -/
theorem squareFreeRat_of_hasSquarefreeSturmChain
    (p : ZPoly) (h : hasSquarefreeSturmChain p = true) : SquareFreeRat p
```

`toPolyℝ` abbreviates the `hex-poly-z-mathlib` cast composed with
`Polynomial.map (Int.castRingHom ℝ)`. Its coefficient/coefficient-sum
bridges (`coeff_toPolyℝ` / `coeff_toPolyℚ`, `eval_toPolyℝ` /
`eval_toPolyℚ`) rewrite a root goal on a literal `ofCoeffs` to an explicit
polynomial equation, and `toReal_ofInt_shiftRight` normalizes `n / 2ⁱ`
dyadic endpoints.

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
structures plus `SquareFreeRat p` (and, for `isolates`, `p ≠ 0`, since
`SquareFreeRat 0` is vacuous), so it holds for any `RealRootIsolations p`
value, no matter which engine produced it.

```lean
/-- The witness means what it says: exactly one real root in the
    half-open interval. -/
theorem RealRootIsolation.exists_unique_root
    (hp : SquareFreeRat p) (iso : RealRootIsolation p) :
    ∃! r : ℝ, (toPolyℝ p).IsRoot r ∧
      (iso.interval.lower : ℝ) < r ∧ r ≤ (iso.interval.upper : ℝ)

/-- A complete run captures every real root exactly once. -/
theorem RealRootIsolations.isolates
    (hp0 : p ≠ 0) (hp : SquareFreeRat p) (out : RealRootIsolations p) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! iso ∈ out.isolations.toList,
        (iso.interval.lower : ℝ) < r ∧ r ≤ (iso.interval.upper : ℝ)
```

The second follows from the first plus `ordered` (disjointness) and
`complete` (counting): the isolations hold `rootCount p` distinct
roots among them, and that is all the roots there are. Both are also
exported in the `Hex` namespace, so dot notation resolves on the
executable structures (`iso.exists_unique_root`).

## The `isolate_roots` term elaborator

A user-facing front-end that automates the pattern of the worked
`x⁴ − 2` example: run the executable isolator at elaboration time and
package the certified result as one term the caller can `obtain`,
`have`, or pass to `grind`.

```lean
-- natural intervals (whatever the isolator's separation produced)
isolate_roots p
-- every interval refined to width at most x
isolate_roots (width := x) p
```

`p` is either a closed `Hex.ZPoly` term or a closed `Polynomial ℤ/ℚ/ℝ`
expression over `X`, `C`, numerals, `+`, `-`, `*`, `^` whose
coefficients are integers (non-integer coefficients are rejected with
a clear message). The width `x` is any closed positive rational
literal expression (`1/1000`, `2^(-20)`, `10^(-2)`); it converts to
the bit target `k = ⌈log₂ x⁻¹⌉` in exact integer arithmetic and is an
operational promise about the emitted intervals, not a field of the
result. The syntax uses an `atomic` lookahead on `"(" "width" ":="`
so a parenthesised polynomial argument parses as the polynomial.

The result type, uniform over the input rings through `aeval`:

```lean
structure Hex.IsolatedRealRoots {R : Type*} [CommRing R] [Algebra R ℝ]
    (P : Polynomial R) (n : ℕ) where
  intervals   : Vector (ℚ × ℚ) n
  unique_root : ∀ i : Fin n, ∃! x : ℝ,
      Polynomial.aeval x P = 0 ∧ (intervals[i].1 : ℝ) < x ∧ x ≤ intervals[i].2
  covers      : ∀ x : ℝ, Polynomial.aeval x P = 0 →
      ∃ i : Fin n, (intervals[i].1 : ℝ) < x ∧ x ≤ intervals[i].2
```

Intervals are half-open `(lo, hi]` with exact rational endpoints (the
isolator's dyadics). A `ZPoly` input is stated over `toPolynomial p :
Polynomial ℤ`. The elaborator is fat-API/thin-meta: all proof content
lives in library constructors, and the emitted term only instantiates
them with literals and `decide`-style certificates.

- `IsolatedRealRoots.of` : from `p ≠ 0` (stated as a size check, see
  below), `SquareFreeRat p`, and a `RealRootIsolations p` value, via
  `exists_unique_root` + `isolates` and the cast lemmas.
- `IsolatedRealRoots.congrRoots` : transport along
  `∀ x : ℝ, aeval x P = 0 ↔ aeval x Q = 0`, heterogeneous in the
  coefficient rings (`P : Polynomial R`, `Q : Polynomial S`) since it
  is used twice with different rings: once for the squarefree-core
  step and once to restate over the user's polynomial (the latter
  hypothesis closed by a bridge tactic over
  `aeval`-of-`toPolynomial` unfolding, coefficient lookups, and
  `norm_num` — a pointwise evaluation bridge, not a `Polynomial`
  identity).
- `IsolatedRealRoots.constant` : the `n = 0` result for nonzero
  constants, which never enter the isolator (the squarefree Sturm
  certificate is `false` on constants by design).
- The **replay constructor**: the production certificate shape (see
  below).

**Squarefreeness is invisible to the user.** If
`hasSquarefreeSturmChain p` fails, the elaborator runs on
`squareFreeCore p` and transports along

```lean
theorem aevalIff_squareFreeCore (hp0 : p ≠ 0) (x : ℝ) :
    Polynomial.aeval x (toPolynomial (ZPoly.squareFreeCore p)) = 0 ↔
    Polynomial.aeval x (toPolynomial p) = 0
```

(the roots of a nonzero polynomial and of its squarefree core agree
as sets; proven through the `primitiveSquareFreeDecomposition`
bridge and a root-multiplicity argument, and shared with the `rcf`
tactic's step 3).

**Kernel replay.** Following the `irreducible_cert` pattern (and
hex-rcf §Kernel replay), the elaborator never asks the kernel to
re-run the search. Measured on the Stage-1 prototype, the naive
per-field `decide` shape (each `count_one`/`complete` certificate
rebuilding the Sturm chain) grows superlinearly — heartbeats
33k/103k/326k at Wilkinson degrees 6/8/10 — while the replay shape
(reify the Sturm chain once as an `Array ZPoly` literal, then check
per-endpoint sign variations against it) amortises to 29k/66k/138k,
2.4× cheaper at degree 10 and scaling. The elaborator therefore
emits the replay shape. Two constraints shape its soundness lemma:

- chain validity is verified by a structural `IsSturmChain`
  predicate over coefficient-level checks, NOT by deciding
  `chain = sturmChain p` (a nonempty `Array ZPoly` equality, which
  does not kernel-reduce under the module system: the core
  `Array.instDecidableEqImpl` issue);
- nonzeroness is stated as a size check (`p.size ≠ 0` via a Bool
  test plus `of_size_ne_zero`), avoiding structural `DensePoly`
  equality for the same reason.

The executable closure the kernel replays (`sturmChain`, `spem*`,
`signVar`, `sturmVarAt/±Inf`, `sturmCount`, `rootCount`,
`evalDyadic`, `dyadicSign`) is `@[expose]`d in hex-real-roots for
this purpose, with the `spem` helpers de-privatized (an exposed
public definition may not reference a `private` one); see the
hex-real-roots SPEC. `Dyadic.toReal`'s unfolding is provided by a
cast lemma rather than cross-module defeq.

**Errors** are user-grade and distinguish: the zero polynomial
("every real number is a root"), non-integer coefficients,
unsupported polynomial syntax, non-closed input (free variables or
metavariables, in the polynomial or the width), non-positive or
non-closed width, backend failure, and internal certificate mismatch
(a bug, reported as such).

**Practical limits** (Stage-1 measurements, single-threaded
elaboration): degree ≤ 10 with widths to `2^(-20)` costs seconds;
per-field certificates remain acceptable only below degree ~6. The
elaborator caps refinement with a diagnostic for pathological widths.

A Mathlib-free variant (same meta core, emitting a
`RealRootIsolations` value whose conclusions are the executable
Sturm certificates) is a possible follow-up for consumers who cannot
import Mathlib; the ℝ-valued statements above necessarily live here.

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

## Descartes engine termination (the two-circle theorem)

```lean
theorem isolateDescartes?_isSome (p : ZPoly) (hp0 : p ≠ 0)
    (hp : SquareFreeRat p) : (Hex.isolateDescartes? p).isSome
```

Proven in `TwoCircle.lean`; with it the companion is fully
`sorry`-free. The Descartes engine alone returns `some` on every
nonzero square-free input, so the runtime never falls back to the
Sturm engine.

Prerequisite: the **Obreshkoff two-circle theorem**, in its correct
*λ-graded* form (Obreschkoff 1963; Krandick-Mehlhorn 2006,
Eigenwillig 2008): if all but `λ` complex roots of a real polynomial
lie in the closed sector of half-angle `π/(λ+2)` about the negative real
axis (equivalently, at most `λ` roots lie outside), then the
coefficient sequence has at most `λ` sign variations. The naive count
bound "variation count ≤ number of roots in the two-circle region" is
**false** — `(X²+X+1)·(X²−(3/2)X+1)` has four sign variations while
only two of its roots lie outside the sector (the counterexample is
recorded in `TwoCircleSector.lean`). We use only the two lowest graded
cases, `λ ∈ {0, 1}`: `Polynomial.signVariations_le_one_of_sector`
(`TwoCircleSector.lean`, the `λ = 1` bound via Hoggar log-concavity)
and its `λ = 0` corollary.

Route (`TwoCircle.lean`): at each node the Descartes count `V` equals
`signVariations` of the Möbius transform; the Descartes parity exports
(`DescartesParity.lean`) pin the open-interval root count exactly when
`V ∈ {0, 1}`, and the exact endpoint test settles `p(b) = 0`, so the
half-open Sturm count is computed exactly and every candidate certifies
(count `1`) and every discard emits `#[]` (count `0`). At the depth
budget the bisecting rows are refuted: `V = 1 ∧ p(b) = 0` forces a
Sturm count of `2` against `sturmCount_le_one`, and `V ≥ 2` triggers
the sector bound (`≥ 2` transform-roots outside the sector correspond
via `roots_mobiusPoly`/`not_inTwoCircle_iff_mem_sector` to two distinct
`p`-roots in the two-circle region, closer than the Mahler separation
`sepPrec_separates'` allows). The worklist therefore drains at
`isolationDepth p`.

Status and boundaries:

- The two-circle theorem is now formalised here (the sector core
  `signVariations_le_one_of_sector`, the region geometry
  `TwoCircleRegion.lean`, and the Descartes parity). The classical
  proof (Obreschkoff 1963; Krandick-Mehlhorn 2006, Eigenwillig 2008)
  runs by induction on multiplying in linear and conjugate-quadratic
  factors, with sector inequalities on coefficient sequences.
- **Nothing else waited for it.** `isolate?_isSome`, all soundness
  theorems, and hex-rcf's decision procedure were complete without it;
  its value is to retire the Sturm fallback path from the trusted
  runtime story. The executable conformance stand-ins for this
  theorem (`isolateDescartes?` succeeds and agrees with `isolate?` per
  fixture) are retired in the same change now that the theorem carries
  the claim.
- Like the Sturm slice, the sector/region/parity development is stated
  against `Polynomial ℝ`/`ℂ` with no `HexRealRoots` dependence, ready
  as a Mathlib contribution in its own right.

## File organisation

```
HexRealRootsMathlib/
  SturmChainDefs.lean  -- IsSturmChain, sturmVar over Polynomial ℝ
  SturmTheorem.lean    -- the counting theorem and the line form
  ChainCorrespond.lean -- sturmChain_isSturmChain, sturmVarAt_eq,
                          sturmCount_eq_card_roots; compatibility aliases for
                          HexPolyZMathlib.Squarefree
  Discr.lean            -- compatibility import of the shared discriminant API
  Hadamard.lean         -- compatibility import of the shared determinant bound
  Separation.lean      -- sepPrec_separates, rootBound_bounds_roots;
                          specializes shared Mahler/Vandermonde analysis
  Isolations.lean      -- exists_unique_root, isolates
  IsolateRoots.lean    -- IsolatedRealRoots, its constructors, the
                          bridge tactic, and the isolate_roots
                          term elaborator
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
