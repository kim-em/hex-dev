# hex-real-roots-mathlib

Dependencies: hex-real-roots, hex-poly-mathlib, hex-poly-z-mathlib and
Mathlib; the shared abstract Sturm–Tarski foundation adds a planned Tau Ceti
import. When implemented, the release configuration must carry that pinned
third-party dependency to the published companion and its downstream consumers.
This SPEC does not change publication metadata.

Mathlib companion for [hex-real-roots](https://github.com/leanprover/hex-real-roots). Proves
**soundness** of the certified isolations (a `RealRootIsolation`
witness implies a unique real root in its half-open interval, and a
`RealRootIsolations` value captures every real root exactly once) and
**completeness** of the driver (`ZPoly.isolateRealRoots? p ≠ none` for squarefree
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

Stated for `Polynomial ℝ`, with no reference to Hex types. The pointwise and infinity
counts use Mathlib’s `List.signVariations`, including its zero-skipping and sign-congruence
API. The bridge proves that the Mathlib-free `Hex.signVar` agrees with this count.

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
and it is what makes the executable `ZPoly.sturmCount` match hex-real-roots'
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
dyadic endpoints. `evalSign_zero_iff` packages exact dyadic Horner evaluation
as the reusable equivalence between zero sign and a real root at the endpoint.

### Literal-chain replay API

Consumers such as [hex-rcf](../../HexRCF/SPEC/hex-rcf.md) certify a supplied chain by
multiplication identities without identifying it with the executable
`sturmChain`. The companion therefore exposes a second bridge from
literal integer-polynomial chains to the same abstract theorem.

The reusable proof is an induction over an abstract list of at least two entries
`[f, s₁, ..., sₙ]` with these hypotheses:

- every entry is nonzero and `sₙ` is a nonzero constant;
- `derivative f = scale δ s₁` for a positive integer `δ`;
- every consecutive triple satisfies
  `scale α sᵢ = q * sᵢ₊₁ - scale β sᵢ₊₂` for positive integers
  `α`, `β` and a supplied `q`.

It concludes that the cast list is an `IsSturmChain (toPolyℝ f)` and
that `toPolyℝ f` is squarefree. Degree descent is useful for bounding and
validating a compiled replay certificate, but is not an axiom of
`IsSturmChain` and is therefore not a hypothesis of this proof. The induction
is independent of `chainList` and serves RCF's Boolean literal-chain checker;
the older executable correspondence remains a separate proof for the chain it
constructs. Both use the public supporting lemmas for reverse coprimality,
derivative flanks, and exclusion of a common zero.

The finite-point bridge `sturmVarAt_eq` and the infinity bridges
`sturmVarNegInf_eq` / `sturmVarPosInf_eq` are public for an arbitrary
literal `Array ZPoly`. Together with `Sturm.IsSturmChain.sturm_Ioc` and
`Sturm.IsSturmChain.sturm`, they turn literal executable variation reads into
root counts without calling `ZPoly.sturmCount` or `ZPoly.rootCount`. The
`ZReplay.count_eq_card_roots` and `ZReplay.total_eq_card_roots` corollaries
perform the list-to-array alignment and compose replay, squarefreeness, and
counting in the form consumed by a checker.

The same layer supplies generalized isolation semantics parameterized
by those literal counts: count-one gives a unique root in `(lower,
upper]`, while an ordered complete array captures every root exactly
once. These statements consume `Squarefree (toPolyℝ f)` and `f ≠ 0`,
not the executable `SquareFreeRat f` predicate, and do not reuse the
current `RealRootIsolation` fields that are definitionally tied to
`ZPoly.sturmCount`. The existing executable isolation theorem remains separate for
API compatibility: the generic statement intentionally mirrors its finite
cardinality argument rather than coupling the literal layer back to the
executable structures it is meant to abstract over.

### Consequences for the executable counts

```lean
theorem sturmCount_eq_card_roots (p : ZPoly) (hp : 1 ≤ p.natDegree)
    (hsq : SquareFreeRat p) (I : DyadicInterval) :
    Hex.ZPoly.sturmCount p I =
      ((toPolyℝ p).roots.filter (fun r => I.lower < r ∧ r ≤ I.upper)).card

theorem rootCount_eq_card_roots (p : ZPoly) (hp : 1 ≤ p.natDegree)
    (hsq : SquareFreeRat p) :
    Hex.ZPoly.rootCount p = (toPolyℝ p).roots.card
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
`complete` (counting): the isolations hold `ZPoly.rootCount p` distinct
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
the bit target `k = max 0 ⌈log₂ x⁻¹⌉` in exact integer arithmetic
(widths above `1` never coarsen the natural intervals) and is an
operational promise about the emitted intervals, not a field of the
result. The syntax uses an `atomic` lookahead on `"(" "width" ":="`
so a parenthesised polynomial argument parses as the polynomial.

When an expected type `Hex.IsolatedRealRoots (P : Polynomial R) n` is
available at the call site, the coefficient ring `R` is used as the
elaboration hint for the argument, so `isolate_roots (X ^ 4 - 2)` (no
type ascription on the argument) elaborates as a `Polynomial ℝ` under
`… : IsolatedRealRoots (X ^ 4 - 2 : Polynomial ℝ) 2`. The hint is a
fallback: the argument is first elaborated with no expected type (a
`ZPoly` argument, or an already-ascribed polynomial, resolves this way
and is unaffected), and the ring hint is applied only when that leaves
the argument's type ambiguous.

The result type, uniform over the input rings through `aeval`:

```lean
structure Hex.IsolatedRealRoots {R : Type*} [CommRing R] [Algebra R ℝ]
    (P : Polynomial R) (n : ℕ) where
  intervals   : Vector (ℚ × ℚ) n
  unique_root : ∀ i : Fin n, ∃! x : ℝ,
      Polynomial.aeval x P = 0 ∧ (intervals[i].1 : ℝ) < x ∧ x ≤ intervals[i].2
  covers      : ∀ x : ℝ, Polynomial.aeval x P = 0 →
      ∃ i : Fin n, (intervals[i].1 : ℝ) < x ∧ x ≤ intervals[i].2
  ordered     : ∀ i j : Fin n, i < j → intervals[i].2 ≤ intervals[j].1
```

`ordered` makes the enumeration honest: without it, duplicate
intervals could satisfy the other two fields and `n` would not
determine the root count; with it the intervals are pairwise
disjoint and sorted, so `n` is exactly the number of distinct real
roots (a derived lemma, not a field). Intervals are half-open
`(lo, hi]` with exact rational endpoints (the isolator's dyadics). A `ZPoly` input is stated over `toPolynomial p :
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

The elaborator's own transport does not identify the reified core
with `squareFreeCore p` in the kernel — that identification would
need to reduce `squareFreeCore`'s rational-arithmetic helpers, which
are deliberately outside the replay closure. It instead emits a
radical certificate: reified cofactors `a`, `b`, a scalar `t`, and an
exponent `k` with the two literal `ring` identities
`orig = core * a` and `t · core^(k+1) = a * b`, from which
`aevalIff_radical` derives the shared real root set. Squarefreeness
stays invisible either way; `aevalIff_squareFreeCore` remains the
library-level statement (and the `rcf` dependency).

**Kernel replay.** Following the `factor_poly` / `irreducibility` pattern (and
hex-rcf §Kernel replay), the elaborator never asks the kernel to
re-run the search. Measured on the Stage-1 prototype, the naive
per-field `decide` shape (each `count_one`/`complete` certificate
rebuilding the Sturm chain) grows superlinearly — heartbeats
33k/103k/326k at Wilkinson degrees 6/8/10 — while the replay shape
(reify the Sturm chain once as an `Array ZPoly` literal, then check
per-endpoint sign variations against it) amortises to 29k/66k/138k,
2.4× cheaper at degree 10 and scaling. The prototype's replay
numbers are surrogate measurements: its chain-identification lemmas
were assumed, so the cost of the `SturmChainCert` validity check
itself is not yet measured and is re-measured when the production
constructor lands. The elaborator emits the replay shape. Two constraints shape its soundness lemma:

- chain validity is verified by a decidable executable certificate
  predicate `SturmChainCert p chain` over coefficient-level checks
  (distinct from the companion's existing semantic `IsSturmChain`
  over `Polynomial ℝ`, which is stated through `primitivePart p` and
  is not decidable), NOT by deciding `chain = sturmChain p` (a
  nonempty `Array ZPoly` equality, which does not kernel-reduce
  under the module system: the core `Array.instDecidableEqImpl`
  issue). Its soundness bridge to the certified counts goes through
  the executable chain's `primitivePart` head, exactly as the
  existing chain correspondence does. `SturmChainCert p chain` also
  carries a `chain.size ≤ p.size` fuel-bound conjunct — every genuine
  Sturm chain satisfies it, since chain degrees strictly decrease —
  which the soundness proof (`cert_imp_eq`) needs to bound the
  `sturmChainAux` fuel when reconstructing `sturmChain p` from the
  certified tail; the constructor discharges it by the same
  per-certificate `decide`;
- nonzeroness is stated as a size check (`p.size ≠ 0` via a Bool
  test plus `ne_zero_of_size_ne_zero`), avoiding structural
  `DensePoly` equality for the same reason.

The executable closure the kernel replays — thirteen definitions:
`sturmChain`, `sturmChainAux`, `spem`, `spemAux`, `spemStep`,
`signVar`, `sturmVarAt`, `sturmVarNegInf`, `sturmVarPosInf`,
`ZPoly.sturmCount`, `ZPoly.rootCount`, `ZPoly.evalDyadic`, `dyadicSign` — is
`@[expose]`d in hex-real-roots for this purpose, with the three
private helpers (`spemStep`, `spemAux`, `sturmChainAux`)
de-privatized (an exposed public definition may not reference a
`private` one); see the hex-real-roots SPEC. `Dyadic.toReal`'s unfolding is provided by a
cast lemma rather than cross-module defeq.

**Interval literals.** The emitted term re-bases `intervals` on
pretty rational literals (`m`, or `m / 2^k` in lowest terms) via
`IsolatedRealRoots.ofCertPretty`, which wraps the replay constructor
in `withIntervals`: any interval vector whose endpoints agree with
the isolator's **as reals** carries the same three theorems. The
endpoint identities are stated against the literal `iso` argument
itself (`Dyadic.toReal` of each reified dyadic — a shape user
modules check without reducing any of this library's definitions)
and discharged through the `toReal` cast lemmas, so no `Rat`
normalization (and hence no `Nat.gcd`) comes near the kernel. With
`intervals` definitionally a `#v[…]` literal, user-side endpoint
extraction is a definitional step:
`rw [show H.intervals = #v[…] from rfl]`. The wrappers this step
unfolds (`withIntervals`, `ofCertPretty`, `congrRoots`) are
`@[expose]`d so the reduction works from module-system files; it
never reaches `ofCert` itself. Their `intervals` projections also
carry `@[simp]` lemmas (`ofCertPretty_intervals`,
`withIntervals_intervals`, `congrRoots_intervals`), so `simp`,
`simpa`, and `grind` compute an isolation's endpoints to their
literals without naming the constructors: a `unique_root i`
projection closes a concrete-endpoint theorem with a single
`simpa [H]`. The whole `IsolatedRealRoots` API (`of`, `ofCert`,
`withIntervals`, `ofCertPretty`, `congrRoots`, `constant`) lives in
the `Hex.IsolatedRealRoots` namespace alongside the structure, so
dot notation reaches every constructor and lemma.

**Errors** are user-grade and distinguish: the zero polynomial
("every real number is a root"), non-integer coefficients,
unsupported polynomial syntax, non-closed input (free variables or
metavariables, in the polynomial or the width), non-positive or
non-closed width, backend failure, and internal certificate mismatch
(a bug, reported as such).

**Practical limits** (Stage-1 measurements, single-threaded
elaboration): degree ≤ 10 at natural widths, and degree ≤ 6 refined
to `2^(-20)`, cost seconds (deeper refined-width combinations are
unmeasured); per-field certificates remain acceptable only below
degree ~6. The bit target is read off the requested width's bit
lengths, so a very fine width costs what isolating to it costs and
nothing extra.

**Phase-4 proof evidence.** `isolate_roots` is an elaboration/proof surface,
not a LeanBench executable. Build-only modules below
`bench/HexRealRootsMathlib/ProofProbe/` measure natural-width Wilkinson
products at degrees 6, 8, and 10 and width-`2^(-20)` products at degrees 2, 4,
and 6. Each case is adjacent to the same import-only baseline, and degree 6
also has a direct natural-to-refined pair. Baseline and natural-degree-10
same-module controls are first in manifest `config.order`; execution order
rotates by round. The external runner uses six balanced rounds, exact
generated-artifact invalidation, ordinary kernel checking, exact axiom
validation, and complete source provenance.
`HexRealRootsMathlibReplayProbe` supplies the reduced CI coverage;
`HexRealRootsMathlibReplayProbeScientific` owns the larger release arms and
remains outside routine CI.

A canonical shared-host invocation selects a CPU for placement and records it:

```bash
cpu=$(python3 scripts/bench/idle_core.py)
taskset -c "$cpu" python3 scripts/bench/real_roots_mathlib_sweep.py --samples 6 \
  --timeout 180 --warm-timeout 600 \
  --shared-host --cpu "$cpu"
```

The six balanced rounds retain every adjacent pair. Scheduler and SMT activity
remain in the artifact as context and never trigger retries or removal.

The runner follows the shared-host contract in `SPEC/benchmarking.md`: matched
arms remain adjacent with alternating orientation, every completed pair is
retained, and host/core activity is descriptive context. Executable
isolation arithmetic belongs to the existing Mathlib-free `HexRealRoots`
benchmark. The bridge declarations have no separable compiled runtime kernel.
For the proof-emitting elaborator there is
`no-comparable-surface-in-named-comparator`: no external tool emits and
kernel-checks the same Lean proof term.

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
    (Hex.ZPoly.isolateSturm? p).isSome

theorem isolateRealRoots?_isSome (p : ZPoly) (hp : SquareFreeRat p) :
    (Hex.ZPoly.isolateRealRoots? p).isSome
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
    (hp : SquareFreeRat p) : (Hex.ZPoly.isolateDescartes? p).isSome
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
- **Nothing else waited for it.** `isolateRealRoots?_isSome`, all soundness
  theorems, and hex-rcf's decision procedure were complete without it;
  its value is to retire the Sturm fallback path from the trusted
  runtime story. The executable conformance stand-ins for this
  theorem (`ZPoly.isolateDescartes?` succeeds and agrees with `ZPoly.isolateRealRoots?` per
  fixture) are retired in the same change now that the theorem carries
  the claim.
- Like the Sturm slice, the sector/region/parity development is stated
  against `Polynomial ℝ`/`ℂ` with no `HexRealRoots` dependence, ready
  as a Mathlib contribution in its own right.

## Root-count certificates over Mathlib polynomials

`SturmCertificate` checks signed remainder identities over `Polynomial ℝ`.
`Sturm.RemainderChain.pair` terminates a certificate at a nonzero constant;
`Sturm.RemainderChain.cons` prepends a positive scaled remainder identity.
The derivative relation gives `RemainderChain.isSturmChain` and
`RemainderChain.separable` separately. `RemainderChain.card_rootSet` works for
any coefficient ring equipped with an algebra map into `ℝ`.

`RealRootCount` provides the tactic `by real_root_count` and the term elaborator
`real_root_count p`. Both accept closed squarefree integer-coefficient
polynomials over `ℚ` of positive degree. The generator and rational division
run at elaboration time; the emitted proof checks polynomial identities,
nonvanishing, positivity, and the natural-number variation count.

The generic Sturm statements, certificate checker, polynomial parser, and
root-count elaborator agree with their Mathlib counterparts after module-path,
parser-namespace, and documentation-markup translation. Run
`python3 scripts/check_sturm_sync.py /path/to/mathlib` to check that agreement.
Once the pinned Mathlib release contains the development, these companion
modules can re-export the corresponding Mathlib modules.

## Sturm-Tarski correspondence

`TarskiInterpret.lean` supplies the actual signed identities and degree bounds
under noninjective coefficient interpretation, the sufficient internal degree
bound, and produced-chain acceptance. `TarskiInteger.lean` instantiates positive
content normalization over `Int` and proves produced-certificate acceptance and
agreement with the query's returned value. `TarskiGcd.lean` proves terminal-gcd
correspondence, the squarefreeness check and success exactly on squarefreeness
plus the executable endpoint guards. `TarskiDomain.lean` proves integer/dyadic
endpoint correspondence, exact mathematical domain equivalence and domain
soundness of accepted replay. Root-sum and semantic replay soundness,
singleton-sign and count/bound results below remain proof gates.

`TarskiCompare.lean` proves that arbitrary accepted chains for positively
scaled inputs have equal lengths and entrywise positive scaling under their
coefficient interpretations. It extracts the field remainder equations from
the actual initial, step and terminal checks, including singleton chains and
nonconstant terminal gcds. `TarskiSigns.lean` turns that comparison into finite and infinite
endpoint sign-array equality and extracts the checked variation value.
These algebraic proofs do not assume the signed-remainder/root-sum theorem.

First extend endpoint evaluation to the computational owner's
`sturmVarAtRat`. Prove `sturmVarAtRat_eq` by positivity of the homogeneous
denominator factor in each chain entry, `sturmVarAtRat_dyadic` by equality
of exact signs at a dyadic's rational value, and `sturmCountRat_eq` by the
existing half-open Sturm theorem at rational endpoints cast to `ℝ`.
An upper endpoint root contributes one; a lower endpoint root contributes
zero. This rational-count extension does not require the root-free guards
of the separate Tarski-query API.

The [Tarski-query primitive](../../HexRealRoots/SPEC/hex-real-roots.md#tarski-queries)
requires new signed-remainder/Cauchy-index semantics here. Prove
`tarskiQuery_eq`, identifying the executable variation drop with the sum of
`sign (f(α))` over the real roots of squarefree nonzero `p` in the interval,
under its non-root endpoint guards. Prove `tarskiQuery_isSome` for that domain
and `tarskiQuery_sign` when the interval isolates exactly one root. Zero `f`,
zero initial remainder, a nonconstant common gcd, negative query values and
constant `p` are part of the contract.

`IntTarskiCertificate.check_sound` must derive the same signed sum from accepted
literal data. Transport positive-scaled remainder identities through the
integer-to-real cast, prove that reducing `f*p'` modulo `p` preserves the
Cauchy index, and allow termination at a nonconstant gcd. The present
`Sturm.IsSturmChain` root-flank orientation and root-count conclusion do not
prove this statement: a root where `f` is negative contributes `-1`, and a
common root contributes zero. Introduce the signed-query theorem without
weakening the existing Sturm-count predicate or its theorems.

The abstract foundation is a planned Tau Ceti import through this companion,
shared by the integer frontend and
[hex-sturm](../../SPEC/Libraries/hex-sturm.md#required-correspondence-and-specialization-theorems).
It is not a second proof from the existing derivative-chain theorem.
The [Sturm–Tarski theorem](https://www.isa-afp.org/entries/Sturm_Tarski.html)
is prior art, not an existing Lean import. This companion supplies
the root/sign semantics; `hex-number-field-mathlib` composes them with its
chosen-real-embedding theorem to prove `QAdjoin.signTarski_eq` against
`realCompare`. No reverse dependency on number fields is introduced.
Literal kernel replay belongs to the fresh-module proof evidence track;
query construction and endpoint evaluation belong to the computational
owner's ordinary benchmarks. A general comparison elaborator is deferred.

### Shared foundation and proof ownership

The following are planned statement shapes, not available declarations at
the [Mathlib pin](../../lake-manifest.json)
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. Import the family foundation
requested from Tau Ceti by [#10300](https://github.com/kim-em/hex-dev/issues/10300)
once here: polynomial IVT on `[a,b]`, Rolle between distinct roots, and the
signed-remainder/Cauchy-index formula. With
`[Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]`, that
formula equates zero-skipping variation drop to
`∑ α ∈ Roots(P;a,b), sign (F.eval α)` for nonzero squarefree `P`, strictly
ordered finite or infinite endpoints, and nonvanishing at finite endpoints.
It includes `F=0`, initial reduction of `F*P'`, zero initial remainder,
positive-scaled recurrence identities and nonconstant terminal gcd; root
count is the `F=1` specialization. It must not assume `P,F` are coprime.

### Abstract signed remainders

Use `sgn : R → Int` with values `-1,0,1`, and the finite set
`Roots(P;a,b)` of **distinct** roots (`P.roots.toFinset` filtered by strict
endpoint inequalities). Infinite endpoint inequalities impose no bound on
that side. Require `P≠0`, `Squarefree P`, `a<b` and nonzero evaluations of
`P` at finite endpoints. For arbitrary `F : Polynomial R`, the planned
shared theorem `HexRealRootsMathlib.Tarski.variation_eq` has the following
explicit certificate hypotheses:

```text
S₀ = P
u*(F*P') = A*P + v*S₁,                       u>0, v>0
lᵢ*Sᵢ = Qᵢ*Sᵢ₊₁ - rᵢ*Sᵢ₊₂,                lᵢ>0, rᵢ>0
l*Sₘ₋₁ = Q*Sₘ,                              l>0
```

Scalars multiply polynomials as constant polynomials. In the non-singleton
case, all entries are nonzero, `deg S₁<deg P`, and every subsequent degree
strictly decreases. Here `deg` is `natDegree` of a certified nonzero entry;
zero is handled separately. The terminal identity is required even when the last
entry has positive degree. There is no coprimality assumption on `P,F`.
For the singleton `[P]`, replace the initial identity by
`u*(F*P')=A*P` with `u>0`; there is no second entry or terminal pair.
This includes nonzero constant heads and every zero initial remainder.
All branches retain the domain guards.

For a chain entry at a finite endpoint use its evaluation sign. At `+∞`
use its leading-coefficient sign; at `−∞` multiply that by `(-1)^natDegree`.
Delete zeros and count adjacent sign changes to obtain `V`. The conclusion is

```text
(V(a) : Int) - (V(b) : Int) =
  ∑ α ∈ Roots(P;a,b), sgn (F.eval α).
```

Tau Ceti owns the polynomial IVT/Rolle and signed-remainder/Cauchy-index
foundation over arbitrary ordered real closed `R`. The required IVT shape
is: `a≤b`, and `t` between `H.eval a` and `H.eval b` in either order, imply
`∃ c∈[a,b], H.eval c=t`. Rolle is: `a<b` and `H.eval a=H.eval b` imply
`∃ c∈(a,b), H.derivative.eval c=0`. The signed-index theorem uses the
convention in which `P'/P` contributes `+1` at a simple root. It must cover
initial reduction of `F*P'`, arbitrary common factors and infinite endpoints.
The singleton identity gives zero; common roots of `P,F` contribute zero;
`F=1` gives the cardinality of the root set. These are required import
shapes, not existing theorem names. If the imported recurrence is unscaled,
Hex proves positive-rescaling transport to the displayed identities rather
than introducing another analytic proof. Polynomial IVT over `R` does not
assert ordinary topological connectedness of its intervals.

### Representation and replay bridge

Use a nontrivial ordered commutative domain `D`, with an injective
order-preserving ring map `j : D →+* R`. On the Mathlib side use
`[CommRing D] [IsDomain D] [LinearOrder D] [IsStrictOrderedRing D]` and
`StrictMono j`. No `Field D` hypothesis is needed. The computational
Lean-core structures on `D` and these Mathlib structures must have the same
operations, equality and order. Runtime equality/order decisions are total
and executable; classical decisions may occur only in semantic proofs.

Reuse HexPolyMathlib's `DensePoly` arithmetic correspondence. Prove mapping
of the new pseudo-division identities, degree descent and fraction-field
pseudo-gcd guards; the arithmetic owner proves their ordinary core laws.
`degree? = none` corresponds to zero, and `some d` to a nonzero polynomial
of degree `d`. There is no fallible-record interpretation or parallel raw
polynomial representation. For canonical-zero representation coefficients,
use the [execution contract](../../SPEC/real-closure-execution.md): first
interpret them in `D` with operation/sign preservation and zero reflection.
That map need not be injective. Prove degree and actual kernel correspondence
before composing with `j`; quotient laws are not executable prerequisites.

The scalar interpretation preserves natural casts and the explicit executable
sign, as well as the arithmetic used by the shared kernel. Prove squarefree
guards via a semantically nonzero constant gcd or a checked Bézout identity;
a normalized noncanonical coefficient need not be structurally one. Replay
polynomial equations use zero differences. Literal context/operand bindings
remain separate exact-data checks and must be renewed after refinement, even
when an operand literal is unchanged.

Endpoint representations have a total interpretation in `R` and correct
comparison/evaluation operations; dyadics need not belong to `D`. Prove exact
Horner and degree-parity infinity sign agreement. Positive rescaling
preserves signs/variations; translate every initial, step and terminal
identity. Negative scaling alone does not preserve these quantities.

The shared `Hex.TarskiCertificate.check_sound` derives the mathematical guards
and `HexRealRootsMathlib.Tarski.variation_eq` from accepted finite literal data.
Squarefreeness is in the fraction field (hence in `R` in characteristic zero), so integer `4*X`
is accepted. Recurrence identities alone do not prove squarefreeness: a
separate gcd or Bézout guard witness is checked. Prove producer correctness
and produced-certificate acceptance separately from replay soundness.

The generic exact checker uses total field/domain decisions. The tactic
proof interface may discharge expensive coefficient equality/sign obligations
with supplied kernel proofs or finite lower-level certificates bound to the
exact operands and extension context. Prove their composition into the same
abstract chain theorem. This avoids rerunning coefficient refinement or BKR
search in tactic replay; it is not an alternative arithmetic interface.
Nested sign proofs are finite and acyclic, with child claims established
before the parent query. Every split-related reuse needs a denotation
transport proof. No per-addition or per-multiplication certificate is required.

Replay checks initial and terminal data, polynomial identities, positive
scales, nonzero entries, degree descent, finite endpoint guards and variation
counts. It does not rerun chain production, gcd search or root isolation.
Structural checks terminate by literal size; exact arithmetic terminates by
its ordinary laws. Rejected evidence does not prove mathematical invalidity.
For public query producers, `none` means exactly a failed domain guard;
there is no resource-exhaustion outcome. The computational owner's degree
bounds establish termination without a user threshold.

### Real specialization

The Mathlib audit refers to revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` in `lake-manifest.json`.
`Mathlib.FieldTheory.IsRealClosed.Basic` supplies the class and
`IsRealClosed.of_linearOrderedField`, but not `IsRealClosed ℝ` or generic
polynomial IVT/Rolle/Sturm–Tarski. `Mathlib.Analysis.Polynomial.Order`
states its sign results over `ℝ`; those cannot be cited over arbitrary `R`.
The existing local `Sturm.IsSturmChain` likewise remains a structure over `ℝ`
with derivative root flanks and a root-free tail, not this signed theorem.

This companion proves `Real.instIsRealClosed` in `RealClosed.lean` using
`IsRealClosed.of_linearOrderedField`. Its nonnegative-square obligation is
supplied by `Real.sqrt` and `Real.sq_sqrt`. The private `real_odd_root`
proves that every odd-degree polynomial over ℝ has a root: assuming no root
makes both root-bound hypotheses vacuous, so Mathlib's polynomial order
lemmas at zero give contradictory signs in odd degree (split on the
leading-coefficient sign). Those real order lemmas already use continuity/IVT
internally. This uses existing real analysis, not the generic Tau Ceti IVT
that already assumes `IsRealClosed`.
The umbrella exports the instance; the downstream real-algebraic companion
uses `IsRealClosed.exists_isRoot_of_odd_natDegree`. The lower companion has no
import of hex-real-algebraic-mathlib, and the odd-root proof has only one copy.

Instantiate the shared domain/replay bridge with `D=ℤ`, `j=Int.castRingHom ℝ`
and exact dyadic evaluation to prove `ZPoly.tarskiQuery_eq` and
`IntTarskiCertificate.check_sound` here. Also retain `tarskiQuery_isSome` for exactly
the nonzero/squarefree/root-free domain and `tarskiQuery_sign` for a singleton
root set. `DyadicInterval.lt` already supplies endpoint ordering. Optimized
integer content and dyadic Horner operations must correspond to the shared
kernel. No generic field frontend is imported to prove these specializations.

[hex-sturm-mathlib](../../SPEC/Libraries/hex-sturm-mathlib.md) consumes these
shared results for field guards, generic endpoint sign operations, coefficient-proof
composition, positive rational denominator clearing and `rootCount_eq`.
Real-closure existence for arbitrary ordered fields remains a separate Tau
Ceti obligation consumed downstream by hex-real-closure-mathlib. All missing
results above are planned proof obligations, never new axioms, and the
existing derivative `Sturm.IsSturmChain` development remains unchanged.

Shared replay conformance must include negative sums, common gcds, zero
initial remainder, constants, semantic degree cancellation and rejected
scales/terminal data. Integer specialization tests include `4*X` and finite
root-endpoint rejection. General and non-Archimedean frontend integration
fixtures are owned by the new companion's
[conformance contract](../../SPEC/Libraries/hex-sturm-mathlib.md#conformance-and-phase-4-evidence).
Measure shared literal replay through fresh-module kernel proof probes,
recording axiom sets and artifact sizes; keep arithmetic producer benchmarks
in the Mathlib-free owner. Nested evidence size and rejected-certificate paths
are explicit proof-probe dimensions, not hidden coefficient-oracle costs.

## File organisation

```
HexRealRootsMathlib/
  RealClosed.lean      -- Real.instIsRealClosed from real analysis
  SturmChainDefs.lean  -- IsSturmChain, sturmVar over Polynomial ℝ
  SturmTheorem.lean    -- the counting theorem and the line form
  SturmCertificate.lean -- certificates over Mathlib polynomials
  RealRootCount.lean   -- checked root-count tactic and term elaborator
  SturmTests.lean      -- endpoint conventions and constant chains
  RealRootCountTests.lean -- root counts and elaborator diagnostics
  ChainCorrespond.lean -- executable-chain correspondence and the shared
                          recurrence/cast helpers; sturmCount_eq_card_roots;
                          compatibility aliases for HexPolyZMathlib.Squarefree
  LiteralChain.lean    -- abstract and integer literal recurrences,
                          IsSturmChain/squarefree consequences, literal counts
  LiteralChainTests.lean -- proof-level literal-replay regressions
  LiteralIsolations.lean -- unique-root and full-coverage semantics for
                            supplied interval and total counts
  Discr.lean            -- compatibility import of the shared discriminant API
  Hadamard.lean         -- compatibility import of the shared determinant bound
  Separation.lean      -- sepPrec_separates, rootBound_bounds_roots;
                          specializes shared Mahler/Vandermonde analysis
  Isolations.lean      -- executable-count forms of exists_unique_root,
                          isolates
  IsolateRoots.lean    -- IsolatedRealRoots, its constructors, the
                          bridge tactic, and the isolate_roots
                          term elaborator
  Drivers.lean         -- isolateSturm?_isSome, isolateRealRoots?_isSome,
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
  1982: see the [hex-real-roots SPEC](https://github.com/leanprover/hex-real-roots/blob/main/SPEC/hex-real-roots.md) §"References".
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
