# hex-rcf (decision procedure for univariate real-closed-field sentences, depends on hex-real-roots + hex-real-roots-mathlib + hex-poly-z + hex-poly-z-mathlib + Mathlib)

A Lean tactic, `rcf`, deciding the univariate fragment of
real-closed-field arithmetic: Boolean combinations of polynomial
(in)equalities in one real variable under a single quantifier over
`ℝ` or over a half-open dyadic interval. The procedure is complete on
this fragment in the following sense: `isolate?` succeeds on
squarefree input by `isolate?_isSome` from
[hex-real-roots-mathlib](hex-real-roots-mathlib.md), so the compiled
search reaches a verdict on every in-fragment sentence, and every
`true` verdict becomes a kernel-checked proof. On a `false` verdict
the tactic fails with a message naming a witness cell. It never
proves a negation: no theorem turns a `false` verdict into a proof,
so only the `true` direction is trusted.

This is the user-facing payoff of the real-root machinery: neither
`polyrith` nor `nlinarith` is complete on this fragment, and `decide`
does not apply to quantifiers over `ℝ`. Decidability of the full
theory is Tarski's theorem. This library implements the
one-variable case, where the cell decomposition of `ℝ` by the roots
of a single polynomial replaces cylindrical algebraic decomposition.

`hex-rcf` is `mathlib: true` (the tactic targets `ℝ`), and its
soundness theorem lives in the same library. There is no separate
`hex-rcf-mathlib`.

## What `rcf` decides

Sentence forms, with `pᵢ ∈ ℤ[x]` (or `ℚ[x]`, cleared to `ℤ[x]` by
the reifier) and `⊳ᵢ ∈ {<, ≤, =, ≥, >, ≠}`:

```lean
∀ x : ℝ, φ(x)
∃ x : ℝ, φ(x)
∀ x ∈ Set.Ioc (a : ℝ) b, φ(x)     -- a, b dyadic numerals
∃ x ∈ Set.Ioc (a : ℝ) b, φ(x)
```

where `φ` is any Boolean combination (`∧`, `∨`, `¬`, `→`) of atoms
`pᵢ(x) ⊳ᵢ 0`. The reifier normalises `s ⊳ t` to `(s − t) ⊳ 0` and
clears rational denominators from numeral coefficients (multiplying
an inequality only by positive constants).

Concrete examples the tactic closes:

```lean
∀ x : ℝ, x² + 1 > 0
∀ x : ℝ, 0 ≤ x → x³ + x ≥ 0
∀ x : ℝ, 0 < x → x² + 1 ≥ 2*x
∀ x : ℝ, x² ≤ 1 → x⁴ − x² ≤ 0
∃ x : ℝ, x³ − x − 1 = 0 ∧ 1 < x ∧ x < 2
```

## What `rcf` does not decide, and how it falls through

The tactic must fail cleanly (no wrong proof, no unbounded search) on
anything outside the fragment:

- **More than one variable.** `∀ a x : ℝ, a*x² + 1 > 0` reifies with
  two free variables, so the reifier refuses. The multivariate theory
  needs cylindrical algebraic decomposition and is out of scope.
- **Non-polynomial atoms.** `sin`, `exp`, `abs`, division by terms
  containing the variable (`x + 1/x ≥ 2`). The reifier refuses. For
  division, the error message suggests clearing denominators by hand
  first (for example to `∀ x, 0 < x → x² + 1 ≥ 2*x`).
- **Symbolic coefficients.** `∀ x : ℝ, x² + a > 0` with `a` free is
  the two-variable case.
- **Nested quantifiers.** The `Sentence` type has exactly one
  quantifier, so `∀ x, ∃ y, …` does not reify.
- **`Set.Icc` / `Set.Ioo` quantifiers.** Only `Set.Ioc` matches the
  half-open isolation convention. The error message shows the
  rewrite: `∀ x ∈ Set.Icc a b, φ` is `φ(a) ∧ ∀ x ∈ Set.Ioc a b, φ`,
  and `∃ x ∈ Set.Ioo a b, φ` is `∃ x ∈ Set.Ioc a b, φ ∧ x ≠ b`
  handled by adding the atom.
- **Sentences that are false.** `decide` returns `false` and the
  tactic fails, reporting a cell on which the body evaluates to `false`
  (a concrete dyadic test point, or an isolating interval for a root
  cell), so the user sees a counterexample region rather than a bare
  failure.

Fall-through is a `MetaM` failure with the reason, so downstream
tactics can take over.

## The reflected language

Two levels, matching the algorithm: a quantifier-free body and a
single top-level quantifier. Nested quantifiers are unrepresentable
by construction.

```lean
namespace Hex.RCF

inductive Cmp | lt | le | eq | ge | gt | ne

/-- An atom `p(x) ⊳ 0`. -/
structure Atom where
  p   : ZPoly
  cmp : Cmp

/-- Quantifier-free body: Boolean combinations of atoms. -/
inductive Formula
  | atom (a : Atom)
  | tt | ff
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or  (φ ψ : Formula)
  | imp (φ ψ : Formula)

inductive Sentence
  | forallReal (φ : Formula)
  | existsReal (φ : Formula)
  | forallIoc (a b : Dyadic) (φ : Formula)
  | existsIoc (a b : Dyadic) (φ : Formula)

def Formula.toProp (φ : Formula) (x : ℝ) : Prop
def Sentence.toProp (s : Sentence) : Prop

end Hex.RCF
```

The reifier (`Qq` / `Lean.Meta`) produces a `Sentence` together with
a proof that `Sentence.toProp` of it is definitionally the goal.

## Algorithm

1. **Reify** the goal to a `Sentence`. Refuse anything out of
   fragment.

2. **Collect** the atom polynomials. Constant atoms (degree ≤ 0,
   including the zero polynomial) are evaluated to `tt`/`ff` during
   reification and never reach the decomposition.

3. **Decompose.** Let `P := Hex.ZPoly.squareFreeCore (∏ᵢ pᵢ)` over
   the nonconstant atom polynomials. `P` is squarefree and its real
   roots are exactly the union of the atoms' real roots. Run
   `Hex.isolate? P` and eliminate the `Option` with
   `isolate?_isSome` (squarefreeness of `squareFreeCore` is a lemma
   here, through hex-poly-z-mathlib's gcd correspondence; the
   root-set equality is `aevalIff_squareFreeCore` from the
   hex-real-roots companion's `isolate_roots` development). If there
   are no nonconstant atoms, the decomposition is the single cell
   `ℝ` and steps 4-6 degenerate to one test-point evaluation.

4. **Separate.** Refine the isolations (`refineTo`) until
   consecutive intervals have a nonempty gap between them
   (`upperᵢ < lowerᵢ₊₁`). Bisection can emit touching intervals, and
   the open cells between roots need interior dyadic test points, so
   this step is not optional. It terminates because distinct roots
   have positive gaps. For bounded sentences over `(a, b]`, also
   refine until every interval lies inside `(a, b]` or outside it:
   first test `P(a) = 0` and `P(b) = 0` exactly (an isolation whose
   root *is* an endpoint is classified by that test), then refinement
   separates every other interval from the endpoints.

5. **Build cells.** With isolations `I₁ < … < I_k` (roots
   `r₁ < … < r_k`) and `M := rootBound P`:

   ```
   Cell = tailLeft            -- semantic (−∞, r₁),   test point −M − 1
        | root i              -- semantic {rᵢ},       data Iᵢ
        | gap i               -- semantic (rᵢ, rᵢ₊₁), test point in
                              --   (upperᵢ, lowerᵢ₊₁], which step 4
                              --   made nonempty
        | tailRight           -- semantic (rₖ, +∞),   test point M + 1
   ```

   The semantic cells partition `ℝ`. Every `pⱼ` is sign-constant on
   each open cell: a sign change would put a root of `pⱼ`, hence of
   `P`, strictly between consecutive roots of `P`.

6. **Sign matrix.** For each cell and each atom polynomial `pⱼ`:
   - Open cells: exact Horner evaluation at the cell's dyadic test
     point. The value is nonzero (the test point is in no isolation,
     and roots of `pⱼ` are roots of `P`). A zero value would refute
     the library's own invariants, and the driver fails rather than
     guesses.
   - Root cells: whether `pⱼ(rᵢ) = 0` is exactly
     `sturmCount gⱼ Iᵢ = 1` for `gⱼ := gcdZ pⱼ P` (the integer gcd
     through hex-poly-z's rational gcd and `ratPolyPrimitivePart`):
     `gⱼ` divides `P`, so it has at most one root in `Iᵢ`, and its
     Sturm count decides whether that root exists, which happens
     exactly when `pⱼ` and `P` share the root `rᵢ`. When
     `pⱼ(rᵢ) ≠ 0`, its sign at `rᵢ` equals its sign on the two
     adjacent open cells, which always exist (a gap or a tail on
     each side) and agree: in that case `pⱼ` has no root anywhere
     strictly between the neighbouring `P`-roots (taking `±∞` at the
     ends).

7. **Evaluate.** Substitute each cell's signs into the atoms, fold
   the Boolean structure: one truth value per cell.

8. **Quantify.**
   - `forallReal`: every cell true. `existsReal`: some cell true.
   - `forallIoc a b`: every cell whose semantics meets `(a, b]`
     true; `existsIoc`: some such cell true. Step 4 made "meets
     `(a, b]`" decidable, case by case: root cell `i` meets `(a, b]`
     iff `a < rᵢ ∧ rᵢ ≤ b`, where the endpoint tests identify
     `rᵢ = a` and `rᵢ = b` exactly and otherwise the separated
     interval lies strictly inside or strictly outside; the gap
     `(rᵢ, rᵢ₊₁)` meets `(a, b]` iff `rᵢ < b ∧ a < rᵢ₊₁`;
     `tailLeft` iff `a < r₁`; `tailRight` iff `rₖ < b`; each
     conjunct decided by the same endpoint-test and
     interval-position analysis. With no roots at all, the single
     cell `ℝ` always meets `(a, b]`.

9. **Reflect.** `decide s = true` closes the goal through
   `decide_sound` (below). `false` produces the witness-cell failure
   message.

## Kernel replay

`Sentence.decide : Sentence → Bool` runs the whole pipeline and is
the function the soundness theorem speaks about, but the tactic does
not ask the kernel to evaluate it: re-running the search (bisection,
gcds, refinement) inside the kernel would be far slower than the
compiled search. Following the compiled-prep / kernel-verify pattern
of `irreducible_cert` (hex-berlekamp-zassenhaus), the tactic:

- runs the search compiled, collecting a `Certificate`: the Sturm
  chain of `P` with the quotient of each pseudo-division step, the
  separated isolations, the test points, the sign matrix, and for
  each root-cell test the gcd `gⱼ` (primitive, positive leading
  coefficient) with three multiplication-checkable witnesses:
  quotients for `gⱼ ∣ pⱼ` and `gⱼ ∣ P`, and a denominator-cleared
  Bézout identity `u·pⱼ + v·P = c·gⱼ` with `u, v ∈ ℤ[x]` and a
  nonzero `c : ℤ`;
- emits a proof of `Sentence.check s cert = true` by kernel
  reduction, where `check` only *replays*: it verifies each chain
  step by one polynomial multiply-subtract against the provided
  quotient, re-evaluates the variation counts at the given endpoints
  and test points, re-checks the counts, orderings, and totals, and
  re-folds the Boolean and quantifier steps. No division, no gcd, no
  search in the kernel.

```lean
theorem check_sound (s : Sentence) (cert : Certificate) :
    check s cert = true → s.toProp
```

`check_sound` is the library's one trusted theorem. `decide` is a
convenience wrapper (it builds the certificate and calls `check`)
used by conformance and the external oracle, with

```lean
theorem decide_eq_true_iff_exists_cert :
    decide s = true ↔ ∃ cert, check s cert = true
```

tying the two together.

## Soundness theorem structure

`check_sound` factors exactly along the algorithm:

- **Chain and count replay.** The certificate's chain satisfies the
  step relation, so it is the Sturm chain up to positive scalars, so
  the replayed counts are root counts
  (`sturmChain_isSturmChain`, `sturmCount_eq_card_roots` from
  hex-real-roots-mathlib).
- **Cell partition.** The replayed isolations form a
  `RealRootIsolations P` value, so its semantic theorem
  (`RealRootIsolations.isolates`) makes the semantic cells a
  partition of `ℝ`.
- **Sign matrix.** On open cells: sign constancy from
  root-containment (roots of `pⱼ` are roots of `P`) plus the exact
  test-point evaluation. On root cells: the `gⱼ` count argument of
  step 6. The divisibility witnesses give that every root of `gⱼ` is
  a common root of `pⱼ` and `P`, the Bézout identity gives the
  converse, and `gⱼ` is squarefree because it divides the squarefree
  `P`, which is what lets `sturmCount_eq_card_roots` apply to it.
- **Boolean and quantifier steps.** The per-cell fold computes
  `Formula.toProp` at every point of the cell (signs determine
  atoms), and the quantifier step lifts cell-wise truth to `ℝ` or to
  `(a, b]` because the cells partition and the classification of
  step 8 is exact.

No completeness theorem is stated for `decide` (that `false` implies
the negation): the tactic never uses a `false` verdict as a proof,
and Tarski-style completeness of the fragment is not a consumer-facing
obligation.

## Tactic surface

```lean
example : ∀ x : ℝ, x^2 + 1 > 0 := by rcf
example : ∀ x : ℝ, 0 < x → x^2 + 1 ≥ 2*x := by rcf
example : ∃ x : ℝ, x^3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by rcf
```

The name is algorithm-neutral: it names the theory fragment (real
closed fields), not the isolation method, which hex-real-roots is
free to change.

## File organisation

- `HexRCF/Language.lean`: `Atom`, `Formula`, `Sentence`, `toProp`.
- `HexRCF/Certificate.lean`: `Certificate`, `check`, `decide`.
- `HexRCF/Cells.lean`: separation refinement, cell construction,
  endpoint classification for bounded sentences.
- `HexRCF/SignMatrix.lean`: test-point evaluation, the `gⱼ` root-cell
  computation, Boolean folding.
- `HexRCF/Soundness.lean`: `check_sound` and its four factors.
- `HexRCF/Reify.lean`: `Qq`/`MetaM` reification, normalisation,
  fall-through messages.
- `HexRCF/Tactic.lean`: the `rcf` front end.
- `conformance/HexRCF/{Conformance,EmitFixtures}.lean`: conformance
  in the shared sub-project.

No bench target: bench targets must not import Mathlib
([SPEC/benchmarking.md](../benchmarking.md)), and this library
cannot avoid it. The time budgets below are validated through the
`local` conformance profile, which times elaboration of the fixture
file.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md):

- *core* (Lean-only):
  - The five example sentences above, as `example … := by rcf`.
  - `∀ x : ℝ, x² + 2x + 2 ≠ 0` (no real roots).
  - Bounded quantifiers: `∃ x ∈ Set.Ioc (1 : ℝ) 2, x³ − x − 1 = 0`,
    and a `forallIoc` case whose truth depends on an endpoint being
    a root (exercising the `P(b) = 0` classification).
  - Fall-through, asserted to fail: the two-variable example, a
    `sin` example, a division example, an `Icc` example, and one
    false sentence (`∃ x : ℝ, x² + 1 = 0`) checking the witness-cell
    message.
- *ci* (external oracle): 30 sentences over random small-coefficient
  polynomials from a deterministic seed, serialised with expected
  verdicts. The oracle evaluates them in SageMath (`QQbar` real
  roots plus interval evaluation) against `decide`'s output.
- *local*: Mignotte-cluster atoms and degree-50 sentences, timing
  the pipeline where the isolation layer is under stress.

## Complexity contract

For a sentence with `m` atoms of degrees summing to `n`:

- Reification: linear in the goal.
- `P`: one product and one `squareFreeCore`, `deg P ≤ n`.
- Isolation: hex-real-roots' contract at degree `deg P`.
- Separation refinement: `O(k)` chain evaluations per level of extra
  precision, `k ≤ n` roots.
- Sign matrix: `k` root cells × `m` atoms, one `gⱼ` gcd and count
  each, plus `(k + 1)·m` open-cell evaluations.
- Certificate replay in the kernel: linear in the certificate, all
  multiplication and comparison.

For typical goals (`m ≤ 5`, `deg ≤ 10`, small coefficients) the whole
pipeline is dominated by elaboration overhead, not arithmetic.

## Time budgets (Phase 4 validation)

- Quadratic goals, one atom: under 100 ms.
- Degree ≤ 10, up to 3 atoms: under 1 second.
- Adversarial degree-50, one atom: under 30 seconds.

## References

- Tarski. *A Decision Method for Elementary Algebra and Geometry.*
  RAND Corporation, 1948; University of California Press, 1951.
  Decidability of the full theory.
- Basu, Pollack, Roy. *Algorithms in Real Algebraic Geometry.*
  Springer, 2nd ed., 2006. Sign determination at roots (Algorithm
  10.13) and the one-variable decision procedure this library
  implements.
- Li, Paulson. *A modular, efficient formalisation of real algebraic
  numbers.* CPP 2016, and the derived univariate decision procedure
  in Isabelle/HOL. The closest existing artifact to `rcf`.
- Cohen, Mahboubi. *Formal proofs in real algebraic geometry.* LMCS
  8(1), 2012. The Coq/MathComp quantifier-elimination development.
- McLaughlin, Harrison. *A proof-producing decision procedure for
  real arithmetic.* CADE-20, 2005. Proof-producing RCF decisions in
  HOL Light.
