# hex-rcf (decision procedure for univariate real-closed-field formulas, depends on hex-real-roots + hex-real-roots-mathlib + hex-poly-z + hex-poly-z-mathlib + Mathlib)

A Lean tactic providing a **complete decision procedure** for the
univariate fragment of real-closed-field arithmetic. Closes goals
that are Boolean combinations of polynomial (in)equalities in one
real variable, with universal/existential quantifiers over `ℝ` or
over bounded dyadic intervals.

Reflective implementation: reify the goal to a `Formula` AST,
form the squarefree product of every polynomial appearing in the
formula, isolate its roots via
[hex-real-roots](hex-real-roots.md), build the **sign matrix** over
the resulting cell decomposition of `ℝ`, evaluate the Boolean on
each cell, check the quantifier, and close the goal via a
soundness-of-reflection lemma proved in this same library. No
separate Mathlib bridge — `hex-rcf` is `mathlib: true` because the
tactic targets `ℝ`.

This is the user-facing payoff of the algebraic-numbers stack:
neither `polyrith` nor `nlinarith` is complete on this fragment,
and `decide` is unavailable for `ℝ`-quantifiers. `hex-rcf` decides
the entire univariate fragment of the theory of real-closed fields
(per Tarski 1948).

## What `rcf` decides

Goal forms:

```lean
∀ x : ℝ,                             p₁(x) ⊳₁ 0 ∨ p₂(x) ⊳₂ 0 ∧ ¬ p₃(x) ⊳₃ 0 …
∃ x : ℝ,                             …
∀ x : ℝ, q(x) ≥ 0 →                  p(x) > 0
∀ x ∈ Set.Ioc a b,                   p(x) ⊳ 0           -- a, b : Dyadic
∃ x ∈ Set.Ioc a b,                   p(x) = 0           -- root in interval
```

The atoms `pᵢ ⊳ᵢ 0` use `pᵢ ∈ ℤ[x]` (or `ℚ[x]`, cleared to `ℤ[x]`)
and `⊳ᵢ ∈ {<, ≤, =, ≥, >, ≠}`. Boolean connectives `∧`, `∨`, `¬`
nest freely.

Concrete examples the tactic closes:

```
∀ x : ℝ,                                  x² + 1 > 0
∀ x : ℝ, 0 ≤ x →                          x³ + x ≥ 0
∀ x : ℝ, 0 < x →                          x + 1/x ≥ 2
∀ x : ℝ, x² ≤ 1 →                         x⁴ − x² ≤ 0
∃ x : ℝ, x³ − x − 1 = 0   ∧   1 < x ∧ x < 2
```

## What `rcf` does NOT decide (and how it falls through)

The tactic must **fall through** (not produce a wrong proof, not
loop forever) on any goal it cannot decide. Cases:

- **Multivariate** goals (free variables ≠ 1 in the
  reified formula). `∀ a x, ax² + 1 > 0` has two free variables;
  the tactic refuses.
- **Transcendental** terms: `sin`, `exp`, `log`, etc. The tactic
  recognises these as non-polynomial atoms and refuses.
- **Parameterised** atoms where coefficients are not concrete
  integers: `∀ x : ℝ, x² + a > 0` (where `a` is a free variable)
  reduces to multivariate.
- **Goals with an unprovable conclusion.** The tactic only emits
  "yes" answers; it does not produce a counterexample-style
  rejection. On unprovable goals, it falls through silently.
- **Bounded quantifiers over `Set.Icc` or `Set.Ioo`.** The tactic
  natively decides only `Set.Ioc a b` quantification (matching
  `hex-real-roots`'s half-open isolation convention). Users with
  closed- or open-interval goals reduce to half-open by evaluating
  endpoints — e.g. `∃ x ∈ Set.Icc a b, p(x) = 0` becomes
  `p(a) = 0 ∨ ∃ x ∈ Set.Ioc a b, p(x) = 0`. Future work could
  encode endpoint-closure in the AST; out of scope for v1.

Falling through is implemented as the tactic raising
`MetaM`-failure with a clear message; downstream tactics
(`decide`, `nlinarith`, etc.) can take over.

Multivariate generalisation is *Cylindrical Algebraic
Decomposition* (CAD), which is exponentially expensive; explicitly
out of scope. Univariate is the practical sweet spot.

## Algorithm (reflective)

The tactic implements 1-dimensional CAD:

1. **Reify** the goal to a `Formula` AST:

    ```lean
    inductive AtomCmp where
      | lt | le | eq | ge | gt | ne

    inductive Atom where
      | poly (p : ZPoly) (cmp : AtomCmp)   -- represents `p(x) ⊳ 0`

    inductive Formula where
      | atom    (a : Atom)
      | tt
      | ff
      | not     (φ : Formula)
      | and     (φ ψ : Formula)
      | or      (φ ψ : Formula)
      | implies (φ ψ : Formula)
      -- Quantifiers wrap a Formula whose only free atom-variable
      -- is the bound x.
      | forallReal     (φ : Formula)
      | existsReal     (φ : Formula)
      -- Bounded quantifiers range over `Set.Ioc a b`, matching
      -- `hex-real-roots`'s half-open isolation convention.
      | forallInterval (a b : Dyadic) (φ : Formula)
      | existsInterval (a b : Dyadic) (φ : Formula)

    structure ReifiedGoal where
      formula : Formula
      -- plus the proof obligation: `formula.toProp` is the original
      -- Lean Prop the user asked us to prove.
    ```

   The reification machinery lives alongside the tactic in this
   library; it uses Lean's `Qq` / `Lean.Meta` infrastructure.

2. **Reject out-of-fragment input** (bail with `MetaM` failure).

3. **Collect atoms' polynomials.** Walk `formula` and gather every
   `pᵢ ∈ ZPoly` appearing in an `Atom.poly pᵢ cmpᵢ`.

4. **Form the squarefree product** `P := squarefreePart (∏ᵢ pᵢ)`,
   computed as `(∏ᵢ pᵢ) / gcd(∏ᵢ pᵢ, (∏ᵢ pᵢ)')`. The real roots of
   `P` are precisely the union of the real roots of all `pᵢ`, with
   multiplicity 1 each (shared roots across atoms collapse into a
   single root of `P`; multiplicities within a single `pᵢ` are
   killed by the squarefree quotient). Then call
   `Hex.isolate? P hP_simple targetPrecision`, where
   `hP_simple : Hex.HasOnlySimpleRealRoots P` is automatic from the
   squarefree-by-construction `P`. If the call returns `none`,
   raise `targetPrecision` (e.g. to `Hex.realRootSeparation P`,
   where the bridge guarantees `some`) and retry. The result is a
   pairwise-disjoint array of `RealRootIsolation P`.

5. **Build the cell decomposition.** Use the `isolate?` output for
   `P` directly. Sort isolations by lower endpoint; the cells are:

   ```
   (−∞, root₁), {root₁}, (root₁, root₂), {root₂}, …, (rootₖ, +∞)
   ```

   Each "open interval" cell has a sign-constant interior for
   *every* `pⱼ` (an interior point cannot be a root of any `pⱼ`,
   else it would be a root of `P`). Each "root point" cell is a
   root of some subset of the `pⱼ`s (those `pⱼ` having that real
   root). Test points: any dyadic rational in the open-interval
   cell (e.g. midpoint of consecutive isolation upper/lower
   bounds); for root-point cells, the cell *is* the root.

6. **Sign matrix.** For each cell, evaluate the integer sign of
   each `pⱼ` at the cell's representative point.
   - Open-interval cells: evaluate `pⱼ` at the dyadic test point.
     The result is in `{−1, +1}` (never zero: a zero would mean
     the test point is a root of `pⱼ`, hence of `P`, hence not
     interior to the cell).
   - Root-point cells: the cell is a real root `r` of `P`. The
     relevant `pⱼ`s with `pⱼ(r) = 0` are determined at the
     polynomial level: `pⱼ(r) = 0` iff `r` is a root of
     `gcd(pⱼ, P)`. Precompute `gⱼ := gcd(pⱼ, P)` for each `j`,
     and isolate the roots of each `gⱼ`; root-point cell `r` has
     `sign pⱼ(r) = 0` iff some isolation of `gⱼ` contains the
     same `RealRoot P`-equivalence-class as `r`. For `pⱼ` with
     `pⱼ(r) ≠ 0`, the sign at `r` equals `sign pⱼ` on either of
     the two adjacent open-interval cells (which agree because no
     root of `pⱼ` lies between them other than possibly `r`
     itself).

   The result is a `m × k` matrix of signs `{−1, 0, +1}`.

7. **Boolean evaluation.** For each cell, substitute the per-`pⱼ`
   sign into each `Atom.poly pⱼ cmpⱼ`'s comparison, getting `True`
   or `False` for each atom. Evaluate the Formula's Boolean
   structure recursively to get a per-cell truth value.

8. **Quantifier check.**
   - `∀ x : ℝ, φ`: every cell evaluates true.
   - `∃ x : ℝ, φ`: some cell evaluates true.
   - `∀ x ∈ Set.Ioc a b, φ`: every cell *intersecting* `(a, b]`
     evaluates true.
   - `∃ x ∈ Set.Ioc a b, φ`: some cell *intersecting* `(a, b]`
     evaluates true.

9. **Reflection.** The decision result `true`/`false` is reflected
   back to the original goal via the soundness lemma
   `rcf_decide_sound` (below). On `true`, the tactic emits a
   proof. On `false`, the tactic emits no proof and falls through —
   it does not negate the goal.

## Soundness theorem (in this library; no separate Mathlib bridge)

```lean
def Formula.toProp : Formula → Prop
  -- Evaluate the AST against ℝ-valued atoms, with quantifiers
  -- ranging over ℝ (or the specified Dyadic interval).

def decide_rcf : Formula → Bool
  -- Run the algorithm above; return whether the formula is valid.

theorem rcf_decide_sound :
    ∀ (φ : Formula), decide_rcf φ = true → φ.toProp
```

This is the **soundness lemma**: every "yes" answer produces a
genuine proof of the corresponding `ℝ`-Prop. The proof factors
through:

- **Sign-matrix correctness.** For each cell, the signs are correct
  at *every* point in the cell (not just the representative). This
  follows because each `pⱼ` is sign-constant on cell interiors (no
  `pⱼ` has a root strictly between consecutive `P`-roots, since
  every real root of every `pⱼ` is a real root of `P`), and the
  zero-detection at root-point cells is correct by definition of
  `gⱼ := gcd(pⱼ, P)`.
- **Cell-decomposition completeness.** Every real number lies in
  exactly one cell of the `P`-decomposition. Follows from
  `isolate?_correct` applied to `P`: every real root of `P` is
  isolated by exactly one interval, the intervals are pairwise
  disjoint, and the open-interval cells between consecutive
  isolations (plus the two tails) partition `ℝ ∖ {real roots of P}`.
- **Boolean evaluation correctness.** Substituting signs into atoms
  gives the correct truth value at every point in the cell.
- **Quantifier correctness.** ∀/∃ on cells lifts to ∀/∃ on `ℝ`
  because cells partition `ℝ` and the inner Prop is constant on
  each cell.

Imports: `hex-real-roots-mathlib`'s `isolate?_correct` and the
Möbius-transform-correspondence theorem; Mathlib's IVT,
`Polynomial.aeval`, ordered-field structure on `ℝ`,
`Polynomial.gcd` over `ℤ[x]`.

The library does **not** prove completeness (that every valid
univariate ℝ-CF formula is decided correctly). Tarski–Seidenberg
gives this for free, but the tactic only ever emits "yes" answers;
"no" answers are never emitted as Lean proofs (the tactic falls
through). So soundness is sufficient for tactic correctness.

## Tactic surface

```lean
example : ∀ x : ℝ, x^2 + 1 > 0 := by rcf
example : ∀ x : ℝ, 0 < x → x + 1/x ≥ 2 := by rcf
example : ∃ x : ℝ, x^3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by rcf
```

Tactic name: `rcf` (for "real-closed field"). Algorithm-neutral —
the tactic name does not commit to which root-isolation algorithm
`hex-real-roots` uses internally.

## Layered file organisation

- `HexRCF/Formula.lean` — the AST (`Atom`, `Formula`,
  `AtomCmp`); `Formula.toProp` Prop semantics; `decide_rcf`
  driver.
- `HexRCF/CellDecomposition.lean` — union-of-isolations cell
  construction; representative-point selection; cell-set invariants.
- `HexRCF/SignMatrix.lean` — per-cell, per-atom sign evaluation;
  Boolean evaluation of `Formula` against the sign matrix.
- `HexRCF/QuantifierCheck.lean` — ∀/∃ checks (full ℝ + bounded
  intervals); cell-intersection logic.
- `HexRCF/Soundness.lean` — `rcf_decide_sound` and supporting
  lemmas (sign-matrix correctness, cell-decomposition completeness,
  Boolean and quantifier soundness).
- `HexRCF/Reflect.lean` — `MetaM`/`Qq` reification; tactic
  driver; `MetaM`-failure paths for out-of-fragment input.
- `HexRCF/Tactic.lean` — the user-facing `rcf` tactic
  registration.
- `HexRCF/Conformance.lean`, `HexRCF/Bench.lean`,
  `HexRCF/EmitFixtures.lean` — standard testing trio.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md):

- *core* (Lean-only):
  - **Provable, simple polynomials:**
    - `∀ x : ℝ, x² + 1 > 0`
    - `∀ x : ℝ, 0 ≤ x → x³ + x ≥ 0`
    - `∀ x : ℝ, 0 < x → x + 1/x ≥ 2`  *(after `field_simp`-style
      preprocessing or stated as `∀ x > 0, x² + 1 ≥ 2x`)*
    - `∀ x : ℝ, x² ≤ 1 → x⁴ − x² ≤ 0`
  - **Existential with explicit witness location:**
    - `∃ x : ℝ, x³ − x − 1 = 0 ∧ 1 < x ∧ x < 2`
  - **Squarefree polynomial root absence:**
    - `∀ x : ℝ, x² + 2x + 2 ≠ 0`
  - **Fall-through cases (tactic must refuse, not produce a wrong proof):**
    - Multivariate: `∀ a x : ℝ, a*x² + 1 > 0` — refused
      (multivariate).
    - Transcendental: `∀ x : ℝ, sin x ≤ 1` — refused
      (non-polynomial atom).
- *ci* (CI, with external oracle when available): 30 deterministic
  univariate goals constructed from random small-coefficient
  polynomials. Oracle: SageMath's `QQbar.real_roots` + manual
  formula evaluation, or Mathematica's `Reduce`.
- *local* (developer-driven): high-degree adversarial families
  (Mignotte-near-zero polynomials, polynomials with extremely close
  roots requiring high-precision sign matrix). Note: these stress
  `hex-real-roots`'s Uspensky algorithm, which has known
  performance pathologies on tight clusters; bench-driven
  validation that the tactic still terminates within budget on
  these cases.

External oracles: SageMath (`Reduce`-equivalent via
`QQbar`-based real-root analysis); Mathematica (`Reduce`,
`Resolve`); Wolfram Alpha for one-off cross-checks.

## Complexity contract

For a goal with `k` distinct polynomials of total degree `n` and
sup-norm `‖·‖∞`:

- **Reification:** linear in goal size.
- **Squarefree product** `P := squarefreePart (∏ pⱼ)`: degree `≤ k·n`,
  computation dominated by polynomial gcd.
- **Root isolation** of `P`: `O((k·n)^4 · log² ‖P‖∞)` bit operations
  (Uspensky's worst case, per `hex-real-roots.isolate?`).
- **Cell decomposition:** `O(k·n)` cells (one per real root of `P`,
  plus open-interval cells between them).
- **Sign matrix:** `O(k · n²)` polynomial evaluations.
- **Boolean evaluation:** `O(k · |formula|)` per cell.
- **Total:** dominated by root isolation, roughly
  `O(k · n^4 · log² ‖·‖∞)`.

For typical user goals (`k ≤ 5`, `n ≤ 10`, small coefficients) the
tactic should complete in under a second. Mignotte-cluster
adversarial cases are bounded by `hex-real-roots`'s
`realRootSeparation` — sub-second for moderate inputs but degrades
gracefully on high-degree pathological clusters.

## Time budgets (Phase 4 validation)

- Linear or quadratic goal, `k = 1`, `n ≤ 4`: < 100 ms.
- Polynomial goal of degree ≤ 10, `k ≤ 3`: < 1 second.
- Adversarial degree-50, `k = 1`: < 30 seconds.

## References

- Tarski, A. *A Decision Method for Elementary Algebra and
  Geometry.* RAND Corp, 1948 (republished by Univ. California
  Press, 1951). The foundational decidability result for the
  theory of real-closed fields.
- Descartes 1637 / Uspensky 1948 / Akritas–Strzeboński 2008 — see
  [hex-real-roots](hex-real-roots.md) §"References" for the
  underlying root-isolation algorithm.
- Basu, S.; Pollack, R.; Roy, M.-F. *Algorithms in Real Algebraic
  Geometry.* Springer, 2nd ed., 2006. Algorithm 10.13 (Sign
  Determination at the Roots) and Chapter 13 (CAD) cover the
  univariate sign-matrix construction this library implements.
- Cohen, A. M. (ed.) *A Mathematical Companion to Computer
  Algebra.* Springer, 2002. §3 (Real Algebraic Geometry).
