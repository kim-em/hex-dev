# hex-rcf (decision procedure for univariate real-closed-field sentences, depends on hex-real-roots + hex-real-roots-mathlib + hex-poly-z + hex-poly-z-mathlib + Mathlib)

A Lean tactic, `rcf`, deciding the univariate fragment of
real-closed-field arithmetic: Boolean combinations of polynomial
(in)equalities in one real variable under a single quantifier over
`ℝ` or over a half-open dyadic interval. For an in-fragment sentence
the compiled builder constructs a squarefree carrier, isolates its
roots, and must return a verdict. Builder failure has a separate
`Except`/`Option` channel and is never reported as `false`. Every
`true` verdict is accompanied by a certificate which a small kernel
checker turns into a proof. A `false` verdict is diagnostic only: the
tactic never proves a negation, and no theorem turns `false` into a
proof.

For a false universal sentence the diagnostic names a cell on which
the body is false. For a false existential there is no single
counterexample witness; the diagnostic instead reports that every
relevant cell was checked and found false. Operational totality of the
compiled builder follows from the squarefree carrier and
`isolate?_isSome`, together with the structurally fuel-bounded
separation pass, from
[hex-real-roots-mathlib](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md).
It is not exposed
as a kernel-side completeness theorem for false verdicts.

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
  half-open isolation convention. The error message shows valid
  rewrites, including the empty/reversed-interval cases:
  `∀ x ∈ Set.Icc a b, φ` is
  `(a ≤ b → φ(a)) ∧ ∀ x ∈ Set.Ioc a b, φ`, and
  `∃ x ∈ Set.Icc a b, φ` is
  `a ≤ b ∧ (φ(a) ∨ ∃ x ∈ Set.Ioc a b, φ)`;
  `∀ x ∈ Set.Ioo a b, φ` is
  `∀ x ∈ Set.Ioc a b, x ≠ b → φ`, and
  `∃ x ∈ Set.Ioo a b, φ` is
  `∃ x ∈ Set.Ioc a b, φ ∧ x ≠ b`. The added `x ≠ b` remains a
  polynomial atom after denominator clearing.
- **Sentences that are false.** `decide` returns `some false` and the
  tactic fails. A false universal reports a cell on which the body is
  false (a concrete dyadic test point, or an isolating interval for a
  root cell). A false existential reports that no relevant cell
  satisfies the body.

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
a kernel proof

```lean
Sentence.toProp sentence ↔ goal
```

and the tactic uses the forward direction after checking the
sentence. This is propositional transport, not definitional equality:
normalising `s ⊳ t` to `(s - t) ⊳ 0`, clearing denominators, and
relating `ZPoly` evaluation to the original expression all require
proved equivalences.

## Algorithm

1. **Reify** the goal to a `Sentence`. Refuse anything out of
   fragment. Normalisation records the positive/nonzero scalar facts
   used when clearing denominators, and produces the equivalence with
   the original goal described above.

2. **Collect** the atom polynomials. Constant atoms (degree ≤ 0,
   including the zero polynomial) are evaluated to `tt`/`ff` by the
   decision pipeline and never reach the decomposition. The reifier
   may perform the same fold as an optimisation, but `decide` and
   `check` must also handle arbitrary directly constructed
   `Sentence`s containing constant atoms.

3. **Handle empty bounded domains.** Before any cell reasoning, compare
   the dyadic endpoints. If `a < b` is false, `(a,b]` is empty:
   `forallIoc` returns `true` and `existsIoc` returns `false`. Every
   later bounded-domain argument therefore has the explicit hypothesis
   `a < b`.

4. **Build and certify the carrier.** Let
   `Q := ∏ᵢ pᵢ` over the nonconstant atom polynomials and let the
   compiled builder choose `P := Hex.ZPoly.squareFreeCore Q`. The
   runtime uses the existing square-free-core implementation, but the
   kernel checker does not recompute it. Instead the certificate
   supplies polynomials `R`, `S` and nonzero integers `k`, `d` with

   ```text
   Q = scale k (P * R)
   scale d (derivative Q) = R * S.
   ```

   The checker derives the atom list from `s`, verifies that these
   atoms have positive degree, and recomputes `Q`; the certificate
   cannot choose a different product. It also checks that `Q` has
   positive degree, `R ≠ 0`, and `k,d ≠ 0`. A replay certificate for
   `P` proves that it is nonzero and
   squarefree. The two identities then prove that the real roots of
   `P` are exactly the real roots of `Q`: the first inclusion is
   immediate, and the converse is the standard squarefree-factor
   lemma for `Q = P*R` with `R ∣ Q'`. Since `Q` is the atom product,
   these are exactly the union of the atom root sets.

   Run `Hex.isolate? P`; the compiled builder knows this succeeds from
   the squarefreeness theorem. If there are no nonconstant atoms, do
   not construct a carrier: the decomposition is the single cell `ℝ`
   and the sign matrix is the already-folded constant formula.

5. **Separate.** Scan consecutive isolations in order. Already-strict
   pairs are left unchanged. For a touching pair, repeatedly apply the
   replay-based `Separation.refine1?` once to **both** intervals until
   `upperᵢ < lowerᵢ₊₁`. This helper reads variation differences from the
   cached generalized replay chain; it cannot use `RealRootIsolation.refine1With`,
   whose types are tied to the executable `ZPoly.sturmChain`. The pair walk is
   structurally fuel-bounded by the
   maximum of the two `refineTo` bounds

   ```text
   (ceilLog2Dyadic initialWidth + sepPrec P).toNat + 1.
   ```

   At that bound both widths are at most `2^(-sepPrec P)`, and the
   separation theorem forces a strict gap; honest isolations therefore
   cannot exhaust the fuel while still touching. Refining a later pair
   only shrinks its intervals and cannot destroy an earlier strict gap.
   This retains a structural termination argument without paying the
   worst-case separation precision for every already-separated root.
   The kernel certificate checks only the emitted strict dyadic gaps;
   it does not evaluate `sepPrec` or certify interval widths.

   Each of the two bounded endpoints is compared with every carrier
   root. For an isolation `I = (l,u]`, if `e ≤ l`, the root is greater
   than `e`; if `u < e`, it is less. In the remaining case
   `l < e ≤ u`, compute the literal carrier-chain count on `(l,e]`,
   which must be `0` or `1`. Count `0` means the root is greater than
   `e`. Count `1` means the root is at most `e`; exact evaluation of
   `P(e)` distinguishes equality from strict inequality.
   `Sturm.sturm_half_open` has no endpoint-nonroot premise, so this is
   valid even when the dyadic lower endpoint `l` is itself a root.

6. **Build cells.** With isolations `I₁ < … < I_k` (roots
   `r₁ < … < r_k`):

   ```
   Cell = tailLeft            -- semantic (−∞, r₁),   point lower₁ − 1
        | root i              -- semantic {rᵢ},       data Iᵢ
        | gap i               -- semantic (rᵢ, rᵢ₊₁), test point in
                              --   (upperᵢ, lowerᵢ₊₁), which step 5
                              --   made nonempty
        | tailRight           -- semantic (rₖ, +∞),   point upperₖ + 1
   ```

   Use the dyadic midpoint of `upperᵢ` and `lowerᵢ₊₁` for a gap.
   With no roots, use the sole open cell `ℝ` and test point `0`.
   The semantic cells partition `ℝ`. Every `pⱼ` is sign-constant on
   each open cell: a sign change would put a root of `pⱼ`, hence of
   `P`, strictly between consecutive roots of `P`.

7. **Prepare common-root packages.** Do the expensive work once per
   distinct nonconstant atom, not once per root cell. For each `pⱼ`,
   the builder computes a rational gcd representative `gⱼ` and emits
   `aⱼ`, `bⱼ`, `uⱼ`, `vⱼ` and a nonzero integer `cⱼ` satisfying

   ```text
   pⱼ = gⱼ * aⱼ
   P  = gⱼ * bⱼ
   uⱼ * pⱼ + vⱼ * P = scale cⱼ gⱼ.
   ```

   These multiplication-checkable identities prove that the real
   roots of `gⱼ` are exactly the common real roots of `pⱼ` and `P`.
   No executable `gcdZ` API is assumed. A nonzero constant `gⱼ` has
   count zero; each distinct nonconstant `gⱼ` carries one cached
   generalized Sturm replay used for all carrier roots.

8. **Sign matrix.** For each cell and each atom polynomial `pⱼ`:
   - Open cells: exact Horner evaluation at the cell's dyadic test
     point. The value is nonzero (the test point is in no isolation,
     and roots of `pⱼ` are roots of `P`). A zero value would refute
     the library's own invariants, and the driver fails rather than
     guesses.
   - Root cells: whether `pⱼ(rᵢ) = 0` is exactly
     the generalized Sturm count of `gⱼ` on `Iᵢ` being `1`.
     Since `gⱼ ∣ P`, the interval contains at most one such root; the
     common-root identities make that root exist exactly when
     `pⱼ(rᵢ) = 0`. When `pⱼ(rᵢ) ≠ 0`, its sign at `rᵢ` equals its sign
     on either adjacent open cell. The two adjacent signs agree,
     because otherwise `pⱼ` would have another root before the next
     carrier root.

9. **Evaluate.** Substitute each cell's signs into the atoms, fold
   the Boolean structure: one truth value per cell.

10. **Quantify.**

    - `forallReal`: every cell true. `existsReal`: some cell true.
    - `forallIoc a b`: every cell whose semantics meets `(a, b]`
      true; `existsIoc`: some such cell true. Under the step-3
      hypothesis `a < b`, meeting the domain is decided exactly:
      a root cell meets iff `a < rᵢ ∧ rᵢ ≤ b`; a gap meets iff
      `rᵢ < b ∧ a < rᵢ₊₁`; `tailLeft` iff `a < r₁`; and `tailRight`
      iff `rₖ < b`. The endpoint comparisons from step 5 decide every
      conjunct. With no roots, the single cell `ℝ` meets `(a,b]`.

11. **Reflect.** A successful kernel replay gives
    `Sentence.toProp s`; the reifier's equivalence transports that
    proof to the original goal. A false result produces the diagnostic
    described above.

## Kernel replay

The tactic does not ask the kernel to evaluate the compiled decision
pipeline: re-running the search (bisection, gcds, refinement) inside
the kernel would be far slower. Following the compiled-prep /
kernel-verify pattern of the `factor_poly` / `irreducibility` tactics
(hex-berlekamp), the tactic runs the search compiled, embeds a
`Certificate`, and emits a proof of
`Sentence.check s cert = true` by kernel reduction.

### Generalized Sturm replay

The existing `SturmChainCert` identifies a supplied array with the
library's executable pseudo-remainder chain, so its checker recomputes
`spem` and primitive parts. RCF instead needs a generalized,
multiplication-only replay shared by the carrier and the atom gcds.
For a positive-degree `f`, a replay contains

```lean
structure SturmStep where
  leftScale  : Int
  quotient   : ZPoly
  rightScale : Int

structure SturmReplay where
  chain      : Array ZPoly
  derivScale : Int
  steps      : Array SturmStep
```

Writing the literal chain as `[f, s₁, ..., sₙ]`, the Boolean checker
verifies with `DensePoly.beqCoeffs`:

- the chain has at least two entries, its head is `f`, every entry is
  nonzero, degrees strictly decrease, and `sₙ` is a nonzero constant;
- `derivScale > 0` and
  `derivative f = scale derivScale s₁`;
- `steps.size + 2 = chain.size`; and for each step `i`, both scales
  are positive and

  ```text
  scale leftScale sᵢ = quotient * sᵢ₊₁ - scale rightScale sᵢ₊₂.
  ```

The recurrence propagates coprimality backwards from the terminal
constant, gives alternating flanks at every interior zero, and the
positive derivative seed gives the root flank. Consequently the
literal cast chain satisfies `Sturm.IsSturmChain`; in particular `f`
is squarefree. Its interval count is the variation difference of
this literal chain, not a call to `sturmCount f`, and its total count
is the corresponding `−∞/+∞` difference. The proof factors through
`Sturm.sturm_half_open` and `Sturm.sturm_line`. Constants are handled
separately because the interval-count theorem requires positive
degree.

The compiled builder obtains the witnesses by instrumenting the existing
sign-managed pseudo-remainder loop. During division of `prev` by `cur` it
maintains

```text
scale A prev = Q * cur + r.
```

One `spemStep` with positive multiplier `a`, cancelled leading monomial
`monomial k b`, and new remainder `r'` updates
`A := a*A`, `Q := scale a Q + monomial k b`, and `r := r'`. At a nonzero
stopping remainder it emits `next := -primitivePart r` and
`rightScale := content r`, turning the invariant into exactly the checked
subtractive recurrence. The builder starts the chain at the literal input
`f`; only its derivative is primitive-normalized, with `derivScale` equal to
the derivative content. Fuel exhaustion and a zero remainder before a
constant terminal entry are rejected, and the public builder retains a raw
candidate only after `SturmReplay.check` accepts it.

Three existing private lemmas in
`HexRealRootsMathlib/ChainCorrespond.lean` transfer directly and should
be exported: `coprime_step_rev`, `flank_of_key`, and
`eval_ne_zero_of_isCoprime`. The current
`isSturmChain_of_seeds` does **not** transfer directly: its conclusion
and four supporting inductions are tied to the executable `chainList`.
The shared foundation must instead prove one abstract-list theorem from
a per-triple recurrence hypothesis, terminal-constant hypothesis, and
degree/nonzero hypotheses. Both the executable pseudo-remainder chain
and the RCF literal array then instantiate that theorem. The public
`sturmVarAt_eq` and generalized/exported versions of the currently
private `sturmVarNegInf_eq` and `sturmVarPosInf_eq` connect executable
variation reads to `Sturm.sturmVar` at finite endpoints and infinity.

### Certificate contents

The certificate contains:

- when needed, the carrier `P`, its generalized replay, and the
  carrier identities from algorithm step 4; the atom list and product
  `Q` are recomputed from `s`, not trusted from certificate data;
- isolating intervals whose `count_one`, ordering, and completeness
  fields are expressed using the literal carrier replay, plus the
  strict-gap checks;
- all endpoint classifications, open-cell test points and their exact
  polynomial evaluations, per-cell formula values, and the quantified
  result; `check` re-evaluates these fields and derives every root-cell
  sign from a `gⱼ` count (zero) or an adjacent open-cell sign
  (nonzero), rather than trusting a supplied sign;
- one common-root package per distinct nonconstant atom, with its
  three identities and at most one generalized replay for its `gⱼ`.

These are generalized isolation records: they must not be presented
as the current `RealRootIsolation P` / `RealRootIsolations P` types,
whose fields are definitionally tied to the executable `sturmCount P`
and `sturmChain P`. Their semantic theorems parallel
`RealRootIsolation.exists_unique_root` and
`RealRootIsolations.isolates`, but consume the literal replay counts,
`Squarefree (toPolyℝ P)`, and `P ≠ 0`; they do not require the
executable predicate `Hex.ZPoly.SquareFreeRat P`.

`check` performs coefficient equality, multiplication/subtraction,
integer scaling, formal differentiation, degree and leading-coefficient
reads, dyadic comparison, Horner evaluation, sign variation, and
Boolean folding only. It performs no pseudo-division, primitive-part
normalisation, gcd, square-free-core computation, root search, or
refinement. The kernel reduces the specification implementation of
`DensePoly.scale`; compiled acceleration is irrelevant to replay
soundness.

```lean
theorem check_sound (s : Sentence) (cert : Certificate) :
    check s cert = true → s.toProp
```

`decide : Sentence → Option Bool` is a convenience wrapper used by
conformance and the external oracle. Internally, the builder returns
either a diagnostic false result or a candidate true certificate.
`decide` returns `some false` for the former; for the latter it runs
`check s cert` and returns `some true` only when that check succeeds,
otherwise `none`. An internal builder or certificate failure therefore
cannot pass a fixture expecting either verdict. The required one-way
connections are

```lean
theorem decide_eq_some_true_imp_exists_cert :
    decide s = some true → ∃ cert, check s cert = true

theorem decide_sound (s : Sentence) :
    decide s = some true → s.toProp
```

The reverse implication would assert completeness of this particular
builder from the mere existence of some certificate and is neither
needed by the tactic nor part of this contract. The trust boundary is
Lean's kernel: it checks `check_sound`, the reduction proof
`check s cert = true`, and the reifier-produced equivalence with the
original goal. No unverified result of the compiled builder or reifier
is accepted as a proof.

## Soundness theorem structure

`check_sound` factors exactly along the algorithm:

- **Chain, carrier, and count replay.** The generalized recurrence
  proves `Sturm.IsSturmChain` for each literal chain. The carrier
  identities prove that `P` is nonzero and squarefree and that its
  real roots are exactly the union of the atom roots. Literal
  variation differences are therefore the required root counts.
- **Cell partition.** The generalized isolation theorem proves that
  every carrier root occurs in exactly one certified interval. Strict
  gaps and the endpoint-comparison theorem then make the root and
  open cells a partition of `ℝ`, with exact intersection tests for
  `(a,b]`. Empty and reversed bounded intervals were discharged
  before this step.
- **Sign matrix.** On open cells: sign constancy from
  root-containment (roots of `pⱼ` are roots of `P`) plus the exact
  test-point evaluation. On root cells: the cached `gⱼ` count
  argument of step 8. The divisibility identities give that every
  root of `gⱼ` is a common root of `pⱼ` and `P`; the scaled Bézout
  identity gives the converse; and the literal `gⱼ` replay (or the
  nonzero-constant case) justifies its count.
- **Boolean and quantifier steps.** The per-cell fold computes
  `Formula.toProp` at every point of the cell (signs determine
  atoms), and the quantifier step lifts cell-wise truth to `ℝ` or to
  `(a, b]` because the cells partition and the classification of
  step 10 is exact.

No completeness theorem is stated for `decide` (that `some false`
implies the negation): the tactic never uses a false verdict as a proof,
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

- `HexRCF/Language.lean`: `Atom`, `Formula`, `Sentence`, `toProp`;
  `HexRCF/LanguageTests.lean`: executable language-semantics tests.
- `HexRCF/SturmReplay.lean`: generalized multiplication-only chain
  replay and literal root counts.
- `HexRCF/SturmBuilder.lean`: compiled pseudo-remainder instrumentation that
  emits replay witnesses and retains only checker-approved candidates;
  `HexRCF/SturmBuilderTests.lean`: valid, malformed, nonprimitive, and
  nonsquarefree regressions.
- `HexRCF/Carrier.lean`: deterministic nonconstant-atom collection, the
  multiplication-checkable carrier certificate, and root-set soundness;
  `HexRCF/CarrierTests.lean`: constant filtering, genuine repeated-factor,
  dropped-root, and other tampered-carrier regressions.
- `HexRCF/Isolations.lean`: the raw generalized isolation checker and its
  bridge to literal isolation semantics; `HexRCF/IsolationsTests.lean`:
  count, order, completeness, and no-real-root regressions.
- `HexRCF/Certificate.lean`: `Certificate`, `check`, `decide`.
- `HexRCF/Separation.lean`: replay-based strict-separation refinement,
  strict-gap checking, and endpoint classification for bounded sentences;
  `HexRCF/SeparationTests.lean`: midpoint ownership, close-root, scan,
  malformed-input, and endpoint regressions.
- `HexRCF/Cells.lean`: semantic and executable cell construction.
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
  - Equal and reversed dyadic endpoints for both bounded quantifiers,
    using constant/no-root bodies and nonconstant polynomial bodies;
    these assert that the empty-domain universal is true and the
    empty-domain existential is false.
  - Generalized-replay rejection tests for a wrong head, derivative
    scale, recurrence scale/sign, quotient, degree order, terminal
    constant, isolation count, and carrier/common-root identity.
  - Fall-through, asserted to fail: the two-variable example, a
    `sin` example, a division example, an `Icc` example, and one
    false universal plus a false existential
    (`∃ x : ℝ, x² + 1 = 0`), checking their distinct diagnostics.
- *ci* (external oracle, `python-flint`, mode `if_available`): 30
  sentences over random small-coefficient
  polynomials from a deterministic seed, serialised with expected
  verdicts. `scripts/oracle/rcf_flint.py` uses python-flint as required
  by [testing.md](../testing.md). It independently forms and
  squarefrees the atom product. Following
  `scripts/oracle/realroots_flint.py`, its exact tier extracts rational
  roots from `fmpz_poly.factor()` and compares them with `Fraction`;
  its ball tier uses `fmpz_poly.complex_roots()`, accepting a real root
  only when FLINT gives its imaginary part as exact zero. Precision
  escalation separates real-part enclosures, proves nonreal imaginary
  balls away from zero, and resolves ordering/cell membership; it does
  not attempt to infer realness merely from a narrowing ball. Open
  samples are evaluated exactly over `Fraction`; FLINT gcd/root
  matching and sign-definite Arb evaluation handle root cells; dyadic
  endpoints are exact. The oracle consumes only the sentence AST,
  never Lean's carrier, certificate, cells, or signs. Missing
  python-flint is `SKIP`; unresolved enclosure ambiguity after the
  finite precision ladder is a hard failure. Fixtures require
  `decide = some expected`, so builder failure never passes a false
  case. They cover every comparison and Boolean form, true and false
  quantifiers, constants, no-root cases, shared and endpoint roots,
  close roots, and equal/reversed intervals. CI cases stay around
  degrees 8–12; the degree-50 stress case remains local. Phase-3
  wiring adds the `hex-rcf` assignment to `SPEC/testing.md`, the
  conformance/oracle block to `libraries.yml`, and one tuple to
  `scripts/ci/run_oracles.sh`; it adds no job, matrix, workflow, or
  dependency beyond the existing python-flint install.
- *local*: Mignotte-cluster atoms and degree-50 sentences, timing
  the pipeline where the isolation layer is under stress.

## Complexity contract

For a sentence with `m` atoms of degrees summing to `n`:

- Reification: linear in the goal.
- `P`: one product and one `squareFreeCore`, `deg P ≤ n`.
- Isolation: hex-real-roots' contract at degree `deg P`.
- Separation refinement: an adaptive, structurally fuel-bounded pass
  over touching adjacent pairs, reusing the carrier chain; already
  strict pairs pay no bisection cost and `k ≤ n` roots.
- Common-root preparation: one gcd and one generalized chain per
  distinct nonconstant `gⱼ`, reused across all `k` root cells.
- Sign matrix: `k·m` literal variation-count reads plus
  `(k + 1)·m` open-cell evaluations; no per-root gcd computation.
- Certificate replay in the kernel: one pass over the certificate,
  using polynomial multiplication/subtraction, evaluation, and
  comparison only.

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
