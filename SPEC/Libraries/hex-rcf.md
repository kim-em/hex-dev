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
   including the zero polynomial) never contribute carrier boundaries or
   common-root packages. Mixed formulas cache their constant signs alongside
   nonconstant signs in each cell row; a constant-only formula is folded once
   without constructing a carrier. The reifier may perform the same fold as
   an optimisation, but `decide` and `check` must also handle arbitrary
   directly constructed `Sentence`s containing constant atoms.

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

6. **Build cells.** With `k` isolations `I₀ < … < Iₖ₋₁` (roots
   `r₀ < … < rₖ₋₁`), use the size-indexed representation

   ```lean
   inductive Cell (k : Nat)
     | open (cut : Fin (k + 1))
     | root (i : Fin k)
   ```

   Open cut `0` is the left tail, cut `k` is the right tail, and an
   interior cut `j` is `(rⱼ₋₁,rⱼ)`. `Cell.all` enumerates these cells
   left-to-right with rank `2*j` for open cuts and `2*i+1` for roots.
   `RootModel` packages the unique root of each checked isolation, their
   strict monotonicity, and completeness. `Cell.Sem` interprets the indexed
   representation, and `Cell.existsUnique_mem` states the partition theorem.

   `IsolationCert.openPoint` uses the dyadic midpoint of `upperᵢ` and
   `lowerᵢ₊₁` for an interior cut, `lower₀ - 1` and `upperₖ₋₁ + 1` for
   the tails, and `0` for the sole no-root cell. `Cell.openPoint_mem`
   certifies sample membership, `Cell.open_not_root` excludes carrier roots
   from every open cell, and `Cell.isPreconnected_open` supplies the interval
   topology needed by sign constancy. Every `pⱼ` is sign-constant on
   each open cell: a sign change would put a root of `pⱼ`, hence of
   `P`, strictly between consecutive roots of `P`.

   For root-cell transfer, `RootModel.leftSpan` is the interval from the open
   cell immediately left of root `i` through that root. Its preconnectedness,
   open-sample and root membership lemmas, together with
   `RootModel.root_eq_of_mem_leftSpan`, show that the only carrier root in the
   span is root `i` itself.

7. **Prepare common-root packages.** Do the expensive work once per
   distinct nonconstant atom, not once per root cell. For each `pⱼ`,
   the builder computes a rational gcd representative `gⱼ` and emits a
   `CommonRootCert` containing `gcd`, `atomFactor`, `carrierFactor`,
   `atomCoeff`, `carrierCoeff`, a nonzero integer `scale`, and an optional
   generalized replay. Its checker receives `pⱼ` and `P` externally and
   verifies

   ```text
   pⱼ = gcd * atomFactor
   P  = gcd * carrierFactor
   atomCoeff * pⱼ + carrierCoeff * P = scale scale gcd.
   ```

   These multiplication-checkable identities prove `CommonRootCert.isRoot_iff`:
   the real roots of `gⱼ` are exactly the common real roots of `pⱼ` and
   `P`. No executable `gcdZ` API is assumed. The `none` replay branch is
   accepted exactly when `gⱼ` has dense size one, so it is a nonzero
   constant and has no roots. The `some replay` branch requires positive
   degree and checks the replay against `gⱼ`.

   `CommonRootCert.hasRoot` returns `false` for the constant branch and tests
   whether the cached replay count is one otherwise. Under the independently
   checked carrier, strict isolations, and common-root package,
   `CommonRootCert.hasRoot_iff` proves that this Boolean is true exactly when
   `pⱼ` vanishes at any supplied carrier root in the checked isolation;
   `hasRoot_model_iff` specializes it to the canonical `RootModel` root. The
   underlying `count_eq_one_iff` uses divisibility to bound the `gⱼ` roots in
   a carrier isolation by its single `P` root. Thus one replay is shared by all
   carrier root cells for that distinct atom polynomial. Deduplication and alignment
   of these packages with the recomputed distinct atom-polynomial order are
   responsibilities of the step-8 sign-matrix checker, not trusted fields of
   an individual package.

   Compiled preparation computes the gcd and Bézout coefficients over
   `ℚ[x]`, converts the exact factor quotients back to `ℤ[x]`, and clears one
   positive common denominator across both Bézout coefficients and the
   rational unit relating the executable gcd to its primitive integer
   representative. `buildCommonRoots?` traverses exactly the
   first-occurrence-preserving `dedupPolys s.polys` order and retains every
   candidate only after `CommonRootCert.check` accepts it.

8. **Sign matrix.** For each cell and each atom polynomial `pⱼ`:
   The checker first coefficient-deduplicates the recomputed nonconstant atom
   order and checks exactly one positional common-root package per result;
   missing, extra, swapped, or malformed packages fail. It also deduplicates
   all formula polynomials and materializes one option-valued sign row per
   cell, so repeated atom occurrences reuse the same arithmetic result.
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
     on either adjacent open cell. The executable checker canonically uses
     the open cell immediately to the left, which exists for every root.
     Where both adjacent cells exist, their signs agree because otherwise
     `pⱼ` would have another root before the next carrier root.

9. **Evaluate.** Look up each atom in the cached sign row and fold the Boolean
   structure to one truth value per cell. All children are evaluated before a
   connective is combined, so a missing sign returns `none` even when ordinary
   Boolean short-circuiting could already determine the truth value. Under the
   checked alignment and carrier hypotheses, the sign and formula evaluators
   are total and their returned Boolean is equivalent to `Formula.toProp` at
   every point of the semantic cell.

10. **Quantify.**

    - `forallReal`: every cell true. `existsReal`: some cell true.
    - `forallIoc a b`: every cell whose semantics meets `(a, b]`
      true; `existsIoc`: some such cell true. Under the step-3
      hypothesis `a < b`, meeting the domain is decided exactly:
      a root cell meets iff `a < rᵢ ∧ rᵢ ≤ b`; a gap meets iff
      `rᵢ < b ∧ a < rᵢ₊₁`; open cut `0` iff `a < r₀`; and open
      cut `k` iff `rₖ₋₁ < b`. The endpoint comparisons from step 5
      decide every conjunct. With no roots, the single cell `ℝ` meets
      `(a,b]`.

      Executably, `IocCmps k` stores size-indexed lower and upper
      `RootCmp` vectors. `IocCmps.check` replays every claim, and
      `Cell.meetsIoc` implements the table above. Under `a < b`,
      `Cell.meetsIoc_iff_of_check` proves that the Boolean is true exactly
      when some semantic point of the cell lies in `Set.Ioc a b`. Thus a
      lower-endpoint equality excludes a root cell while an upper-endpoint
      equality includes it. `Cell.meetsIocOn` adds the step-3 guard and is
      false for every cell when `a ≥ b`; `Cell.meetsIocOn_iff_of_check` is
      the corresponding all-endpoint-order theorem.

    The executable quantifier folds are strict in their option-valued cell
    results: Boolean `false`/`true` never short-circuits a later malformed
    active cell. Bounded folds filter by the checked `meetsIocOn` predicate
    first, so failures in irrelevant cells do not poison the result, while a
    failure in any relevant cell returns `none`. Empty universal and
    existential folds have the usual identities `true` and `false`.

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
`Certificate.check s cert = true` by kernel reduction.

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

`Certificate` has four constructors matching the disjoint replay cases:
`emptyIoc`, `constants`, `noRoots`, and `cells`. The no-root branch carries a
checked carrier and an empty strict isolation set. The positive-root branch
additionally carries the sign-matrix packages and an optional size-indexed
`IocCmps`: real sentences require `none`, while bounded sentences require a
checked `some`. Thus endpoint evidence cannot be silently ignored or omitted.

Internally, `Certificate.replay?` returns `Option Bool`: `none` means malformed
or shape-mismatched evidence, while `some false` is a valid diagnostic verdict.
`Certificate.check` accepts exactly `some true`. Empty or reversed bounded
domains are handled before all certificate data, so their universal and
existential results are respectively `some true` and `some false` even when no
decomposition exists. Every nonempty branch rejects data meant for a different
shape.

The certificate contains:

- when needed, the carrier `P`, its generalized replay, and the
  carrier identities from algorithm step 4; the atom list and product
  `Q` are recomputed from `s`, not trusted from certificate data;
- isolating intervals whose `count_one`, ordering, and completeness
  fields are expressed using the literal carrier replay, plus the
  strict-gap checks;
- all endpoint classifications and the quantified result; open-cell test
  points are deterministic, and exact polynomial signs and per-cell formula
  values are recomputed rather than stored as redundant claims. `check`
  derives every root-cell sign from a `gⱼ` count (zero) or the canonical
  left-adjacent open-cell sign (nonzero), rather than trusting a supplied sign;
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
    Certificate.check s cert = true → s.toProp
```

`decide : Sentence → Option Bool` is a convenience wrapper used by
conformance and the external oracle. Internally, the builder returns
either a diagnostic false result or a candidate true certificate.
`decide` returns `some false` for the former; for the latter it runs
`Certificate.check s cert` and returns `some true` only when that check succeeds,
otherwise `none`. An internal builder or certificate failure therefore
cannot pass a fixture expecting either verdict. The required one-way
connections are

```lean
theorem decide_eq_some_true_imp_exists_cert :
    decide s = some true → ∃ cert, Certificate.check s cert = true

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

- `HexRCF/Syntax.lean`: Mathlib-free `Cmp`, `Atom`, `Formula`, `Sentence`, and
  their structural polynomial traversals; `HexRCF/Language.lean`: real-valued
  `toProp` semantics;
  `HexRCF/LanguageTests.lean`: executable language-semantics tests.
- `HexRCF/SturmCheck.lean`: Mathlib-free generalized multiplication-only
  replay data, executable validation, and literal root counts;
  `HexRCF/SturmReplay.lean`: Mathlib-facing replay soundness and root-count
  correspondence.
- `HexRCF/SturmBuilder.lean`: compiled pseudo-remainder instrumentation that
  emits replay witnesses and retains only checker-approved candidates;
  `HexRCF/SturmBuilderTests.lean`: valid, malformed, nonprimitive, and
  nonsquarefree regressions.
- `HexRCF/CarrierCheck.lean`: Mathlib-free multiplication-checkable carrier
  certificates and Boolean validation; `HexRCF/Carrier.lean`: squarefreeness
  and root-set soundness;
  `HexRCF/CarrierTests.lean`: constant filtering, genuine repeated-factor,
  dropped-root, and other tampered-carrier regressions.
- `HexRCF/IsolationCheck.lean`: Mathlib-free raw generalized isolation data,
  checks, and ordering/count consequences; `HexRCF/Isolations.lean`: the
  bridge to literal isolation and real-root semantics;
  `HexRCF/IsolationsTests.lean`: count, order, completeness, and no-real-root
  regressions.
- `HexRCF/Certificate.lean`: strict option folds, the four `Certificate`
  branches, three-valued replay, and `check`; `HexRCF/CertificateTests.lean`:
  all quantifiers, empty/reversed domains, constants, zero/single/multiple-root
  decompositions, endpoint equality, and malformed nested evidence.
- `HexRCF/Builder.lean`: exact rational conversion and checker-retained
  compiled carrier and deduplicated, aligned common-root construction;
  `HexRCF/BuilderTests.lean`: signed-content, repeated-factor, rational-scale,
  common-root alignment, and failure regressions.
- `HexRCF/DecisionCheck.lean`: Mathlib-free compiled root isolation, strict
  separation, endpoint classification, sign-matrix and certificate assembly,
  retained diagnostic build results, and `decide`;
  `HexRCF/Decision.lean`: the public one-way soundness theorem;
  `HexRCF/DecisionTests.lean`: all four certificate branches and quantifiers,
  half-open endpoint ownership, multiple/repeated/shared roots, helper failure,
  and output-check regressions.
- `HexRCF/SeparationCheck.lean`: Mathlib-free strict-gap checks, endpoint
  classification, and replay-based separation refinement;
  `HexRCF/Separation.lean`: real-root ordering and classifier semantics;
  `HexRCF/SeparationTests.lean`: midpoint ownership, close-root, scan,
  malformed-input, and endpoint regressions.
- `HexRCF/CellsCheck.lean`: Mathlib-free size-indexed cells, exact dyadic
  samples, endpoint-comparison checks, and bounded-domain relevance;
  `HexRCF/Cells.lean`: checked root models, semantic partition, canonical
  left-root spans, and exact `Ioc` intersection;
  `HexRCF/CellsTests.lean`: enumeration,
  zero/singleton/multiple-root samples, endpoint equality/order guards,
  relevance tables, and malformed lower/upper claim regressions.
- `HexRCF/CommonRootCheck.lean`: Mathlib-free multiplication-checkable
  common-root packages, replay branches, and cached interval queries;
  `HexRCF/CommonRoot.lean`: exact common-root and root-cell semantics;
  `HexRCF/CommonRootTests.lean`: shared-factor, coprime, equal-polynomial, and
  tampered-evidence regressions.
- `HexRCF/SignMatrixCheck.lean`: Mathlib-free three-way exact signs,
  coefficient-equality atom deduplication and common-package alignment,
  guarded open/root-cell evaluation, sign-row caching, and Boolean replay;
  `HexRCF/SignMatrix.lean`: real-polynomial sign, root-cell, and full formula
  reflection semantics;
  `HexRCF/SignMatrixTests.lean`: exhaustive comparisons/connectives,
  zero/singleton/multiple-root cells, shared roots, constants, deduplication,
  and malformed-alignment regressions.
- `HexRCF/Soundness.lean`: strict-fold reflection, quantified cell lifting,
  the four replay factors, and `check_sound`.
- `HexRCF/Reify.lean`: `Qq`/`MetaM` reification, normalisation,
  fall-through messages; `HexRCF/ReifyTests.lean`: checked tactic examples,
  false-sentence diagnostics, and out-of-fragment rejection tests.
- `HexRCF/Tactic.lean`: the `rcf` front end.
- `conformance/HexRCF/{Conformance,EmitFixtures}.lean`: conformance
  in the shared sub-project.

The public `HexRCF` umbrella imports only the supported implementation and
proof API. The `*Tests.lean` regression modules above are compiled through the
separate `HexReleaseTests` Lake target and are not re-exported to consumers.

## Phase-4 evidence tracks

HexRCF is a mixed library. `HexRCF.DecisionCheck` contains the complete
compiled search, certificate construction, replay, and `decide` path in a
mechanically checked import closure containing neither `Mathlib.*` nor
`HexRealRootsMathlib.*`. That track uses the ordinary Mathlib-free
`bench/HexRCF/Bench.lean` LeanBench executable. `by rcf` reification, proof
emission, and kernel checking remain Mathlib-facing and use build-only modules
below the explicit `libraries.yml` root `bench/HexRCF/ProofProbe/`.

The compiled track requires these stable parametric cases. Every ladder varies
only the named parameter, and fixture generation stays outside the timed
region. LeanBench's mandatory conformance hash is computed before its timer
stops; each target therefore returns a result whose structural hash has no
higher asymptotic order than the named operation, and each nonconstant hash
walk is included in the adjacent derivation. The adjacent registration
comments repeat these derivations.

| Case | Timed operation and controlled ladder | Declared textbook model |
| --- | --- | --- |
| `runDecisionCarrierDegree` | `decide` on one square-free product of `n` unit-separated linear factors; one atom and one Boolean node | `O(n⁴)` integer operations: `O(n)` active intervals over `O(n)` levels, each dominated by an `O(n²)` Möbius transform; other fixed-shape RCF phases are no worse on this family. |
| `runDedupRepeated` | `dedupPolys` on `u` repetitions of one fixed-degree polynomial | `O(u)`: after the first entry the seen set has fixed size one; the one-polynomial output has constant hash cost. |
| `runDedupDistinct` | `dedupPolys` on the first `u` entries of a committed fixed-degree, fixed-bit-width distinct-polynomial corpus | `O(u²)`: first-occurrence insertion scans a seen prefix of lengths `0 … u-1`; coefficient comparison cost is bounded by the corpus contract, and the `O(u)` structural output hash is lower-order. |
| `runCommonCoprime` | a strict batch of public `buildCommonRoot?` calls on the first `m` atoms in the committed fixed-degree coprime corpus against one fixed-degree carrier | `O(m)`: one bounded-size gcd, identity package, and checker call per atom; the required hash walks `m` bounded certificates. Distinct-order deduplication is excluded here and measured by `runDedupDistinct`. |
| `runCommonShared` | the same strict public-builder batch over `m` distinct fixed-degree scalar multiples sharing the carrier root | `O(m)`: carrier/atom degrees and coefficient-width range are bounded by the committed schedule, so each nonconstant-gcd package, checker call, and result-hash entry has bounded cost. |
| `runCommonRepeated` | the same strict public-builder batch over `m` repetitions of one fixed atom/carrier pair, deliberately without deduplication | `O(m)`: the public builder is invoked once per occurrence on an unchanged bounded-size pair, and the structural result hash is another linear pass. |
| `runSeparationDepth` | `Separation.separate?` at fixed carrier degree while coefficient height forces a dyadic close pair to depth `b` | There are `O(b)` exact-arithmetic operations, but their operands have `O(b)` bits. The wall-cost contract is `O(b M(b))`; the registration uses the quasi-linear multiplication proxy `b² ceilLog₂(b+1)` on a homogeneous multiprecision schedule, avoiding the immediate-`Int`/GMP seam. |
| `runReplayCells` | `Certificate.replay?` on prebuilt accepted `.cells` certificates for a unit-separated degree-`k` carrier with one atom, varying its `k` roots and `2k+1` cells | Isolation validation and `k` root-cell `hasRoot` checks take `O(k³)` exact operations. For `Pₖ = ∏_{j≤k}(x-j)`, primitive-PRS operand height is `B(k) = O(k² log k)`, so the wall-cost contract is `O(k³ M(B(k)))`; the registration uses the quasi-linear proxy `k⁵ ceilLog₂(k+1)²` on one multiprecision regime. |
| `runReplaySigns` | `Certificate.replay?` on prebuilt accepted `.cells` certificates with a fixed one-root carrier and `u` distinct fixed-width scalar multiples of its linear atom | `O(u²)` exact-arithmetic/list operations: sentence-product construction and the repeated-factor witness grow at most quadratically, while deduplication, aligned common-root lookup, sign-row construction, and formula lookup each scan prefixes of the `u` entries. |
| `runReplayFormula` | `Certificate.replay?` on prebuilt accepted `.cells` certificates with carrier, cell count, and atom multiset fixed while appending `s` literal `.tt`/`.ff` nodes by one fixed tree recipe | `O(s)`: the arithmetic payload is fixed, while the formula/polynomial discovery traversals and the strict option-valued fold visit each added literal/connective node a bounded number of times. |

The five manifest input-family dimensions map respectively to carrier
degree/root count, distinct versus repeated occurrences, common-root package
count, separation depth, and the three independent replay subladders (cells,
distinct sign entries, and formula occurrences). The fixed
quadratic/degree-10/degree-50 cases below do not participate in those
complexity verdicts.

The tactic track begins with same-module `Baseline − Baseline` and
`Degree50.Tactic − Degree50.Tactic` null controls, then uses matched
fresh-module variants for each fixed case:
`Baseline` (identical imports), `Reify` (reify-only checksum), `Input`
(reflected sentence literal), `Search` (the same input plus a meta checksum of
compiled certificate construction, emitting no proof), `Literal` (input plus
the pre-generated certificate), `Replay` (literal plus its kernel-checked
theorem), and `Tactic` (the source goal closed by `rcf`). An external runner
rotates fresh builds and reports both null calibrations followed by raw paired
deltas for reification, search, literal elaboration, replay, and the full
tactic. Six rounds balance which role builds first. Each null's signed deltas,
absolute and relative ranges, and median describe fresh-build noise only: they
are reported before the substantive pairs in artifact `config.order` and are
never subtracted, promoted to a significance test, or used to alter the fixed
tactic budgets. A substantive delta is noise-sized only against a null with a
comparable total build magnitude, or when its relative spread agrees with both
controls; otherwise the sweep leaves it unresolved. `Search − Input` is
phase-attribution evidence only; the matching LeanBench target supplies the
scientific asymptotic verdict, and the report neither substitutes nor adds the
two. The headline report records source hashes, commit/toolchain/host/load
state, raw samples, artifact sizes, timeout cleanup, and the theorem's axiom
set, and refuses release claims from a dirty or busy host.

The committed implementation lives under `bench/HexRCF/ProofProbe/`.
`Support.lean` owns the fixed source and reflected cases plus the precompiled
reify, search, and replay elaborators; `Generated.lean` owns the three
pre-generated certificate macros. The generator replaces exactly the
certificate's dyadic-interval order-proof omissions with `by decide` and
rejects any other pretty-printer omission, so the committed macro source is
independently rebuildable. All measured modules import the same generated
support module and no measured module imports another measured module.

There is one shared `Baseline` and six measured modules under each of
`Quadratic/`, `Degree10/`, and `Degree50/`. The report contains seventeen
pairs: the baseline and degree-50-tactic null controls first, then these five
pairs for each of the three cases:

| Report component | Reference | Candidate |
| --- | --- | --- |
| reification | `Baseline` | `<Case>.Reify` |
| compiled-search attribution | `<Case>.Input` | `<Case>.Search` |
| literal elaboration | `<Case>.Input` | `<Case>.Literal` |
| kernel replay | `<Case>.Literal` | `<Case>.Replay` |
| end-to-end tactic | `Baseline` | `<Case>.Tactic` |

`HexRCFProofProbe` is the reduced structural CI target: it builds the shared
support, reifies all three source goals, checks every committed literal against
the accepted checker and the builder-output hash, and builds the quadratic
matrix. Each Search module repeats its Input module's reflected declaration
before running the search command, so `Search - Input` does not subtract work
absent from the candidate. `HexRCFProofProbeScientific` owns the degree-10 and
degree-50 measured modules without adding them to routine CI. Both are
build-only Lake libraries; there is no proof-probe executable or in-process
clock. The complete external sweep is:

```bash
python3 scripts/bench/hexrcf_proof_sweep.py --samples 6
```

Only `Replay` and `Tactic` print an axiom report, fixed to
`[propext, Classical.choice, Quot.sound]`. `Search` also checks stable
structural sentence and certificate hashes, so a successful build forces the
compiled result instead of merely invoking the builder and discarding its
output.

python-flint is an **informational**, scheduled-only comparator for the
compiled carrier-degree decision family. The paired fixed registrations are
`runLeanDecision{16,20,24,28,32}` and
`runFlintDecision{16,20,24,28,32}`. The additional fixed registration
`runFlintDecisionOverhead` sends the atom-free sentence `∀ x, True` through the
same warmed `rcf/decide` path and supplies a conservative steady-state
per-call floor. At each substantive rung both sides consume the same
precomputed `Sentence`; the FLINT side also consumes its precomputed exact
version-1 fixture encoding. The persistent-driver request and response are

```text
{"family":"rcf","op":"decide","sentence":<v1 sentence>}
  -> {"ok":true,"result":<bool>}
```

Both sides return `Bool` and share one config that pins `Hashable.hash true`,
uses five repeats and a 0.2-second minimum total, and enables
`warmupFirstIter`. `runFlintDecisionOverhead` shares it except for eleven outer
repeats, which stabilize the floor median without changing the timed inner
batch. LeanBench starts one fresh child per outer warmup or repeat.
The discarded first call warms the Lean decision path on both sides; for FLINT
it also starts one `python3` process in the child. The timed auto-tuned
inner-repeat batch reuses that process's streams, and no driver is shared
between outer children. The complete FLINT request line, including the exact
version-1 sentence encoding, is precomputed; pipe transport and Python JSON
decoding remain measured comparator overhead. The floor includes the complete
request/reply path and minimal formula evaluation, but excludes process startup
and understates the parsing cost of the longer degree-rung requests. The
headline report retains raw times and ratios at every rung, then subtracts the
floor median from the FLINT median only on rungs where the floor is at most 50%
of the FLINT median. A rung above that threshold is floor-dominated, ineligible,
and reported raw-only. On an eligible rung where the floor exceeds 5%, both raw
and adjusted ratios are mandatory; below 5%, the raw ratio suffices. Routine
`hexrcf_bench verify` performs one semantic call through every fixed
registration. Scientific runs and ratio reporting require `python3` with
`python-flint` on the named release benchmark host.

This comparison covers carrier degree and real-root count only. It does not
measure atom multiplicity, common-root preparation, separation, certificate
replay, reification, literal elaboration, or end-to-end tactic cost.
python-flint is not proof-producing, and no comparable proof-producing
univariate RCF tactic is currently named; the tactic/elaboration track is
therefore `no-comparable-surface-in-named-comparator` rather than assigned a
fake ratio. The Phase-3 `local` emitter exercises related compiled workloads
but is neither an elaboration benchmark nor Phase-4 asymptotic evidence.

This contract and the pure-module extraction do not advance the phase marker.
`HexRCF.done_through` remains `3` until every dependency, including
HexRealRootsMathlib, has completed Phase 4 and both evidence tracks have their
required structural wiring and scientific artifacts.

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
  samples are evaluated exactly over `Fraction`; exact FLINT factor
  divisibility identifies which atoms vanish at a root, while every nonzero
  atom keeps the sign of the immediately adjacent open cell because the
  carrier contains every atom root. Dyadic endpoints are exact. The oracle
  consumes only the sentence AST,
  never Lean's carrier, certificate, cells, or signs. Missing
  python-flint is `SKIP`; unresolved enclosure ambiguity after the
  finite precision ladder is a hard failure. Fixtures require
  `decide = some expected`, so builder failure never passes a false
  case. They cover every comparison and Boolean form, true and false
  quantifiers, constants, no-root cases, shared and endpoint roots,
  close roots, and equal/reversed intervals. CI cases stay around
  degrees 8–12; the degree-50 stress case remains local. Phase-3
  wiring adds the `hex-rcf` assignment to `SPEC/testing.md` and one
  tuple to `scripts/ci/run_oracles.sh`, the repository's oracle registry;
  it advances `HexRCF.done_through` in `libraries.yml` but adds no unsupported
  manifest block, job, matrix, workflow, or dependency beyond the existing
  python-flint install.
- *local*: Mignotte-cluster atoms and degree-50 sentences exercise the
  pipeline where the isolation layer is under stress. Run
  `lake exe hexrcf_emit_fixtures local > /tmp/hexrcf-local.jsonl` and feed
  that stream to `scripts/oracle/rcf_flint.py --profile local`. This is an
  explicit developer profile and is not part of per-PR conformance.

## Complexity contract

For a sentence with `u` atom occurrences of degrees summing to `n`, of which
`m` are distinct nonconstant polynomials and `c` are distinct constants:

- Reification: linear in the goal.
- `P`: one product and one `squareFreeCore`, `deg P ≤ n`.
- Isolation: hex-real-roots' contract at degree `deg P`.
- Separation refinement: an adaptive, structurally fuel-bounded pass
  over touching adjacent pairs, reusing the carrier chain; already
  strict pairs pay no bisection cost and `k ≤ n` roots.
- Common-root preparation: one gcd and one generalized chain per
  distinct nonconstant `gⱼ`, reused across all `k` root cells.
- Sign matrix: one cached sign per distinct polynomial and cell, so repeated
  atom occurrences do not repeat arithmetic. There are `k·m` literal
  variation-count reads, `(k + 1)·m` open-cell evaluations, and at most `k·m`
  additional evaluations of the canonical left sample for nonzero root-cell
  signs, plus `(2k + 1)·c` constant evaluations. The current cell-wise API
  recomputes both distinct orders and performs coefficient-equality row lookups
  in every row, contributing `O((2k + 1)·u² + k·m²)` coefficient-array
  comparisons. There is no per-root gcd computation.
- Certificate replay in the kernel: one pass over the certificate,
  using polynomial multiplication/subtraction, evaluation, and
  comparison only.

For typical goals (`m ≤ 5`, `deg ≤ 10`, small coefficients) the whole
pipeline is dominated by elaboration overhead, not arithmetic.

## Time budgets (Phase 4 validation)

These are fixed whole-tactic acceptance cases, measured as the preregistered
paired `Tactic − Baseline` fresh-module delta on a clean, quiescent named host.
Raw total wall times and every pair remain in the artifact. They are not
one-parameter ladders, complexity verdicts, or substitutes for the compiled
LeanBench cases above.

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
