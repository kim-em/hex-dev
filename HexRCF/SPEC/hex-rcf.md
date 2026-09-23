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
`isolateRealRoots?_isSome`, together with the structurally fuel-bounded
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

The sections through the existing time budgets describe the integer/rational
path. The [planned real coefficient extension](#planned-real-coefficient-extension)
specifies the optional algebraic/named-constant route and its prerequisites.

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

   Run `Hex.ZPoly.isolateRealRoots? P`; the compiled builder knows this succeeds from
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
   `Sturm.IsSturmChain.sturm_Ioc` has no endpoint-nonroot premise, so this is
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
   strict monotonicity, and completeness. `Cell.Region` interprets the indexed
   cells for any finite list of real points; strict order gives the partition
   theorem. `Cell.Sem` is the rational root-model interpretation, with
   `Cell.sem_eq_region` identifying it with `Cell.Region`.
   `Cell.existsUnique_mem` retains the rational partition interface.

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
   `RootModel.root_unique_leftSpan`, show that the only carrier root in the
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
this literal chain, not a call to `ZPoly.sturmCount f`, and its total count
is the corresponding `−∞/+∞` difference. The proof factors through
`Sturm.IsSturmChain.sturm_Ioc` and `Sturm.IsSturmChain.sturm`. Constants are handled
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
whose fields are definitionally tied to the executable `ZPoly.sturmCount P`
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
theorem exists_cert_of_decide :
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

## Headline correctness theorem

`Hex.RCF.check_sound`: every certificate accepted by the public Boolean
checker proves its sentence, `cert.check s = true → s.toProp`. This is
the library's single end-to-end post-condition. The kernel checks it
together with the reduction proof `check s cert = true` and the
reifier-produced equivalence with the original goal, so no unverified
output of the compiled builder or reifier is trusted. `decide_sound`
and `exists_cert_of_decide` are convenience wrappers over the same
certificate path, not independent claims (see the preceding section);
the per-constructor soundness lemmas and replay theorems below are
load-bearing clauses of the headline proof, per the intermediate-lemma
rule in PLAN/Conventions.md §Headline correctness theorem.

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
  checks, and ordering/count consequences; `HexRCF/Isolations.lean`: literal
  isolation and real-root semantics;
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
  `HexRCF/Regions.lean`: coefficient-independent cell membership, partition,
  order, connectedness and polynomial sign constancy;
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
- `HexRCF/LintTests.lean`: Batteries' default environment linters, applied to
  declarations whose defining module is under the `HexRCF` module prefix. This
  enforces definition, structure, field, and tactic documentation plus the
  default naming/style checks. Theorem docstrings remain a review convention:
  `docBlameThm` is not default-enabled and also flags generated constructor-index
  theorems. The file intentionally uses legacy syntax so imported docstring
  metadata is available to the linters.
- `HexRCF/Tactic.lean`: the `rcf` front end.
- `conformance/HexRCF/{Conformance,EmitFixtures}.lean`: conformance
  in the shared sub-project.

The public `HexRCF` umbrella imports only the supported implementation and
proof API. The `*Tests.lean` regression modules above are compiled through a
separate non-public test target (`HexRCFTests` in the published repository,
`HexReleaseTests` in hex-dev) and are not re-exported to consumers.

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

The tactic track begins with same-module `Baseline − Baseline`,
`Degree10.Tactic − Degree10.Tactic`, and
`Degree50.Tactic − Degree50.Tactic` null controls, plus
`DoubleDegree50 − DoubleDegree50`, where `DoubleDegree50` checks two
independent degree-50 `by rcf` theorems to supply a genuinely higher
build-magnitude calibration. It then uses matched
fresh-module variants for each fixed case:
`Baseline` (identical imports), `Reify` (reify-only checksum), `Input`
(reflected sentence literal), `Search` (the same input plus a meta checksum of
compiled certificate construction, emitting no proof), `Literal` (input plus
the pre-generated certificate), `Replay` (literal plus its kernel-checked
theorem), and `Tactic` (the source goal closed by `rcf`). An external runner
rotates fresh builds and reports all four null calibrations followed by raw
paired deltas for reification, search, literal elaboration, replay, and the full
tactic. Six rounds balance which role builds first. Each null's signed deltas,
absolute and relative ranges, and median describe fresh-build noise only: they
are reported before the substantive pairs in artifact `config.order` and are
never subtracted, promoted to a significance test, or used to alter the fixed
tactic budgets of the run that produced them. A substantive delta is
noise-sized only against the selected
null's zero-centred maximum-absolute envelope at a comparable total build
magnitude; a cheaper selected envelope is scaled up by the magnitude ratio and
is never scaled down. The double-degree-50 null exists only to span the generic
control-magnitude gate; exact single-tactic nulls remain available for every
tactic pair and are expected to be selected instead. Otherwise the sweep leaves
the delta unresolved. `Search − Input` is
phase-attribution evidence only; the matching LeanBench target supplies the
scientific asymptotic verdict, and the report neither substitutes nor adds the
two. The headline report records source hashes, commit/toolchain/host/load
state, raw samples, artifact sizes, timeout cleanup, and the theorem's axiom
set, and refuses release claims from a dirty tree or incomplete provenance. It
uses the shared-host protocol from `SPEC/benchmarking.md`: paired arms are
adjacent with alternating orientation, every completed pair enters the summary,
and affinity, load and scheduler observations are retained as context rather
than admission gates.

The committed implementation lives under `bench/HexRCF/ProofProbe/`.
`Support.lean` owns the fixed source and reflected cases plus the precompiled
reify, search, and replay elaborators; `Generated.lean` owns the three
pre-generated certificate macros. The generator replaces exactly the
certificate's dyadic-interval order-proof omissions with `by decide` and
rejects any other pretty-printer omission, so the committed macro source is
independently rebuildable. All measured modules import the same generated
support module and no measured module imports another measured module.

There is one shared `Baseline`, one `DoubleDegree50`, and six measured
modules under each of `Quadratic/`, `Degree10/`, and `Degree50/`. The report
contains nineteen pairs: baseline, degree-10-tactic, degree-50-tactic, and
double-degree-50 null controls first, then these five pairs for each of the
three cases:

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
degree-50 measured modules and the double-degree-50 control without adding
them to routine CI. `HexRCFProofProbe` and `HexRCFProofProbeScientific` are
both build-only Lake libraries; there is no proof-probe executable or
in-process clock. The complete external sweep is:

```bash
cpu=$(python3 scripts/bench/idle_core.py)
taskset -c "$cpu" python3 scripts/bench/hexrcf_proof_sweep.py --samples 6 \
  --timeout 300 --warm-timeout 600 \
  --shared-host --cpu "$cpu"
```

`DoubleDegree50` takes roughly 15 seconds per arm. The runner takes each
reference/candidate pair once per round in alternating order and retains every
completed pair. The per-arm timeout bounds failures; ordinary host activity is
recorded as context and never starts a retry loop.

Only `Replay`, `Tactic`, and `DoubleDegree50` print an axiom report, fixed to
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
version-1 fixture encoding. The comparator is deliberately not assigned the
Lean target's `n^4` class: it factors the atom product over `ZZ` and asks
FLINT/Arb for certified real-root balls, a different algorithmic class from
the Lean carrier/certificate pipeline. Ratio divergence is therefore expected
and informational; the headline report must quantify the observed trend. The
persistent-driver request and response are

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

`HexRCF.done_through` is `7`. Its Phase-4 record required every dependency,
including HexRealRootsMathlib, to complete Phase 4 and both evidence tracks
to have their structural wiring and scientific artifacts; the committed
HexRCF Phase-4 headline report records that.

## Conformance fixtures

Per [SPEC/testing.md](../../SPEC/testing.md):

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
  by [testing.md](../../SPEC/testing.md). It independently forms and
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
  degrees 8–12; the degree-50 stress case remains local. The `hex-rcf`
  oracle assignment is recorded in `SPEC/testing.md` and as one tuple in
  `scripts/ci/run_oracles.sh`, the repository's oracle registry, in hex-dev;
  the published repository carries neither the oracle nor the fixtures, and
  nothing adds a manifest block, job, matrix, workflow, or dependency beyond
  the existing python-flint install.
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

For the fixed tactic probes, fresh-module cost is dominated by kernel
certificate replay. Nominal atom degree alone does not order the cases: the
three-atom degree-10 goal builds a degree-30 carrier and is comparable in
measured cost to the sparse one-atom degree-50 goal. The relevant drivers are
carrier degree, distinct-atom count, and coefficient growth.

## Time budgets (Phase 4 validation)

These are fixed whole-tactic acceptance cases, measured as the preregistered
paired `Tactic − Baseline` fresh-module delta on a clean tree, using
the shared-host protocol from `SPEC/benchmarking.md`. Raw total wall
times and every pair remain in the artifact. They are not
one-parameter ladders, complexity verdicts, or substitutes for the compiled
LeanBench cases above. Budgets are preregistered offline from a completed
archived sweep and frozen for the run they govern; no null quantity can move a
budget within a run. The failed-v5 [calibration record](https://github.com/kim-em/hex-dev/issues/9025#issuecomment-5104783847)
gives the components and derivation:

| Case | Tactic median | Scaled null envelope | Robust upper | Rule |
| --- | ---: | ---: | ---: | --- |
| quadratic | 0.259 s | 0.833 s | 1.092 s | multiply by 1.5, then round upward |
| degree 10 | 4.353 s | 3.560 s | 7.913 s | multiply by 1.5, then round upward |
| degree 50 | 4.330 s | 3.560 s | 7.890 s | retain the separate 30 s adversarial ceiling |

These are fresh-module regression bounds or adversarial ceilings, not
interactive-latency claims. Artifact metadata distinguishes the two kinds.

- Quadratic goals, one atom: under 2 seconds.
- Degree ≤ 10, up to 3 atoms: under 12 seconds.
- Adversarial degree-50, one atom: under 30 seconds.

## Planned real coefficient extension

This section owns the downstream integration promised by the
[real-closure family](../../SPEC/future-work.md#real-closures-of-ordered-fields).
It extends the integer/rational contract above; it does not change its
implementation status, phase, imports or performance claims. The coefficient adapter names
and signatures in this section are **planned contracts**, not checked Lean
declarations. The base handler registration and rational recognition boundary
described below are implemented independently of that adapter. The family SPECs describe prerequisites, not delivered APIs.
Transcendental coefficients use a caller-supplied approximation procedure and
its authenticated containment evidence; this extension neither supplies π/e
providers nor depends on HexInterval or HexIntervalMathlib. Constant-specific
analytic implementation, interval-library admission and their measurement
work are outside the family. Implementation is coordinated by [#10331](https://github.com/kim-em/hex-dev/issues/10331).

### Coefficients and supported sentences

Retain exactly one real variable under one `∀` or `∃`, with the six
comparisons and Boolean operations above. Domains remain `ℝ` or `Set.Ioc a b`
with literal dyadic endpoints. Algebraic or named-constant domain endpoints,
nested quantifiers and multivariate elimination are not added. Constant
expressions in polynomial atoms may use the following grammar:

```text
c ::= rational literal | a.toReal | registered closed real constant
    | -c | c+c | c-c | c*c | c^n | c⁻¹ | c/c       (n : Nat literal)
```

Here `a` is a closed, reconstructible `Hex.RealAlgebraicNumber` value using
its existing `toReal` interpretation. A registered closed real expression
may stand for `a.toReal` only with a kernel proof of that exact equality;
for example `Real.sqrt 2` must be identified with the **positive** selected
root of `X²-2`, not just any root. Such aliases add no arbitrary functions
to the grammar. Algebraic constructor evidence binds the defining polynomial,
selected real embedding, isolating interval/Thom descriptor and context.
A polynomial equation alone does not select an embedding. Definitions may
unfold within the source budget; opaque declarations need the same checked
registration. No numerical approximation is an algebraic constructor.

Accept real coefficients obtained from closed `Hex.AlgebraicNumber` values
through `RealAlgebraicNumber.ofAlgebraic` or its checked constructor and
`toReal`. The reality check and conversion must preserve the selected root.
An arbitrary complex algebraic number is not a real coefficient, and taking
its real part silently is not a valid conversion of that number. Explicit
projection `a.re.toReal` remains an accepted real coefficient. Checked
constructors must retain their actual semantics: an explicit fallback such
as `(RealAlgebraicNumber.ofAlgebraic? a).getD d` denotes `d` when conversion
fails, not the original `a`. Any accepted proof must concern that actual value.

Accept coefficients computed in `Hex.QAdjoin a` through a proved conversion
to their selected real values. Reuse `QAdjoin.toAlgebraicNumber` and its
value-preservation theorem, followed by checked real interpretation, or an
equivalent proved interpretation of the fixed field. The latter may interpret
the rational power-basis coordinates as a polynomial in the selected real
generator, avoiding a new minimal-polynomial computation and root isolation
for every field element. Kernel replay need not unfold those searches;
it must check the value-preservation evidence. For a real generator,
`QAdjoin.value_real` establishes reality of every field element. A nonreal
generator does not give a real embedding of the whole field, although an
individual element may pass the checked real conversion. Preserve the embedding
selected by `a`, reuse the existing field arithmetic, and do not require a
user to replace a field element by a radical expression or an approximation.
For coefficients from different fields, use the existing common-field or
conversion facilities where needed and prove value preservation. Do not assume
membership in an arbitrarily chosen `QAdjoin` field. The quantified variable
still ranges over `ℝ`, not over a number field that need not be real closed.

Support higher-degree root aliases written using Mathlib's `Real.rpow`,
including `(2 : ℝ) ^ (1 / 3 : ℝ)`. For a fixed nonnegative real algebraic
base `r` and a positive natural degree `n`, identify `r ^ (1 / (n : ℝ))`
with the selected nonnegative Hex algebraic root by a kernel proof.
Use the checked-alias mechanism above: the power equation and nonnegativity
must justify the exact source expression and chosen root. Mathlib's
`Real.rpow_inv_natCast_pow` supplies the power equation under these hypotheses.
This root-alias rule applies only to nonnegative bases: Mathlib's real power
of a negative base is not in general its signed odd root. Normalize the
closed exponent forms `1 / (n : ℝ)` and `(n : ℝ)⁻¹`, including numeral
instances such as `1 / 3`. Other rational exponents require their own checked
alias or a reduction to supported coefficient operations.
The Hex root may be constructed using `AlgebraicNumber.nthRoot` followed by
checked real conversion, or by selecting the nonnegative root of `X^n-r`
with the existing algebraic-coefficient root solver. In either route, prove
reality, nonnegativity and the power equation; the principal complex root
convention alone is not the required real identification. These aliases are
closed coefficients, not an extension to real powers of the quantified variable.

Allowed variable expressions are polynomials in `x` with these coefficients,
including division by a closed coefficient. Division by anything depending
on `x`, `exp x`, `sin x`, unregistered closed real expressions, irrational powers of the variable and
arbitrary free real parameters remain unsupported. A registered closed constant
may have an analytic source expression, but its numerical procedure and evidence
are supplied by the caller, not synthesized by this tactic. Local symbols are accepted only
when an explicit equality identifies them with one of these closed
coefficients; this substitutes a fixed value, not a symbolic parameter.
No implicit quantification over coefficients is introduced.

`Real.pi` and `Real.exp 1` are supported registration subjects, not automatically
available numerical providers. Their use requires a caller registration that
binds an approximation procedure and kernel evidence to that exact real. A
missing registration declines with an actionable diagnostic. The generic
interface can likewise bind another closed computable real expression;
its source identity and enclosure proofs are explicit. The caller supplies
convergence/progress laws only when claiming eventual success or total search;
finite accepted certificates require soundness only. Registrations match
closed subjects by a fixed normalization and definitional-equality policy,
with duplicate matches rejected. Try a registered whole subject before
recursively recognizing its grammar constituents; maximal closed-subterm
abstraction does not change this deterministic policy.

Every inverse/division retains the original nonzero-divisor obligations,
including divisions inside coefficients and divisions erased by cancellation
or multiplication by zero. The extension requires ordinary-kernel proofs of
these guards, either explicitly supplied with coefficient evidence or
constructed by accepted sign/zero replay. A zero divisor is an invalid
extension input even though Lean's total real division defines a value there.
An unresolved divisor exhausts; it is not assumed nonzero. In particular,
`0/(π-π)` and `(π-π)/(π-π)` are refused before simplification. This guarded
extension contract does not retroactively restrict existing rational fast-path
behavior. No inverse is silently cleared from an inequality: rational
clearing uses a proved positive scalar; a general closed inverse stays a
coefficient, or its clearing transformation must prove the scalar's sign and
corresponding comparison change.

### Shared frontend and module boundary

The existing source has `HexRCF.Language` over `ZPoly`, rational parsing in
`HexRCF.Reify`, derivative-seeded integer `SturmReplay`, and ordinary-kernel
quotation in `HexRCF.Tactic`. These remain the integer/rational fast path.
The generalized recurrence does not make that replay a general Tarski
checker or allow extension coefficients.

Reuse the [shared RealFormula frontend](../../SPEC/Libraries/hex-real-formula.md).
Its implementation from
[PR #10338](https://github.com/kim-em/hex-dev/pull/10338), merge revision
`843102b505b61724a9679d0011afb6d662812b92`, is available.
`RealFormula.Reify.Result` carries a valuation-parametric equivalence;
`QF n` and `Prenex n` store integer multivariate polynomials. The
`HexRCF.RealFormula` adapter under `adapters/` proves `toSentence_correct`,
`residue_correct` and `check_sound`, but `univariate?` drops only absent
parameters. It cannot specialize a coefficient coordinate to an algebraic
number or π. Reconcile these interfaces with the current source before
implementation; do not fork the formula syntax or the shared reifier.

The planned frontend first collects and certifies the original division
guards, before any cancellation or abstraction. Rewrite each variable-bearing
`p(x)/c` to `p(x)*c⁻¹` with an ordinary-kernel equality, then abstract maximal
closed coefficient subterms, including the whole `c⁻¹` or closed quotient,
into fresh real parameters. Thus `x/(4-π)` becomes `x*u`, where `u` is bound
to `(4-π)⁻¹` with its original guard, rather than `x/(4-u)` with `u=π`.
Likewise `1/(4-π)` is one coefficient. The shared arithmetic reifier
only clears rational literal denominators: it must never receive division by
a coefficient parameter. This preprocessing/equivalence bridge belongs here;
no parameter-denominator case is assumed in the shared reifier. Invoke that
reifier on the resulting polynomial source schema, with the parameters
explicitly ordered before the sole bound variable. Instantiate its proof for
**every** parameter valuation at the authenticated coefficient values, then
compose the checked preprocessing equivalence back to the original source.
The current shared reifier accepts declared real local parameters, not opaque
π/e ring atoms: creation of the schema, abstraction/substitution correctness,
coefficient recognition and domain evidence are new HexRCF bridges. Shared
normalization and scope/variable proofs are reused as they stand.

For `q : RealFormula.Poly (m+1)`, group monomials by the last coordinate's
exponent and evaluate their first `m` coordinates using ordinary arithmetic
on the family's executable coefficient representations `E`. Produce
`DensePoly E`, with `Specialize.eval` proving its interpreted real evaluation
equals `q.eval (append ρ x)`. Use the
[shared execution contract](../../SPEC/real-closure-execution.md); the
interpretation need not be injective but must reflect zero.
Reuse degree correspondence and retain the original source-domain proofs. The sentence
remains `Prenex m` interpreted at this **fixed** `ρ`; no new formula AST is
needed. Formula traversal, comparisons and Boolean folds use shared syntax.
The integer adapter applies directly only when no coefficient parameters
remain. Reuse its guard/equivalence proofs where their types apply, not by
pretending the specialized array is a `ZPoly`.

Represent bounded domains exactly as shared guard atoms: `∀ x ∈ Ioc a b, φ`
becomes `∀ x, (a<x ∧ x≤b) → φ`, and the existential becomes
`∃ x, (a<x ∧ x≤b) ∧ φ`. There is no separate domain field and no guard-stripping
pass. The guard polynomials participate in the atom/carrier list; ordinary
sign evaluation implements endpoint membership. Checked empty-domain folding
may avoid cell construction after all source guards have been validated.

The optional public import `HexRCF.RealCoefficients` supplies source-schema
preparation. Numerical solving remains planned and will use the base
registration interface in `HexRCF.Tactic`.
`@[rcf_handler]` registers a monomorphic meta declaration of type
`Hex.RCF.Handler` (`Expr → MetaM HandlerResult`). The base checks the signature,
deduplicates declaration names and tries them in `Name.lt` order, independent
of attribute/import order. `HandlerResult` distinguishes `declined`, terminal
`failed message`, and `proved proof`.

`Reify.recognizeSentence` reports unsupported **closed coefficient syntax**
through `ExceptT UnsupportedCoefficient MetaM`. Only that result enters
handler dispatch. `Reify.closeCoefficient?` also recognizes local real symbols
with direct explicit equalities to closed real expressions, in either
orientation. It substitutes every symbol of a compound coefficient and retains
a kernel-checked equality with the original expression. Handlers can reuse the public
`closeCoefficient?` helper while scanning the full original target; the first
recognition failure is not a complete coefficient/guard inventory. It does not chase
nonclosed or cyclic bindings, simplify arithmetic or cancel source divisors.
Unaccounted-for symbolic parameters, unsupported polynomial syntax and
non-rational interval endpoints remain frontend errors. The optional adapter
must still validate the closed grammar and transport its result to the original
target; equality recognition alone does not discharge source divisor guards. False rational
verdicts, replay failures and resource exhaustion remain terminal; diagnostics
are never parsed to choose a solver. Scalar recognition retains `norm_num`'s
exact rational normalization and propagates Lean's runtime exceptions.

Each handler receives the original target. Its metavariable assignments are
restored on every result, including success. All environment, message-log, elaboration-info and pending kernel-check
changes from successful handlers survive, including auxiliary proof declarations.
Declined and failed attempts roll these changes back. The base
type-checks the proof, compares its type with the original target without
assigning existing metavariables, and rejects transitive axiom dependencies
outside `propext`, `Classical.choice`, and `Quot.sound`. Decline tries the
next name; failure or an exception stops dispatch. Failed tactic attempts
restore the goal list and metavariable state, including on resource exhaustion.
The base imports no family module, and existing rational goals take the
original certificate path. Registration alone supplies no real-coefficient
solver. The optional adapter will register its own handler.

During incubation the new files are
`adapters/HexRCF/RealCoefficients.lean` and
`adapters/HexRCF/RealCoefficients/{Coefficients,Specialize,Replay,Soundness,Reify}.lean`,
with module prefix `HexRCF.RealCoefficients` and namespace
`Hex.RCF.RealCoefficients`. Use a separate **default build target**
`HexRCFRealCoefficients` with `srcDir := "adapters"`, plus the matching
`UMBRELLA_BUILD_TARGETS`/library metadata registration, as in the
`HexRCFRealFormula` target. This makes `lake build` and existing CI check the
adapter while the published `HexRCF` umbrella does not import it. Optional
import does not mean optional validation. The owning SPEC and soundness stay
here: HexRCF already uses Mathlib and needs no second companion. Publication
wiring is separate work.

The optional adapter imports the shared frontend and the family computational
libraries/companions. Reusable arithmetic, root/sign production and their
executable replay remain in Mathlib-free family owners, using ordinary exact field and polynomial APIs. Formula-specific specialization and certificate assembly
may use Mathlib-free modules of this adapter; semantic bridges and quotation
import Mathlib. Do not make the family import RealFormula to assemble a tactic
certificate. Neither `HexPoly`, `HexRealRoots`, `HexRealAlgebraic` nor the
shared formula libraries acquire a reverse dependency on this adapter or the
towers. Any reusable computational cell assembly needed for the extension
belongs with the family's shared samples; HexRCF supplies real semantics,
frontend glue and quotation, not a competing CAD/coverings representation.

### Delivered source-schema preparation

`Hex.RCF.RealCoefficients.Reify.prepare` in the optional
`HexRCF.RealCoefficients` import builds pending source data using the shared
reifier. The default Lake target `HexRCFRealCoefficients` checks this module;
the published base umbrella stays independent. No solver handler is registered.

The result contains the exact original proposition, an ordered array of closed
coefficient expressions, original divisor obligations after checked alias
substitution, shared `Prenex` syntax, the fixed coefficient valuation, and an ordinary-kernel proof of
`Prenex.toProp formula valuation ↔ original`. This equivalence uses Lean's total
real arithmetic. It does **not** establish the additional nonzero-divisor or
authenticated-provider conditions required for extension admission.

Input must be synthesized with assigned metavariables instantiated, as in the
base dispatcher. Preparation recognizes real rational arithmetic and literal casts, `Real.pi`,
`Real.exp 1`, arithmetic, natural powers and closed division/inversion. Direct
explicit equalities supply closed aliases through the base checked helper.
Arbitrary functions, nonstandard real arithmetic instances, parameters without
those equalities, variable-dependent division and multiple/nested real quantifiers
are rejected. Ioc endpoints are checked in the original source before alias
substitution; coefficient aliases do not widen the literal-domain grammar. Selected-root
reconstructions and sqrt aliases remain gated on their owner's actual APIs.

Before normalization, every original inverse/division obligation is retained,
including under zero multiplication, leading cancellation and empty domains.
Rational division inside a cast contributes the corresponding real-cast divisor;
non-field division inside a cast is rejected. Repeated identical source
expressions may share an obligation. Pending data for `0/(π-π)` therefore retains
`π-π`: it is not an accepted extension input, and a later admission checker must
reject it. No frontend simplification discharges these guards.

Variable-bearing division becomes multiplication by a closed inverse before
maximal coefficient abstraction; a wholly closed quotient stays one coefficient.
The shared integer reifier receives fresh ordered real parameters and no
parameter denominators. Its all-valuation proof is instantiated at the exact
source expressions and composed with checked alias substitution and division
normalization. Only one real quantifier and whole-real/literal-dyadic Ioc domains
are admitted; Ioc membership remains shared guard atoms.

Preparation uses the shared structured errors and reflection budgets. It charges
source admission before and after alias substitution, literal coefficient and
exponent work, shared reification, and the final proof. Success restores caller
metavariables while retaining declarations needed by the emitted proof; errors
restore the full saved state. Unsupported syntax and budget exhaustion use
structured errors; unexpected elaboration, kernel and runtime exceptions remain
terminal exceptions. The source tests check exact equivalences and
retained guards, including rational casts, aliases, all Boolean/comparison forms,
equal/reversed Ioc bounds, unsupported inputs and budget exhaustion. Fresh named
schema theorems audit only `propext`, `Classical.choice` and `Quot.sound`.
These are frontend regressions, not real-coefficient decision proofs or full
extension performance evidence.

### Construction, evidence and public API

Use the family's ordinary total representation operations, roots/selected-root
operations and section/sector samples, with their companion interpretation
proofs at the tactic boundary. Existing total
[polynomial arithmetic](../../HexPoly/SPEC/hex-poly.md) supplies the coefficient
computations. No shared fallible coefficient record or arithmetic budget is
introduced. These shapes describe the tactic integration surface:

| Planned operation | Contract |
| --- | --- |
| `Coefficients.prepare` | Recognize supported closed syntax and establish its embedding/source identities and original divisor guards. |
| `Specialize.prepare` | Given the shared sentence and its fixed coefficient values, produce `DensePoly K` atoms and the evaluation correspondence. |
| `build` | Using total representation operations/sign, construct the verdict and finite complete cell certificate; correctness assumes their lawful semantic interpretation. |
| `Replay.check` | Validate the supplied certificate against its bound inputs; reject malformed evidence. |
| `check` | Accept precisely a verified true verdict. An accepted false verdict remains diagnostic. |
| `check_sound` | Transport accepted evidence to the original real proposition. |
| `build_checks` | On the valid exact-field fragment, produced certificates pass replay and carry the correct verdict. |

The tactic retains its existing source/reflection execution limits and
structured diagnostics; these do not become the signatures of arithmetic
operations. Where no exact ordered-field interface is supplied, a separate
finite-certificate path can use caller-provided containment/identity proofs
or direct enclosure arguments. It does not run the generic root algorithm
over a partially decidable coefficient field or claim completeness for it.
For example `π<4`, together with nonnegativity of squares, certifies the
promised `∀ x : ℝ, x² > π-4` example without constructing `ℚ(π)` as an
executable ordered field.

Certificates bind the exact shared sentence, coefficient order, original
source guards, registry/provider versions, full context DAG, operand literals
and selected-root identities. Hashes can index caches but cannot authenticate
these bindings. Preflight checks precede zero, constant and empty-domain
shortcuts; unused payload may be omitted, but every retained claim's transitive
dependencies must be validated. A zero/constant polynomial does not erase
its source's domain obligations.

Compiled construction specializes atoms, certifies their semantic degrees,
builds a squarefree carrier for their nonconstant root union, and obtains
complete ordered roots and shared samples. Repeated factors and common roots
are deduplicated with certified identity and root-union evidence. Certificate
replay checks polynomial identities and complete root/table evidence; it does
not rerun isolation, gcd search, BKR production or approximation. The generic
carrier/root-union bridge and specialization/cell correspondence must establish
complete ordered roots and correct signs for the actual coefficient values.
`Cell.Region`, `Cell.Region.sign_eq` and the `CellFold.Region` theorems supply
the coefficient-independent cell interpretation, sign constancy and quantifier
folds. Their root-coverage and sign hypotheses must be proved from the checked
evidence; the integer carrier's signatures alone do not supply them over raw
tower elements.

Required coefficient/replay evidence includes:

- Original domains and successful arithmetic interpretations, including all
  inversions and positive scales. Semantic degree supplies either all-zero
  coefficients or a nonzero leading coefficient and zero coefficients above
  it. Array length and syntactic inequality are insufficient.
- Authenticated constant enclosures from the caller-supplied approximation rules,
  including exact subject, source theorem, finite rational endpoints,
  requested/actual precision and any predecessor enclosures. A callback,
  decimal, display name or unproved containment proposition is not evidence.
- Positive/negative signs established by strictly positive lower or
  strictly negative upper bounds. Exact zero
  requires coefficient identities, algebraic selected-root replay or an
  explicitly supplied proof of that exact evaluation-zero claim. A nondegenerate
  enclosure containing zero does not establish equality; certified `[0,0]`
  is itself an exact evaluation-zero identity.
- Nested coefficient sign/zero certificates and general Sturm–Tarski/BKR
  replay with domain, squarefreeness, degree, scale and endpoint guards.
  Dependencies are finite and acyclic, with predecessor signs established
  before their use. A query cannot prove its own coefficient assumptions.
- Root selection existence and uniqueness; comparison/re-encoding across
  different defining polynomials; checked transports after splitting or
  enlargement for every live polynomial, guard, root and cached sign.
- Complete root coverage, cell membership, sign constancy, atom alignment,
  guard-atom evaluation and the Boolean/quantifier fold. True existential
  certificates include real sample existence as below; true universals require
  full domain coverage. With the guarded matrix, all cells enter the strict
  fold unless a checked simplification removes an obligation. Preserve failure
  propagation and the existing diagnostic-only false policy.

Here is the headline theorem's mathematical shape, not Lean source:

```text
check_sound
  (s : RealFormula.Prenex m) (ρ : Fin m → ℝ) (goal : Prop)
  (env : coefficient/source registry) (cert : Certificate)
  (hLaws : the actual arithmetic, sign and cell correspondence theorems)
  (hEnv : Authenticated env ρ)
  (hReify : RealFormula.Prenex.toProp s ρ ↔ goal)
  (hCheck : check env s cert = true) : goal
```

`Authenticated env ρ` binds each coordinate to its original supported closed
expression and selected embedding, the supplied provider rules to their exact registered real subjects, and any supplied proof references to their precise claims.
`hLaws` is discharged by the family's actual companion theorems for these
exact fields and the shared real foundations; it is not a runtime assertion
that callbacks are sound. In finite-certificate mode interpret closed expressions
in `ℝ` (or the actual generated real subfield), without asserting injectivity
of formal rational-function syntax. `hReify` includes coefficient abstraction,
normalization and substitution correctness; if it needs original domain
facts, those are first extracted from accepted coefficient replay and used
to construct the equivalence. No unresolved reifier side conditions remain.

Acceptance must establish the one-quantifier/dyadic-domain fragment, valid
contexts, **all original divisor guards**, semantic degrees, every nested
claim and all cell/realization obligations listed above. These are checked
conclusions, not silent premises of `check_sound`. Explicitly supplied guard
proofs are kernel terms in the authenticated environment. Supply an auxiliary
`check_domains` projection for constructing `hReify` without assuming the
final goal. No transcendence, convergence or sufficient-search-fuel hypothesis
belongs in this success theorem. Quotation emits literals, their ordinary
kernel acceptance proof and the actual law/equivalence proofs; it does not
accept compiled `Bool` evaluation as a theorem. No `native_decide`, new axiom,
`sorryAx`, foreign oracle or compiler trust is admissible.

### Selected roots, sectors and half-open domains

Consume the family's sample/Thom interface and the
[finite-sign realization contract](../../SPEC/Libraries/hex-real-closure-mathlib.md#finite-sign-realization).
A section is one selected **real** root with identity and sign-at-root proofs.
For sectors, order and adjacency/completeness must exclude every nonzero atom's
roots, so signs are constant throughout the open interval. Ordinary real
samples always suffice for these one-dimensional cells when the boundaries
have compatible real interpretations: a midpoint for a bounded sector,
`a+1` or `b-1` on a ray, and `0` for the whole line. Their representation and
membership still require the arithmetic correctness and root transport
proofs; total field operations compute these points. Dyadic separation
is optional, not a requirement over generic coefficient fields.

The bounded-domain contract is proved through the two guard atoms, not a
second domain representation. At a root `r`, their conjunction is exactly
`a<r ∧ r≤b`; their signs include the upper endpoint and exclude the lower.
Their roots also split sectors at `a,b`, so a sector satisfying the guard is
inside `(a,b]` and its ordinary sample satisfies the bound. A cell spanning
a guard boundary cannot be accepted as sign-constant. Equal/reversed endpoints
make the guard conjunction false everywhere, giving true universals and false
existentials. Thus
an existential witness must satisfy the guard, not merely inhabit some cell.
Family Tarski queries still use **open, root-free finite endpoints**: the
selected-root/sign-at-root proofs for the guard polynomials supply exact
endpoint classification; never call those queries directly at a root endpoint
of the public half-open domain. Any alternative isolation boundaries must
carry their own checked root-free endpoint evidence.

If compiled search chooses infinitesimals, they remain internal. Before any
real existential step, export `Sample.realizeReplay` evidence for the finite
joint conjunction of fixed coefficient values, original domains, selected
roots, cell/bounded-domain inequalities and every consumer sign. Nested
algebraic choices must satisfy these constraints at the **same** selected
root, via a joint table or checked count-one identification, not separately
chosen witnesses for different atoms. Specialize earlier infinitesimals
before later ones and retain their dependent neighborhoods and guards.
There is no substitution `ε : ℝ` satisfying infinitesimal axioms and no
embedding of the whole non-Archimedean field into `ℝ`. Missing realization
evidence makes this tactic attempt decline or select the ordinary-point backend. Replay can use the
companion's direct finite-evidence real theorem without an infinitesimal
ambient model; a symbolic-model backend separately needs the companion's
ordered algebraic real-closure existence foundation.

### Termination, completeness and refusal

Exact-field construction terminates by finite formula traversal, polynomial
degree descent, the family's total root isolation and total coefficient
operations. Supply the corresponding correctness and termination proofs.
No general nested arithmetic/resource-budget protocol is required. Replay
terminates by finite certificate structure, composing ordinary arithmetic
and finite sign proofs without repeating root or approximation search.

Source recognition may decline unsupported syntax; a failed original divisor
guard or false certificate cannot close a goal. A bounded enclosure attempt
may report an undetermined sign. Existing elaborator limits may interrupt a
tactic. These are tactic diagnostics, never a false sentence verdict, default
zero coefficient, empty root list or successful partial result. Restore goal
and metavariable state on every failed attempt.

For valid algebraic-only coefficients, exact field operations, comparisons
and root isolation give a complete mathematical decision procedure for this
sentence fragment. Prove construction correctness and certificate acceptance;
the tactic closes only true sentences. Its execution limits do not weaken
the completeness theorem for the underlying mathematical procedure.

A total transcendental tower requires correct convergent user-supplied
approximations and transcendence of each constant over its **embedded
predecessor field**, together with the proved terminating sign construction.
Separate transcendence of π and e over ℚ does not give this hypothesis for
ℚ(π,e). No such instances or approximation providers are silently installed.

Without those hypotheses, finite containment and exact-identity evidence
still proves specific real claims. The enclosure-only fragment includes
nonzero coefficient signs separated from zero, explicit divisor guards,
formal identities with those guards, and direct consequences such as a
positive closed constant plus a square. It also checks supplied complete
cell certificates whose coefficient/realization obligations are proved.
There is no promise to discover every such certificate, decide unresolved
relations between constants, or run full tower root isolation with only a
bounded comparison attempt. Successful finite checking requires soundness,
not transcendence or convergence.

### Manual, conformance and proof evidence

The future manual must distinguish the optional import, algebraic completeness,
execution-limit failures and finite-certificate mode. Algebraic and generic
supplied-bound examples are required. The following π/e demonstrations are
optional when caller registrations are available; their absence does not
create a provider implementation obligation:

```lean
-- after HexRCF.RealCoefficients and caller-supplied authenticated π/e registrations
example : ∀ x : ℝ, x^2 > Real.pi - 4 := by rcf
example : ∀ x : ℝ, x^2 + 1 / (4 - Real.pi) > 0 := by rcf
example : ∀ x : ℝ, x^2 + Real.exp 1 > 2 := by rcf
example : ∃ x : ℝ, x = Real.exp 1 ∧ 2 < x ∧ x < 3 := by rcf
```

The division example must replay the original guard `4 - Real.pi ≠ 0`,
justified by the supplied upper bound on `Real.pi`, before coefficient
normalization. Include a generic supplied-bound variant independently of
whether a π registration is available.

For the API examples, construct `a` as the selected positive root of `X²-2`
and `b` as its other real root `-a`, with reconstruction/equality proofs.
This is the negative algebraic conjugate, not `RealAlgebraicNumber.conj`,
which is complex conjugation and fixes real values.
Demonstrate `∃ x, x²=a.toReal`, `∀ x, x²+ a.toReal>0`, and an inequality
whose verdict changes when `a` is replaced by `b`. Show a registered
`Real.sqrt 2` alias closing the same goals. Demonstrate the low-level
`prepare → build → check → check_sound` path with explicit coefficient
identities and original-goal equivalence. Print failures separately from
accepted false results; examples of `#eval` alone are not proof examples.

The manual must also construct a nonquadratic real algebraic coefficient,
show arithmetic in its `QAdjoin` field, and use the resulting real values in
tactic proofs. For example, select the real root `α` of `X³-X-1`, compute
`β=α²-1` in its fixed field, and prove `∀ x : ℝ, x/α=β*x` after the checked
real conversions. Include a formula combining coefficients from independently
constructed fields and prove that any common-field coordinates represent
the original real values, using `QAdjoin.common_get` or the corresponding
conversion theorem.
Retain the existing number-field and real-algebraic manual examples and link
them from the tactic documentation.

Include a higher-degree Mathlib root alias as an actual tactic coefficient,
for example `∀ x : ℝ, x² + (2 : ℝ)^(1 / 3 : ℝ)*x + 1 > 0`.
Show the checked identification with the positive root of `X³-2` and the alias
setup alongside the `Real.sqrt` examples. These examples must use the same
algebraic-coefficient interface as direct Hex values.

Required tests extend the existing
[conformance discipline](../../SPEC/testing.md):

- Kernel theorems for algebraic examples and generic supplied-bound coefficient
  transport; optional π/e examples use supplied registrations. Include constant-only and
  zero-polynomial bodies, semantic leading cancellation, all comparisons and
  Boolean forms, and integer/rational fast-path compatibility.
- Checked real conversion from `AlgebraicNumber` and `QAdjoin`, agreement
  with their existing value interpretations, and coefficients from different
  number fields. Reject a claimed real interpretation of a nonreal value,
  wrong selected roots and higher-root aliases lacking the required equality
  or branch proof. Test explicit real-part projections and checked-constructor
  fallbacks against their actual values.
- Repeated/common roots, including atoms `(x-a.toReal)^2` and
  `(x-a.toReal)*(x-1)`, reducible selected-root definitions, re-encoding and
  splitting with live dependent roots. Check exact signs/multiplicities and
  wrong-conjugate rejection independently of display syntax.
- Root equality at both dyadic endpoints, zero, equal/reversed intervals,
  sectors split at guard boundaries, repeated roots at endpoints, and false universal
  versus false existential diagnostics. Algebraic/named-coefficient formulas
  must exercise these cases even though interval bounds remain dyadic.
- Negative divisors, nested guarded division, cancelled and zero numerators,
  exact-zero divisors and unresolved divisors. Reject certificates omitting
  even a cancelled source guard. Exact `π-π=0` is accepted with its guards;
  unresolved signs at the supplied precision must be refused. A synthetic
  user procedure returning valid nonseparating bounds without an exact-zero
  identity exercises this path without implementing any analytic provider.
  π/e variants are optional caller-supplied tests, not independence claims.
- Swapped coefficient coordinates, wrong subjects/precision/source rules,
  stale provider versions, changed root/context identity, missing transports,
  cycles/forward references, omitted BKR support, wrong degree/scale/endpoint
  evidence and interrupted tactic attempts. Fabricated real-witness evidence using ε
  is rejected. Test provider uncertainty without assuming any open numerical
  relation is true or false.

Exact algebraic checks and independently certified interval enclosures are
the numerical test evidence. Approved external CAS fixtures (python-flint/Arb
for algebraic and real bounds, pinned Z3 family samples where applicable)
are independent differential tests, never soundness premises. Kernel tests
must rebuild quoted proofs in fresh modules and audit the transitive axiom
set, excluding `sorryAx`, new axioms and compiled evaluation trust.

Keep separate [compiled and fresh-module proof tracks](../../SPEC/benchmarking.md#fresh-module-proof-evidence).
Mathlib-free family drivers measure coefficient production, root/sign search,
executable replay and specialization arithmetic separately. Build-only HexRCF
probes measure coefficient abstraction/reification, literal elaboration,
ordinary-kernel replay, realization and the full tactic with matched imports.
No Mathlib-importing executable benchmark is added. Vary degree, distinct atom
count, coefficient size, precision and tower depth independently; include
bounded failures and common/repeated roots, not only easy enclosing bounds.
Record proof/serialized bytes, memory, unique DAG nodes and expanded reference
work. For local work `L_d` with child costs `T_i`, charge
`T_d ≤ L_d + ∑ T_i`; do not hide recursively nested proofs behind a unit-cost
sign oracle or assert a polynomial bound in unrestricted tower depth.
Quotation must preserve sharing or account for its expansion. Follow shared-host
CPU selection, fixed trial-major schedules, adjacent alternating AB/BA arms,
retention of every completed sample and at most one unchanged inconclusive
rerun. Existing rational tactic timings do not become extension guarantees;
preregister bounded extension cases when implementation permits measurements.

### Implementation prerequisites

The following are prerequisites for implementation/proof claims, not new assignments.
The coordinator owns dispatch; a merged SPEC alone satisfies none of the
missing algorithm or theorem obligations.

| Owner / current surface | Required semantic artifact |
| --- | --- |
| Existing HexRCF integer path | Preserve `check_sound`, real reification equivalences, half-open semantics and ordinary-kernel quotation. Add the base-owned fallback registry and structured rational recognition declines; generic coefficient/cell bridges remain new. |
| Shared frontend, PR #10338 and consumer #10329 | Merged `QF`/`Prenex`, scope/normalization/valuation proofs and optional integer RCF adapter. Add guarded division preprocessing, maximal closed-coefficient abstraction and `Specialize.eval` here; virtual substitution itself is not a prerequisite and its symbolic parameters are not silently accepted. |
| HexPoly / HexPolyMathlib | Existing total `DensePoly` arithmetic, division/gcd/xgcd and correspondence; ordinary ordered-domain pseudo-division for shared signed remainder chains. |
| HexRationalFn / HexRationalFnMathlib | Existing exact rational-function arithmetic and correspondence over lawful coefficient fields. The tactic separately retains every original source divisor guard. |
| Caller-supplied approximation procedures | Exact finite bounds bound to the registered real subject, kernel containment evidence and terminating approximation calls. Convergence and relative transcendence are extra hypotheses for total sign search. Generic composition belongs to ordered-fn; no HexInterval/HexIntervalMathlib or bundled π/e provider implementation is required. |
| [Ordered-fn](../../SPEC/Libraries/hex-ordered-fn.md) and [companion](../../SPEC/Libraries/hex-ordered-fn-mathlib.md) | Caller-registered real constants, minimal exact finite-bound arithmetic, guarded evaluation, Horner enclosure composition, nested sign/zero evidence, replay soundness and conditional progress. Successful finite interpretation must not assume faithful specialization. |
| HexRealRoots / HexRealRootsMathlib | Shared signed-remainder kernel and its positive-scaling/representation bridges, general Cauchy-index/Tarski replay correspondence, and shared `IsRealClosed ℝ`; the existing derivative-seeded integer theorem is insufficient. |
| [Sturm](../../SPEC/Libraries/hex-sturm.md) and [companion](../../SPEC/Libraries/hex-sturm-mathlib.md) | Domain-checked ordered-field Tarski queries, endpoint adapters, complete root counts and nested coefficient replay/transport soundness. |
| [Sign-det](../../SPEC/Libraries/hex-sign-det.md) and [companion](../../SPEC/Libraries/hex-sign-det-mathlib.md) | Complete BKR support/counts, Thom existence/uniqueness/order, sign-at-root, common-root re-encoding and their literal correspondence, using the existing matrix/rank companions. |
| HexNumberField / HexNumberFieldMathlib | Existing `QAdjoin` arithmetic, coordinate interpretation, `toAlgebraicNumber` value preservation, `value_real`, common-field conversions with `common_get`, and `AlgebraicNumber.nthRoot` correspondence. The adapter must prove their selected real interpretations and root-alias equalities. |
| HexRealAlgebraic / HexRealAlgebraicMathlib | Existing `toReal`, exact comparison, `RealAlgebraicPoly.roots` with multiplicities/`all`, and Repr correspondence; new tower conversions and trivial-base agreement must be proved. |
| [Real-closure](../../SPEC/Libraries/hex-real-closure.md) and [companion](../../SPEC/Libraries/hex-real-closure-mathlib.md) | Implemented contexts and total coefficient representations, selected-root interpretation, splitting/all-live transport, Yun and complete ordered roots, shared samples and real `Sample.realizeReplay` including joint nested constraints. SPEC #10318 is merged; these APIs/proofs are planned. Quotient and interpretation laws are proof prerequisites; core algebraic execution is independent of them. Transcendental search retains its caller progress premise. |
| Tau Ceti through the owning companions | Univariate IVT/Rolle, signed-remainder/Cauchy-index, Thom and BKR foundations from the existing #10300 roadmap work. Ordered algebraic real-closure existence is additionally needed for symbolic infinitesimal ambient models; direct finite replay into ℝ does not need that existence theorem. Continue the existing roadmap PR, never a duplicate. |
| This optional HexRCF adapter | Coefficient/source authentication, shared-schema abstraction/specialization, generic carrier/cell and half-open correspondence, finite real witness export, quotation, `check_domains`, `check_sound`, construction termination and certificate acceptance, manual examples and both evidence tracks. |

Transcendence over predecessor fields and effective convergence are explicit
hypotheses of any future total named-constant mode, not missing axioms to add
to successful bounded checking. The base registry does not advance the library phase or satisfy the
coefficient adapter implementation gates.

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
