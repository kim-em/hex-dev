# hex-virtual-subst

Virtual substitution for real polynomial formulas, eliminating one variable
of degree at most two in every atom at a time. The output is a formula in
the remaining variables with no radicals, reciprocals, infinitesimals, or
infinities. The shared language is the separate
[hex-real-formula](hex-real-formula.md) library. This document also specifies
`hex-virtual-subst-mathlib` and its `virtual_subst` tactic.

## Scope, dependencies, and proof order

`HexVirtualSubst`, namespace `Hex.VirtualSubst`, is Mathlib-free and depends
on `HexRealFormula` and `HexMvPoly`. It owns coefficient extraction, guarded
test points, substitution tables, elimination, and certificate checking.
`HexVirtualSubstMathlib` depends on that core, `HexRealFormulaMathlib`,
`HexMvPolyMathlib`, `HexRCF`, and Mathlib. It proves the elimination-set and
local sign theorems over `ℝ`, connects executable formulas to `toProp`, uses
the shared adapter in `HexRCF.RealFormula`, and implements the tactic.
Generalization to an ordered field with `IsRealClosed` is a later theorem extension; arbitrary ordered
fields do not suffice for quadratic root existence.

Ship **exact reflection first**: a total, budgeted eliminator over the kernel
form, with equivalence on success. Then ship a compiled certificate producer
and checker, reusing those same substitution lemmas. No algebraic-number,
root-isolation, CAD, or cubic implementation is needed for the quadratic
core. RCF is a companion fast path, not a core dependency. The new formula
frontend and its beyond-H0 reifier work are implementation prerequisites,
not blockers to writing this SPEC. No implementation or phase registration
is part of this design change.

## Elimination sets

Use `toUnivariate` in a selected main variable, with a proved coordinate
permutation and coefficient extraction. Pass the fixed lexicographic order
on the remaining coordinates as `toUnivariate`'s coefficient comparator
`cmp'`, so its coefficients already have the formula library's order.
After normalization every atom is
`p(x) = a*x² + b*x + c`, where `a,b,c : Poly n`. The eligibility check bounds
**each atom's degree in x**, not total degree or the degree of a product of
atoms. Symbolic leading coefficients must be split by their value at the
remaining valuation; syntactic nonzeroness is not a nonvanishing proof.

For each atom polynomial, include the following guarded formal roots. Here
`D = b² - 4*a*c`; root labels do not assert their numerical ordering.

| Case | Guard | Formal roots |
| --- | --- | --- |
| Quadratic | `a ≠ 0 ∧ D ≥ 0` | `(-b - √D)/(2*a)`, `(-b + √D)/(2*a)` |
| Linear degeneration | `a = 0 ∧ b ≠ 0` | `-c/b` |
| Constant degeneration | `a = 0 ∧ b = 0` | None; retain the comparison on `c` |

For every listed root include both `r` and `r + ε`, with the same guard.
Also include `−∞`, guarded by `True`, once. Zero polynomials contribute no
actual boundary. When `D=0` the repeated roots may remain duplicated;
deduplication is optional and must preserve coverage. `a<0` is allowed:
never infer that the minus-labelled root is the smaller one.

The reference generator emits at most `6*m+1` syntactic test points for `m`
distinct atom polynomials, counting both quadratic and linear guarded
alternatives. At a fixed valuation at most `4*m+1` are active before
deduplication. Thus the often-quoted factor `2*m+1` is not a bound for this
unpruned symbolic list. A later relation-sensitive generator needs its own
coverage theorem before replacing this generator.

For a quantifier-free `φ : QF (n+1)`, let `E φ` be this complete list and
`subst φ t : QF n` the Boolean extension of the atom rules below. The central
companion theorem, `elim_correct`, is:

```text
(∀ p ∈ φ.polys, degree p last ≤ 2) →
∀ ρ : Fin n → ℝ,
  (∃ x : ℝ, φ.toProp (append ρ x)) ↔
  (∨ t ∈ E φ, (guard t ∧ subst φ t).toProp ρ).
```

Both implications are required. Finite roots are evaluated literally.
`r+ε` means truth on some interval `(r,r+η)` with `η>0`; `−∞` means truth
below some finite bound. These are eventual truth predicates, not elements
of `ℝ`. Each atom has an eventually constant sign on these intervals, and
finitely many atoms have a common interval. This proves Boolean substitution
including negation, not just conjunction. Conversely, a satisfying point
is a root, lies before all roots, or lies in an interval immediately right
of some root. All atom signs are constant in each such interval. This
finite sign decomposition proves completeness without computing or sorting
any roots in the executable algorithm.

The formal precedent is Scharager–Cordwell–Mitsch–Platzer, FM 2021
([AFP entry](https://isa-afp.org/entries/Virtual_Substitution.html)). The
paper credits Katherine Cordwell; the current AFP entry uses her name
[Katherine Kosaian](https://sites.google.com/view/katherinekosaian/).
The Cordwell–Tan–Platzer paper is the separate BKR work. AFP's
[GeneralVSProofs](https://isa-afp.org/browser_info/current/AFP/Virtual_Substitution/GeneralVSProofs.html)
`gen_qe_eval'` assumes `all_degree_2 var L` and a valuation-prefix length
condition, proves the existential equivalence for a conjunction of atoms,
and establishes independence from the eliminated coordinate. Here fixed arity
and `QF n` encode that independence; the deliberately redundant list extends
the same boundary argument directly to Boolean formulas, avoiding mandatory
DNF. This is a different executable enumeration, not a claim that AFP's
optimized generator is identical. Its
[ExportProofs](https://isa-afp.org/browser_info/current/AFP/Virtual_Substitution/ExportProofs.html)
`VSGeneral` preserves semantics; that alone does not assert that every
arbitrary-degree input is reduced to a quantifier-free formula.

## Substitution tables

All displayed expressions below are abbreviations for integer-polynomial
atoms and Boolean combinations. They specify the complete reference rules;
they are not requests for a radical datatype in the output language.

### Finite roots

Represent a root by `(u + v*√D)/w` under `D≥0 ∧ w≠0`. Quadratic roots use
`(u,v,w)=(-b,±1,2*a)` and linear roots use `(-c,0,b)` with `D=0`. For an atom
polynomial `q(x)=α*x²+β*x+γ`, compute and check the identity

```text
U = α*(u² + v²*D) + β*u*w + γ*w²
V = 2*α*u*v + β*v*w
w² * q((u+v*√D)/w) = U + V*√D.
```

Identity replay takes place polynomially modulo `s²-D` in a formal variable
`s`; the once-proved real rule instantiates `s=√D`. The denominator `w²` is
strictly positive even if `w<0`. A kernel identity check by itself does not
prove the order or guard conditions.

For `D≥0`, define `H=U²-V²*D` and the polynomial sign formulas:

```text
Z(U,V,D) := H=0 ∧ U*V≤0
P(U,V,D) := (D=0 ∧ U>0) ∨
  (D>0 ∧ ((V=0 ∧ U>0) ∨
           (V>0 ∧ (U≥0 ∨ H<0)) ∨
           (V<0 ∧ U>0 ∧ H>0)))
N(U,V,D) := P(-U,-V,D)
```

These mean zero, positive, and negative for `U+V*√D`, respectively. The
`D=0` branch and the sign conditions accompanying squaring are essential.
Under the root guard substitute every comparison by this table:

| Atom | Finite-root result |
| --- | --- |
| `q = 0` | `Z` |
| `q ≠ 0` | `P ∨ N` |
| `q < 0` | `N` |
| `q ≤ 0` | `N ∨ Z` |
| `q > 0` | `P` |
| `q ≥ 0` | `P ∨ Z` |

### A root plus ε

Use the finite-root rules to obtain predicates `Zᵢ,Pᵢ,Nᵢ` for the signs of
`q(r)`, `q'(r)`, and `q''(r)`, for `i=0,1,2`. Set

```text
Zε := Z₀ ∧ Z₁ ∧ Z₂
Pε := P₀ ∨ (Z₀ ∧ P₁) ∨ (Z₀ ∧ Z₁ ∧ P₂)
Nε := N₀ ∨ (Z₀ ∧ N₁) ∨ (Z₀ ∧ Z₁ ∧ N₂).
```

The six rows of the finite-root table apply with `Zε,Pε,Nε`. In particular,
equality just to the right of a root requires all derivatives to vanish;
`q(r)=0` alone is insufficient. Prove `eps_sign` by the exact Taylor identity
`q(r+h)=q(r)+q'(r)*h+q''(r)*h²/2` and the sign of the first nonzero
coefficient for sufficiently small **positive** `h`. Include the all-zero
case and prove a common positive bound for a finite formula. `ε` is not a
user-selectable small rational.

### Negative infinity

For `q(x)=α*x²+β*x+γ`, let

```text
Z∞ := α=0 ∧ β=0 ∧ γ=0
P∞ := α>0 ∨ (α=0 ∧ β<0) ∨ (α=0 ∧ β=0 ∧ γ>0)
N∞ := α<0 ∨ (α=0 ∧ β>0) ∨ (α=0 ∧ β=0 ∧ γ<0).
```

Again all six comparisons use the same table with `Z∞,P∞,N∞`. Prove
`negInf_sign` by eventual dominance of the highest nonzero term. The odd
linear term reverses sign at negative infinity. Constants and the zero
polynomial require no limiting argument.

## Reflection and certificates

The public reflection API `elim : QF (n+1) → Budget → ElimResult n` has
constructors `success (ψ : QF n)` and `declined (reason : Reason)`. Reasons
distinguish unsupported input from budget exhaustion; the caller retains
the original input. It validates degree, generates the entire guarded set,
substitutes, and performs only proved exact local reductions. `elim_sound` states

```text
elim φ budget = success ψ →
∀ ρ, ψ.toProp ρ ↔ ∃ x, φ.toProp (append ρ x).
```

This public `QF` API is a wrapper: `toKernel` supplies a well-formed list
input to the private kernel eliminator, and validated decoding reconstructs
its `QF` output. Prove preservation of arity and canonicality in the private
algorithm and the conversion round trips, then derive `elim_sound`. A raw
kernel entry point validates arity, canonicalizes, and rejects malformed
input before elimination; its soundness theorem refers to the decoded input.
The wrapper discharges the public theorem's validation obligation.
The implementation and degree checks reduce over the list kernel form from
[HexMvPoly.Kernel](../../HexMvPoly/Kernel.lean), using `decide +kernel`, never
`native_decide`. The certificate APIs use the same validated boundary.
The completeness contract for eligible inputs is successful exact elimination
given sufficient budget, without claiming a bound independent of output size.

The compiled certificate route separates two types of claims:

| Checker | Headline theorem |
| --- | --- |
| `checkElim φ ψ cert` | Acceptance implies `∀ρ, ψ.toProp ρ ↔ ∃x, φ.toProp (append ρ x)` (`checkElim_sound`). |
| `checkRefute φ cert` | Acceptance implies `∀ρ, ¬∃x, φ.toProp (append ρ x)` (`checkRefute_sound`). |

The producer chooses order, proposed test points, polynomial identity data,
and output. The checker regenerates the required canonical test-point keys,
checks that every required point has a branch (or a checked impossible-guard
proof), binds each branch to the actual input atom, checks the coefficient
and radical identities, and applies the tables with their guards. A subset
of test points can demonstrate existence but cannot certify elimination or
refutation. Missing branches, altered comparisons, stale inputs, forged
coefficients, and unproved guards must be rejected. No hash, external CAS,
or compiled Boolean enters a theorem hypothesis as trusted evidence.
Certificates record point keys, per-atom coefficient/identity witnesses,
guard derivations, proposed output nodes, and rewrite/refutation traces.
Replay still enumerates the complete set; it replaces search for arithmetic
expressions and simplifications with identity and rule checking. It makes no
claim to avoid polynomial arithmetic or exhaustive coverage in the kernel.

For `checkElim`, output is the exact disjunction reconstructed by these rules.
Its exact rewrite trace permits polynomial normalization, constant folding,
comparison scaling by a checked nonzero rational (reversing order if negative),
and guard-local polynomial rewrites `p-q = Σ hᵢ*gᵢ` under explicit equalities
`gᵢ=0`. The latter are checked polynomial identities, proving equality of
values and hence equivalence of every comparison under the guard. A guard
may never be inferred from a sibling disjunct. Prove each rewrite once.

After these rewrites, a budgeted kernel truth-table checker may prove
propositional equivalence: assign each distinct normalized polynomial one
of the three signs, interpret all six comparisons by that sign, and check
both formulas agree for every sign assignment. Real trichotomy proves
soundness; dependence between distinct polynomials need not be decided.
This permits absorption and comparison complementation. The test can be
exponential and has its own node/step accounting. A producer may always
emit the unchanged exact output, avoiding this test. These are the permitted
exact rules; there is no generic semantic-equivalence oracle inside
`checkElim`. This route retains exactness through quantifier alternation.

For `checkRefute`, the only semantic simplification extension is a checked
**weakening** `D → W` of each disjunct; a refutation of `W` then refutes `D`.
Permitted traces project conjuncts, fold constants, or replace conjuncts by
checked consequences. Normalize inequality premises to `pᵢ≥0` or `pᵢ>0`
by negating polynomials for the opposite orientation. Check the identity
`q = Σ λᵢ*pᵢ + Σ μⱼ*eⱼ`, with `eⱼ=0` the equality premises and every
`λᵢ≥0`. This proves `q≥0`. A strict conclusion additionally requires a
strict premise with a **strictly positive** multiplier. Equality multipliers
`μⱼ` are arbitrary; polynomial inequality multipliers need separately
checked sign evidence under the same branch assumptions. A `≠` premise is
rejected by this rule; a prior checked split into `<` or `>` may expose
usable signed premises. Missing orientation or sign evidence is rejection.

The reference refutation checker first computes verified NNF, with negation
absorbed into comparisons. DAG nodes are immutable: a branch-local rewrite
copies the affected occurrence and its path, preserving other incoming
edges. This also applies to guard-local exact rewrites. A global replacement
requires an unconditional implication valid at every occurrence and, if
Boolean negations are retained, positive polarity along **every** path to
the replaced node. Checking only the currently visited path or its local
assumptions is insufficient. Dropping a disjunct is not weakening.

Core refutation leaves use checked constant contradictions, incompatible
sign comparisons on the same normalized polynomial, or the preceding
linear-combination rule deriving a negative constant as nonnegative (or a
nonpositive constant as strictly positive). Compound branches are checked by
budgeted propositional decomposition; full coverage is required. Additional
existential elimination of remaining parameters recurses through the same
checker, with a decreasing variable count. An unfinished branch rejects the
certificate. RCF leaf proofs are composed in the Mathlib tactic through the
adapter, not trusted as an unchecked Boolean in the core `checkRefute`.

Dolzmann–Sturm equivalence-based simplification guides the **untrusted
search only**. There is no trusted call to that simplifier. Even a
mathematically valid simplification needs a supported proof trace to affect
the checked result. A weakening certificate cannot be reused as a QE
equivalence, passed through negative polarity, or used to prove an
existential by proving its weaker output. For a universal goal the tactic
may instead refute its existential negation, checking every disjunct.
If a weakened refutation does not finish, retry the exact route within the
remaining budget or decline; it is not a `false` verdict.

## Composition and tactic surface

`qe : Prenex n → Budget → QeOutcome n` has constructors
`success (ψ : QF n)` and `residual (p : Prenex n) (reason : Reason)`.
It recursively eliminates the innermost quantifier. Existentials use `elim`;
universals use `¬ elim (nnf (¬φ))`.
Each step is an equivalence for **all** remaining parameter valuations.
Recompute degrees after every step. Equal adjacent quantifiers may be
permuted with a proof and explicit coordinate maps; never commute an
existential across a universal. Compositional rewriting of an innermost
quantified frontend subformula uses the same exact theorem before global
prenex conversion, particularly for biconditionals.

A stalled computation returns `residual p reason`; if no progress was made,
`p` is the original input. Both constructors are computational data. The
companion proves `qe_correct` for success and `qe_residual` for residuals:
`qe input budget = residual p reason → ∀ρ, p.toProp ρ ↔ input.toProp ρ`.
The tactic reconstructs this equivalence (from reflection or accepted step
certificates), retaining the parameter map; it does not label a residual a
quantifier-free answer. Degree above two after substitution is expected.
Hand a single remaining quantified coordinate with no symbolic parameters to
RCF, even above degree two; the adapter and sentence-equivalence obligations
are specified in [hex-real-formula](hex-real-formula.md#relation-to-hex-rcf).
Evaluate `QF 0` by exact rational arithmetic in the kernel. A parameterized
`QF n` is an exact QE output, not a closed decision.

Future CAD may consume any residual with the same equivalence contract.
Coverings may consume an existential refutation problem in their supported
fragment; they cannot replace arbitrary quantifier alternation. Until those
providers exist, fall-through returns a diagnostic and leaves the goal open.
No runtime dependency on Redlog or Isabelle is introduced.

The companion exposes:

- `virtual_subst`: prove a supported real-arithmetic goal, optionally using
  explicitly selected hypotheses, by exact reflection initially and by
  certificate replay when available. Free real locals remain parameters
  in equivalence theorems; a proof tactic may explicitly universally close
  them, preserving dependencies and the selected assumptions as antecedents.
- `virtual_subst?`: the same checked proof attempt with a suggested invocation
  and a route/size report; it is not a counterexample prover.
- `virtual_subst (mode := reflect)` and `(mode := certificate)`: explicit
  proof routes; `maxSteps`, `maxNodes`, `maxTerms`, and `maxReplay` budgets
  are separate from Lean's heartbeats. Default mode is reflection until the
  certificate route is implemented and validated.
- A meta-level QE API returning the output and source equivalence, for
  downstream tactics that need formulas rather than goal closure.

Diagnostics name the stage, variable, offending atom and degree, remaining
prefix, and consumed budget. Stable reasons include `degreeExceeded`,
`nonPolynomial`, `unsupportedBinder`, `symbolicDenominator`,
`symbolicResidue`, `nodeBudget`, `termBudget`, `replayBudget`,
`certificateRejected`, and `backendUnavailable`. As a **tactic surface
policy**, a closed computation of `false` is diagnostic only, following
[hex-rcf](../../HexRCF/SPEC/hex-rcf.md): neither tactic closes the goal or emits
an automatic proof of its negation. Unlike RCF's one-sided decision contract,
the exact QE and reification equivalences here do mathematically support
transporting a verified false result to a negation proof. That fact is
available through the equivalence API; it does not change the tactic policy.
Failure to refute a weakening is unknown, not false. Tactic failure leaves
the original goal intact.

## Design sanity checks

These are implementation acceptance examples and mathematical checks of the
rules, not claims of tactic support already present.

1. `∀ x y : ℝ, x²+y² ≥ 2*x*y`. Commute the universal binders to eliminate
   `x` first, or eliminate `y` symmetrically. Refute `(x-y)²<0`. The
   discriminant is zero; at the repeated root `x=y`, `q=0`; immediately to
   its right `q'=0` and `q''=2>0`; at `−∞` the leading coefficient is
   positive. Every counterexample branch is false, for every `y`.
2. `∀ a b c : ℝ, (∃ x, a*x²+b*x+c=0) ↔
   (a=0 ∧ (b≠0 ∨ c=0)) ∨ (a≠0 ∧ b²-4*a*c≥0)`.
   Eliminate the displayed existential as a subformula, keeping `a,b,c`
   free. The quadratic guard supplies exactly the discriminant condition;
   the linear guard supplies a root regardless of `c`; when `a=b=0`,
   the infinity branch reduces to `c=0`. Root-plus-ε equality contributes
   no extra nonconstant roots. Guard-local identities simplify the linear
   root value `a*c²` using `a=0`. The exact output is
   `(a≠0 ∧ D≥0) ∨ (a=0 ∧ b≠0) ∨ (a=0 ∧ b=0 ∧ c=0)`.
   After rewriting the existential by its equivalence, close the remaining
   equivalence to the stated right-hand side with the sign truth-table
   checker (Boolean absorption), then universally close parameters.
   Test both signs of `a`, all three signs of the discriminant, and
   `a=b=c=0` separately.
3. `∀ ε : ℝ, ε>0 → ∃ δ : ℝ, δ>0 ∧ 2*δ<ε`. In `δ`, boundaries are `0`
   and `ε/2`; at `0+ε'` the derivative signs give `δ>0` and `2*δ-ε<0`
   exactly when `ε>0`. Use the quantified-subformula route: the existential
   alone eliminates to `ε>0`, and the implication is a tautology. A fixture
   using the global prenex route instead retains the `ε≤0` alternative and
   eliminates the guarded matrix to `True`. The formal `ε'` is distinct
   from the real bound variable `ε`; no fixed rational choice for it is sound.
4. `∀ y : ℝ, ∃ x : ℝ, x³=y`. The innermost atom has degree three in `x`
   with a remaining symbolic parameter `y`. Return `degreeExceeded`
   (`variable=x`, `degree=3`, `bound=2`); the RCF adapter is ineligible.
   Report `backendUnavailable` if the caller requests a CAD fallback.
   Contrast `∃ x : ℝ, x³=2`, which may take the univariate RCF path.

## Complexity and Phase 4

Let `L` be the matrix's expanded Boolean tree size and `m≤L` its number of
distinct normalized atom polynomials. Each table replaces an atom by at most
a fixed constant number `C` of atoms. Without DNF or heuristic simplification,
one elimination has structural bound
`L' ≤ C*(6*m+1)*(L+1)`, with guards included by enlarging `C`.
Therefore `L'=O(L²)` and repeated successful eliminations satisfy
`L_k ≤ (C'*(L_0+1))^(2^k)` for a fixed constant `C'`. This is a conservative
upper bound, not a prediction for every family. Quantifier count alone is
not a useful runtime bound. DAG sharing may help execution but does not
justify reporting a smaller expanded formula bound.

The polynomial work is additional. If every input coefficient `a,b,c` has
degree at most `d` in a remaining coordinate, the displayed finite-root
rules have `deg D≤2d`, `deg U≤3d`, `deg V≤2d`, and
`deg(U²-V²D)≤6d`; derivative and infinity rules obey the same conservative
`6d` bound. Thus even a biquadratic input can produce atoms beyond quadratic
in the next coordinate. Term counts and coefficient bit lengths can grow
through sparse products and squaring; express cost using measured operand
sizes and the underlying polynomial arithmetic, never unit-cost integers.
A certificate can save search in the kernel but does not promise small
replay or eliminate the coverage obligation.

The Phase-4 compiled track benchmarks coefficient extraction, test-point
generation, atom substitution, `elim`, `qe`, both certificate checkers and
the producer. Use independent one-parameter ladders:

| Axis | Input family and observation |
| --- | --- |
| Atoms | Increasing distinct affine/quadratic boundaries in one eliminated variable; include symbolic leading coefficients and repeated roots. Record generated versus active points and output nodes. |
| Variables | Chains of linear inequalities with increasing prefix length, then independent quadratic blocks; fixed small atom count per block. Record each elimination's input/output size. |
| Degree growth | `x²+y²=0 ∧ x+y²=0` produces the condition `y⁴+y²=0`; vary parameter exponents/monomial support, and measure the later degree refusal separately from successful runs. |
| Arithmetic | Fix syntax and vary coefficient bit length, arity, and sparse coefficient support independently. Report normalization and polynomial-replay costs. |
| Boolean structure | Conjunctions, disjunctions, and alternating Boolean nesting; compare tree versus DAG counts and exact versus weakened-refutation traces. |

Give each compiled operation an independently derived family complexity
claim under [benchmarking](../benchmarking.md); use a one-sided bound where
output growth prevents a sharp model. Compare reflection's compiled core
and certificate production/checking on identical exact-output cases;
refutation timings are a separate group. Redlog and exported Isabelle are
external comparators on their common supported inputs, with pinned settings,
outputs, and unsupported outcomes retained. Reification, proof emission,
`decide +kernel` replay, RCF composition, and tactics use fresh-module
`lake build` probes with matched baselines under [Phase 4](../../PLAN/Phase4.md).
Keep Mathlib out of compiled bench imports. Record shared-host activity,
automatically selected CPU affinity, all completed samples, and the policy's
trial-major schedule; no quiet-host filtering or retry-until-clean runs.

## Conformance and oracle protocol

Use versioned JSONL fixtures with the formula schema from hex-real-formula,
elimination coordinate, requested route, budgets, expected result kind,
exact output formula for QE or a refutation trace for refutation, and
certificate data when applicable. Store integers exactly and
include seed and tool versions. `core` covers every comparison at all three
point kinds, linear/constant degenerations, both signs of denominators,
`D<0`, `D=0`, `D>0`, coincident roots, identically zero polynomials, vacuous
binders, alternation, and the four acceptance examples. Include negative
certificates: omitted linear branch, missing guard, wrong radical identity,
reversed inequality, strengthened disjunct, and changed input digest/data.

The independent oracles are Redlog in open-source REDUCE and AFP's exported
SML code. Use `load_package redlog; rlset ofsf;` followed by `rlqe` on closed
fixtures, and on the universal closure of `input ↔ output` for **exact**
parameterized QE fixtures. A parameterized refutation fixture instead checks
`∀ params, ¬∃x φ`; for a weakening step check `∀ params, D → W` and the
claimed refutation of `W`. Never demand `D ↔ W`. Replay-budget refusals
and unsupported inputs are separate outcomes, not oracle truth values.
Pin REDUCE revision and all switches; reject a still-quantified or timed-out
answer as unsupported/exhausted, never as false. See the
[rlqe contract](https://www.redlog.eu/documentation/service.php?key=rlqe).

Build the SML export from a pinned Isabelle/AFP release using
[Exports](https://isa-afp.org/browser_info/current/AFP/Virtual_Substitution/Exports.html)
(`VSGeneral`, `is_quantifier_free`, and exact rational constructors), recording
the SML compiler and driver revision. Check variable order, comparisons, and
rational encodings with hand-computed fixtures before cross-checking. Compare
closed decisions only when the export fully solves the input; for open exact
outputs, compare rational specializations and ask Redlog to decide the
universally closed equivalence. Different formula text is not a mismatch,
and finite sampling is not an equivalence proof. The Isabelle export is an
independent conformance oracle, not a Lean trust dependency.

Under [testing](../testing.md), both external components are `if_available`
in `ci` and `required` for the pinned `local` acceptance campaign; `core`
uses committed expected outcomes and kernel proofs. Record skips explicitly.
Extend the existing oracle runner and single CI job when implementing these
tests, following [CI](../CI.md); do not add a job or matrix per oracle.
Bound CI fixtures; retain larger growth cases for local runs. Every mismatch
must retain full input, output, certificate, and settings for replay.

## Manual and extensions

The manual presents the squared-difference proof, the parameterized quadratic
root criterion, and the positive-δ example, explaining guards and the
right-hand interval meaning of ε. Show a degree refusal and its residual
formula, an RCF fast path, and a deliberately rejected certificate. Separate
an exact QE result from a refutation-only weakening.

Cubic substitution is a stated extension, following Weispfenning (ISSAC
1994) and Košta's 2016 thesis, including root descriptions/Thom encodings,
degenerations, clustering, and a new completeness theorem and rule tables.
It must revise the degree and complexity contracts and gain independent
fixtures before the tactic accepts degree three. It is not enabled by
silently increasing the quadratic degree check. Relation-sensitive test
points, local guard pruning, and broader real-closed-field semantics are
separate proved improvements to the reference design.

## References

- Loos–Weispfenning, [Applying Linear Quantifier Elimination](https://doi.org/10.1093/comjnl/36.5.450), 1993.
- Weispfenning, [Quantifier elimination for real algebra—the quadratic case and beyond](https://doi.org/10.1007/s002000050055), AAECC 1997.
- Weispfenning, [Quantifier elimination for real algebra—the cubic case](https://doi.org/10.1145/190347.190425), ISSAC 1994.
- Košta, [New Concepts for Real Quantifier Elimination by Virtual Substitution](https://publikationen.sulb.uni-saarland.de/bitstream/20.500.11880/26735/1/mkosta_dissertation.pdf), Saarland thesis, 2016.
- Dolzmann–Sturm, [Simplification of Quantifier-Free Formulae over Ordered Fields](https://doi.org/10.1006/jsco.1997.0123), JSC 1997.
- Scharager–Cordwell–Mitsch–Platzer, [Verified Quadratic Virtual Substitution for Real Arithmetic](https://doi.org/10.1007/978-3-030-90870-6_11), FM 2021, and the AFP theories linked above.
- Nipkow, [Linear Quantifier Elimination](https://www21.in.tum.de/~nipkow/pubs/jar10.html), JAR 2010.
- [Decision-procedure alignment analysis](../../reports/decision-procedures-alignment.md#weispfenning-virtual-substitution).
