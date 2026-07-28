# hex-mv-poly (computable multivariate polynomials, depends on hex-poly)

Multivariate polynomials in a fixed number of variables, with a
distributed representation keyed on exponent vectors, canonical form,
and arithmetic that reduces in the kernel. Mathlib-free; the companion
`hex-mv-poly-mathlib` supplies `aeval` and the ring equivalence with
`MvPolynomial (Fin n) R`.

## Why this library exists

A Mathlib-free multivariate polynomial type, with a Mathlib companion
supplying the correspondence. Two consumers drive the design. A third
input, the public surface of the existing implementations under
"Relationship to existing implementations", sets the capability bar the
API has to clear.

**The `sos` tactic.** [leanprover/sos](https://github.com/leanprover/sos)
implements Harrison's sum-of-squares decision procedure. Its
multivariate polynomial substrate depends on Mathlib, so `sos` inherits
a Mathlib dependency it does not otherwise need. This library removes
that.

Worth being precise about what that does and does not buy, because the
two steps are easy to conflate. It makes `sos` Mathlib-free apart from
its own statement layer, which is worth having on its own. It does not
by itself make `sos` admissible in Mathlib, since Mathlib cannot depend
on Hex either. The path is: migrate `sos` externally first, then either
upstream the core representation and the correspondence layer, or vendor
them as part of upstreaming `sos`. This SPEC serves the first step and
keeps the second possible.

The polynomial surface `sos` needs is small and entirely within scope:
ordered monomial iteration (`monomials`, `toList`, `support`, all used
as `for` sources), `coeff`, `totalDegree`, `monomial`, `C`, `X`, the
ring operations, `bind₁`, `BEq`, `Inhabited` on monomials, and `aeval`
with its homomorphism lemmas. The certificate check is a polynomial
identity on canonical forms, decided in the kernel. Everything except
`aeval` and the homomorphism lemmas belongs in the Mathlib-free layer.

The audited surface, with use counts, is under "Consumer surfaces"
below. Acceptance is two separate criteria: the `sos` search and
certificate code builds against the core, and the `sos` verifier builds
against the companion with its existing kernel certificate checks
passing unchanged.

**Later Hex work.** Multivariate gcd and squarefree decomposition,
multivariate factorization, Gröbner bases, rational-expression tactics,
and cylindrical algebraic decomposition all sit on this type. See
[future-work](../future-work.md).

## Representation

```lean
namespace Hex

/-- Exponent vector for `n` variables. -/
abbrev Mono (n : Nat) := Vector Nat n

/-- A multivariate polynomial in `n` variables over `R`, as a map from
exponent vectors to nonzero coefficients, ordered by `cmp`. -/
structure MvPoly (n : Nat) (R : Type*) [Zero R]
    (cmp : Mono n → Mono n → Ordering) [TransCmp cmp] where
  terms : Std.ExtTreeMap (Mono n) R cmp
  nonzero : ∀ (m : Mono n) (c : R), terms.get? m = some c → c ≠ 0
```

The binder types on `nonzero` are load-bearing: written as `∀ m c,
terms[m]? = ...` the `GetElem?` instance is stuck on a metavariable and
the declaration does not elaborate. `Vector Nat n` has a `TransCmp`
instance for `compare`, so the default lexicographic order is available
without extra work.

Fixed arity `n : Nat` with `Fin n`-indexed variables, matching what
every identified consumer uses. The Mathlib equivalence is therefore
`MvPoly n R cmp ≃+* MvPolynomial (Fin n) R`. A general index type would
have to carry an ordered finite encoding of itself through every
algorithm, and no consumer wants it.

`Std.ExtTreeMap` rather than a sorted array or list, for three reasons.
Ordered iteration gives the leading term in the monomial order, which
every algorithm above the ring operations needs. Extensionality comes
with the type, so two polynomials with equal key-value sets are
propositionally equal and the canonical form condition reduces to "no
zero values". And it does reduce in the kernel, contrary to the
folklore; see "Kernel reduction" below for what has and has not been
established.

The `nonzero` field makes the representation canonical: every
polynomial has exactly one representation. Operations restore it by
construction, using `ExtTreeMap.alter` to delete a key whose
coefficient cancels rather than storing an explicit zero. The
equivalent and slightly simpler invariant `∀ m, terms.get? m ≠ some 0`
is worth preferring.

Equality does not come for free and must be written by hand. `deriving
DecidableEq` fails on a structure with a proof field, so the instance
compares `terms` only and recovers structure equality by proof
irrelevance. The path it compares through matters under the module
system: `HexPoly/Dense.lean` already documents that
`Array.instDecidableEq` delegates its nonempty case to a
non-`@[expose]` implementation whose body is unavailable downstream, so
`decide` and `rfl` on `DensePoly` equalities got stuck until the
instance was rerouted through `List` equality (see
`progress/lean4-array-decidableeq-module-repro.md`). `Mono n` is
`Vector Nat n`, which wraps an `Array`, so this library is exposed to
exactly the same hazard and the chosen instance has to be benchmarked
under module mode rather than assumed to reduce.

## The monomial order is an explicit argument

`cmp` is a parameter of the type, not a typeclass. A monomial admits
many orders and none of them is canonical, so a typeclass would be
resolving something that has no canonical answer, and instances would
have to be kept local to stop callers losing track of which order is in
scope. Algorithms need to change order on the same underlying type
anyway: grevlex for Gröbner-basis computation, lex for elimination.

`Std.ExtTreeMap` already takes its comparator as an explicit argument,
so this costs nothing at the container level. It does mean that `+`,
`*`, and the ring instances are stated for a fixed `cmp`, and that a
change of order is a function `reorder : MvPoly n R cmp → MvPoly n R
cmp'` with a proof that it preserves `coeff`.

**Comparator laws come in three strengths, and the SPEC needs all
three.**

`TransCmp cmp` is what `ExtTreeMap` requires to be a map at all.

`LawfulEqCmp cmp` is what makes it the *right* map. `ExtTreeMap` treats
`cmp a b = .eq` as key identity, so a merely transitive comparator may
identify distinct exponent vectors, silently merging `coeff a p` and
`coeff b p` and falsifying the equivalence with
`MvPolynomial (Fin n) R`. Every comparator appearing anywhere in this
library, including the target comparators of `reorder`, `rename`, and
`toUnivariate`, carries it. `Std` supplies both classes for `compare`
on `Vector Nat n`, so plain lexicographic order costs nothing.

`IsMonomialOrder cmp` is what leading-term algorithms need, and it is
strictly more than a faithful total order:

```lean
class IsMonomialOrder {n : Nat} (cmp : Mono n → Mono n → Ordering) : Prop where
  trans      : Std.TransCmp cmp
  faithful   : Std.LawfulEqCmp cmp
  zero_le    : ∀ m, cmp 0 m ≠ .gt
  add_mono   : ∀ a b c, cmp a b = cmp (a + c) (b + c)
  wf         : WellFounded (fun a b => cmp a b = .lt)
```

Multiplication compatibility and well-foundedness are what make
multivariate division terminate and normal forms unique, so Gröbner
work and `leadingTerm` require this class while storage-only operations
require only the first two. Supply named `lex`, `grlex`, and `grevlex`
comparators with their orientation documented, each with an
`IsMonomialOrder` instance.

## The monomial API

`Mono n` is not just a key type: Gröbner work, factorization, and the
recursive view all compute with exponent vectors directly, and those
operations should be specified here rather than improvised downstream.

```lean
namespace Hex.Mono

def zero : Mono n                                   -- the constant monomial
def unit (i : Fin n) : Mono n                       -- xᵢ
def mul (a b : Mono n) : Mono n                     -- pointwise addition
def dvd (a b : Mono n) : Bool                       -- pointwise ≤
def div (a b : Mono n) : Option (Mono n)            -- exact quotient, none if ¬ dvd
def lcm (a b : Mono n) : Mono n                     -- pointwise max
def gcd (a b : Mono n) : Mono n                     -- pointwise min
def degree (m : Mono n) : Nat                       -- total degree
def degreeOf (i : Fin n) (m : Mono n) : Nat
def support (m : Mono n) : List (Fin n)
```

`mul` is the monoid operation the `add_mono` field of `IsMonomialOrder`
refers to, so the class and this API have to agree on it; state
`IsMonomialOrder` in terms of `Mono.mul` rather than a bare `+`. The
laws worth naming are that `dvd` agrees with the existence of an exact
quotient, that `div` is a left inverse of `mul` on the divisible case,
`degree_mul`, and the `lcm`/`gcd` lattice laws, all of which the
S-polynomial construction uses.

## Kernel reduction

The tactic consumers (`sos`, and anything in the `factor_poly` family
that grows a multivariate arm) check certificates with `decide +kernel`.
The representation therefore has to reduce in the kernel, not merely
compile.

The received view is that `ExtTreeMap` does not reduce in the kernel,
and that a sorted list is needed for kernel work. A first experiment
(`scratch-mvpoly-bench/`) checks `p^(2k) = p^k · p^k` for
`p = 1 + x₀ + x₁ + x₂` by `decide +kernel`, against a minimal
implementation of each representation, with an import-only baseline of
0.24s:

| identity | `ExtTreeMap` | sorted `List` | ratio |
|---|---|---|---|
| `p⁴ = p² · p²` | 1.38s | 1.83s | 1.3× |
| `p⁶ = p³ · p³` | 6.17s | 14.04s | 2.3× |
| `p⁸ = p⁴ · p⁴` | 24.41s | 74.47s | 3.1× |

The one conclusion this supports is that **`ExtTreeMap` reduces in the
kernel at all**, which refutes the strong form of the folklore and is
enough to keep it as the candidate representation. It does not support
"`ExtTreeMap` is faster", and it does not yet clear `ExtTreeMap` for
production kernel replay. Four gaps stand between the two:

- **Module mode.** The experiment is a legacy non-`module` file, while
  Hex is a module-system project. Exposure is exactly what determines
  downstream kernel reduction here, as the `DensePoly` `DecidableEq`
  story above shows. The rerun must use `module`, `public import`, and
  the intended `@[expose]` closure, with the checker in a separate
  downstream module.
- **A handicapped opponent.** The list side inserts linearly for
  addition and for every product term. Sorted-list addition should be a
  linear merge, and multiplication should merge translated rows or
  produce-sort-combine. The current comparison sets a tree's natural
  algorithm against a deliberately weak list algorithm, so the ratios
  overstate the gap by an unknown factor.
- **The wrong types.** The experiment uses `Array Nat` keys, `Int`
  coefficients, bare containers, and list equality after converting the
  tree. Production means `Vector Nat n`, the `nonzero` wrapper, the
  hand-written `DecidableEq`, and `ℚ`, which this SPEC separately
  identifies as the likely bottleneck.
- **A single friendly workload.** Powers of `1 + x₀ + x₁ + x₂` have
  dense simplex support, high collision rates, and no cancellation,
  which favours logarithmic point updates and penalises linear
  insertion. A fair suite needs disjoint and interleaved addition, low-
  and high-collision multiplication, cancellation-heavy identities,
  sparse random supports, rename and substitution collisions, and real
  SOS certificate identities, across varying arity, degree, and order.

Methodology should also improve: the table is one wall-clock run per
case, with no hardware record, repetition, spread, memory, or heartbeat
counts. Ideally the rerun also measures the actual CompPoly and
`MvSparsePoly` implementations rather than proxies.

Phase 4 carries this as a bench target with separate kernel and native
suites. A second, kernel-specialised representation is justified only
if that bench shows one is needed, and the threshold should be written
down in advance; the `PolyOps`-style abstraction in
[future-work](../future-work.md) is where it would attach.

## Kernel exposure

`hex-mv-poly` is a kernel-facing library, so exposure is part of the
design rather than an afterthought. Two concrete constraints follow from
`Mono n = Vector Nat n`, both discovered the hard way elsewhere in this
tree and recorded in
`progress/lean4-array-decidableeq-module-repro.md`.

**Equality.** `Vector`'s `DecidableEq` is derived, and derived instances
are opaque across a module boundary under the module system, so
`decide` on monomial or polynomial equality stalls. `HexBasic.ArrayDecEq`
supplies replacement instances that route through `List`. This library
imports it, which means **hex-mv-poly depends on hex-basic**.

**Construction.** `X i` naturally builds its exponent vector with
`Vector.ofFn`, which delegates through the unexposed `Array.ofFn.go` and
does not reduce. Use `Hex.Vector.ofFn'` from `HexBasic.OfFn` instead.
This is exactly the trap CompPoly's `X` falls into, since it is defined
with `Vector.ofFn`.

Both are shims for [leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270)
and disappear when it lands.

The kernel replay closure is everything a certificate check touches:
`Mono` operations, the comparator, `ExtTreeMap` lookup and `alter`,
addition, multiplication, and the equality instance. Each is `@[expose]`,
and a downstream module must carry a `decide +kernel` test that would
fail if any of them stopped reducing. Anything outside that closure
(`totalDegree`, `vars`, pretty-printing, the recursive view) does not
need exposure and should not pay for it.

Operations whose kernel-friendly shape differs from the fast shape carry
a `@[csimp]` pair, as `Hex.Array.ofFn'` does. Multiplication is the
likely candidate: the scratch-accumulator version below is the one to
compile, and a simpler fold may be the one to reduce.

## Algorithms and complexity

Complexity is in terms of the term counts `s = p.termCount` and
`t = q.termCount`, arity `n`, and the cost of one coefficient
operation. Monomial comparison is `O(n)`, which is not constant and
shows up in every tree operation.

| operation | algorithm | cost |
|---|---|---|
| `coeff` | `ExtTreeMap.get?` | `O(n log s)` |
| `monomial`, `C`, `X` | single insert | `O(n)` |
| `add` | fold `alter` of the smaller into the larger | `O(n · t log (s+t))` |
| `neg`, scalar multiple | map over values | `O(s)` |
| `mul` | Gustavson-style: for each term of `p`, translate every term of `q` and accumulate into one output map | `O(n · s · t · log (s·t))` |
| `leadingTerm` | max entry in `cmp` order | `O(log s)` |
| `reorder` | rebuild under the new comparator | `O(n · s log s)` |
| `rename` | rebuild, combining collisions | `O(n · s log s)` |
| `eval` | Horner over the recursive view, or direct term sum | `O(s · n)` coefficient ops |
| `toUnivariate` | partition by the main variable's exponent | `O(n · s log s)` |

Multiplication is the one to fix now rather than defer, per design
principle 7. The chosen algorithm is the accumulate-into-one-map form
above rather than repeated pairwise `add`, because the latter rebuilds
intermediate maps `s` times. The threshold that would justify revisiting
it is a bench showing sparse inputs where the output support is much
smaller than `s · t`, in which case a heap-merge over translated rows
becomes competitive.

## API

The Mathlib-free layer:

```lean
-- Construction
def C (c : R) : MvPoly n R cmp
def X (i : Fin n) : MvPoly n R cmp
def monomial (m : Mono n) (c : R) : MvPoly n R cmp
def ofTerms (ts : List (Mono n × R)) : MvPoly n R cmp

-- Ring operations (instances: Zero, One, Add, Sub, Neg, Mul, Pow)
-- with `nonzero` restored by construction

-- Queries
def coeff (m : Mono n) (p : MvPoly n R cmp) : R
def support (p : MvPoly n R cmp) : List (Mono n)
def totalDegree (p : MvPoly n R cmp) : Nat
def degreeOf (i : Fin n) (p : MvPoly n R cmp) : Nat
def vars (p : MvPoly n R cmp) : List (Fin n)
def leadingMono (p : MvPoly n R cmp) : Option (Mono n)
def leadingCoeff (p : MvPoly n R cmp) : R
def leadingTerm (p : MvPoly n R cmp) : Option (Mono n × R)

-- Evaluation
def eval (x : Fin n → R) (p : MvPoly n R cmp) : R
def evalHorner (x : Fin n → R) (p : MvPoly n R cmp) : R
def partialEval (s : Fin n → Option R) (p : MvPoly n R cmp) : MvPoly n R cmp

-- Structural
def derivative (i : Fin n) (p : MvPoly n R cmp) : MvPoly n R cmp
def homogeneousComponent (d : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp
def rename (f : Fin n → Fin m) (p : MvPoly n R cmp) : MvPoly m R cmp'
def reorder (p : MvPoly n R cmp) : MvPoly n R cmp'
def subst (f : Fin n → MvPoly m R cmp') (p : MvPoly n R cmp) : MvPoly m R cmp'
```

The signatures above elide their typeclass bounds, and the elision
hides a real requirement: `[Zero R]` alone is not enough for any
operation that has to drop a cancelled term. `C`, `monomial`,
`ofTerms`, addition, multiplication, and negation all need to decide
whether a coefficient is zero, so each carries `[DecidableEq R]` (or
`[BEq R] [LawfulBEq R]`) alongside the algebraic class it needs. Write
the real bounds per declaration rather than a single blanket variable
block.

Constructor and query contracts to state explicitly, since an
implementer will otherwise guess: `ofTerms` sums duplicate monomials
and drops zeros; `support` and every term iteration is ordered by
`cmp`; `totalDegree`, `degreeOf`, `vars`, and `leadingCoeff` have
stated values on the zero polynomial; and `rename`, `partialEval`, and
`subst` may merge terms, so all three combine coefficients and
renormalise.

Content and primitive part are deliberately *not* in this SPEC. The
coefficients in the recursive view are themselves multivariate
polynomials, so a gcd-domain hypothesis on `R` does not determine the
executable algorithm, and the operation belongs with the multivariate
gcd layer in [future-work](../future-work.md).

The backing map should not be public. Exposing `terms` invites exactly
the `p.1.toList` coupling that appears in SOS against CompPoly today
and would make any later representation change unrealistic. Export
`termsList`, `foldTerms`, `monomials`, and `termCount` with documented
ordering and complexity instead.

The recursive view is a separate face on the same data:

```lean
/-- Coefficients of `p` as a univariate polynomial in variable `i`,
with coefficients in the remaining `n` variables. -/
def toUnivariate (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n+1) R cmp) :
    DensePoly (MvPoly n R cmp')

/-- Inverse of `toUnivariate`, reinserting variable `i`. -/
def ofUnivariate (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (q : DensePoly (MvPoly n R cmp')) :
    MvPoly (n+1) R cmp
```

The main variable is `i : Fin (n+1)`, not `Fin n`: a polynomial in
`n+1` variables has `n+1` variables to choose from, and `Fin n` both
excludes the last one and makes the one-variable case `n = 0` have no
admissible index at all. The reindexing between the remaining `n`
variables and the original `n+1` is `Fin.succAbove i` and its partial
inverse, and the comparator on the remaining variables is an explicit
argument since nothing determines it from `cmp`.

Required theorems: coefficient characterisations in both directions,
both round trips (`ofUnivariate i cmp' (toUnivariate i cmp' p) = p` and
its converse), and the degenerate case `MvPoly 1 R cmp ≃+* DensePoly R`.

This is what multivariate gcd, resultants, and factorization recurse
on, and it is where hex-mv-poly meets hex-poly. Supply both directions
rather than making one view primary.

## Correctness theorems

`coeff` is the specification function: every operation is characterised
by what it does to coefficients, and the Mathlib companion transports
those characterisations rather than reproving anything.

```lean
theorem ext (h : ∀ m, coeff m p = coeff m q) : p = q
theorem coeff_zero      : coeff m 0 = 0
theorem coeff_C         : coeff m (C c) = if m = Mono.zero then c else 0
theorem coeff_X         : coeff m (X i) = if m = Mono.unit i then 1 else 0
theorem coeff_monomial  : coeff m (monomial m' c) = if m = m' then c else 0
theorem coeff_ofTerms   : coeff m (ofTerms ts) = (ts.filter (·.1 = m)).sum
theorem coeff_add       : coeff m (p + q) = coeff m p + coeff m q
theorem coeff_neg       : coeff m (-p) = -coeff m p
theorem coeff_mul       : coeff m (p * q)
                            = ∑ ab ∈ m.splits, coeff ab.1 p * coeff ab.2 q
theorem coeff_reorder   : coeff m (reorder p) = coeff m p
theorem coeff_rename    : coeff m (rename f p)
                            = ∑ m' ∈ {m' | m'.map f = m}, coeff m' p
theorem coeff_derivative : coeff m (derivative i p)
                            = (m.degreeOf i + 1) * coeff (m.succAt i) p
theorem eval_eq         : eval x p = ∑ m ∈ p.support, coeff m p * m.prod x
theorem evalHorner_eq   : evalHorner x p = eval x p
theorem toUnivariate_coeff, ofUnivariate_coeff
theorem toUnivariate_ofUnivariate, ofUnivariate_toUnivariate
```

`coeff_mul` is the convolution: `m.splits` enumerates the pairs
`(a, b)` with `Mono.mul a b = m`, which is finite because exponents are
bounded componentwise by `m`. Stating it this way keeps it decidable and
avoids a `Finsupp.antidiagonal` detour in the Mathlib-free layer.

Two invariant families are separate obligations and easy to forget.
Every constructor and operation preserves `nonzero`, and every operation
that can merge terms (`rename`, `subst`, `partialEval`, and `mul`)
combines coefficients rather than dropping one. The second is what a
naive implementation gets wrong, and it is not visible in the
coefficient laws above unless they are stated over all monomials rather
than over the support.

## The Mathlib layer

`hex-mv-poly-mathlib` proves:

```lean
def equiv : MvPoly n R cmp ≃+* MvPolynomial (Fin n) R

def aeval [CommSemiring S] [Algebra R S] (x : Fin n → S) :
    MvPoly n R cmp →ₐ[R] S
```

plus the homomorphism lemmas `aeval_add`, `aeval_mul`, `aeval_sub`,
`aeval_neg`, `aeval_pow`, `aeval_zero`, `aeval_one`, `aeval_C`, and
`aeval_X`. That list is what `sos`'s verifier uses today.

Two things the signatures above still need. `[CommSemiring R]` is
missing, and the `neg` and `sub` lemmas need ring rather than semiring
assumptions, so the lemma set splits by its real hypotheses. And
`aeval_eq_eval` cannot state the case `sos` actually needs: core `eval`
evaluates into `R` itself, whereas `sos` evaluates a `ℚ`-polynomial
into `ℝ`. The core layer therefore needs `eval₂` (and its Horner
variant), and the companion needs `aeval_eq_eval₂` rather than
`aeval_eq_eval`. The companion also owns the transported
`CommSemiring`, `CommRing`, and `Algebra R` instances on `MvPoly`.

Following the project split, no *mathematical* theorems about `MvPoly`
belong in the Mathlib layer. What does belong, beyond the bare ring
equivalence, is a correspondence lemma for each public semantic
operation: coefficients, evaluation, degree, derivative, rename,
substitution, and both directions of the recursive view. Without those
a caller cannot transport anything except a ring identity.

## Relationship to existing implementations

Three implementations exist, and this SPEC is written knowing all three.

**CompPoly** (`CMvPolynomial n R`, Verified-zkEVM) is the closest:
`ExtTreeMap` keyed on `Vector ℕ n`, wrapped in a `Lawful` nonzero
invariant. Differences here are that the monomial order is an explicit
argument rather than `class MonomialOrder (n : ℕ)`, and that the
computational layer carries no Mathlib dependency. Derek Sorensen has
said he is open to both changes.

Its public surface is the useful thing to take from it: a mature
multivariate library's declaration list is a better capability
checklist than anything derived from first principles, so this SPEC
treats matching it as a requirement and records the audit under
"Consumer surfaces". Whether CompPoly then retires its own module is
their call, not a goal of this SPEC. Two points of scope are worth
knowing when weighing that: ArkLib, CompPoly's principal downstream,
does not use the multivariate module at all (zero imports of
`CompPoly.Multivariate`, zero occurrences of `CMvPolynomial`; its
dependency runs through univariate `CPolynomial`, the multilinear `MLE`,
and the finite-field modules), and within CompPoly the module has
exactly two consumers, `Bivariate/CMvEquiv.lean` and
`Univariate/CMvEquiv.lean`, both reaching it only through
`finSuccEquiv` and `isEmptyRingEquiv`. So the capability bar is real but
the downstream footprint is small, and nothing here is on ArkLib's path;
anything aimed at ArkLib would target univariate and multilinear
polynomials, which is a different library.

**`MvSparsePoly R nvars`** (Michail Karatarakis, Mathlib PRs
[#41339](https://github.com/leanprover-community/mathlib4/pull/41339),
[#41348](https://github.com/leanprover-community/mathlib4/pull/41348),
[#41350](https://github.com/leanprover-community/mathlib4/pull/41350),
split from closed #41282/#41283) is a sorted list of
`(exponent-vector, coefficient)` pairs, canonical, with an `AlgEquiv` to
`MvPolynomial (Fin nvars) R` and the tactics `mv_decide`, `mv_compute`,
and `mv_mem`. Definitions by Mario Carneiro, prototype by James
Davenport, proofs by Claude. It is axiom-free and targets kernel
reduction specifically. The design agrees with this one on arity,
canonicality, and the shape of the equivalence, and differs on the
container. `mv_mem` decides ideal membership by multi-divisor normal
form, which is the shape the Gröbner item in
[future-work](../future-work.md) wants.

**`MonomialOrderedPolynomial`** (WuProver) builds
`SortedAddMonoidAlgebra` on `SortedFinsupp σ R cmp`, generic in the
index type and with the comparator explicit, aimed at identity testing
and at Gröbner bases in `WuProver/groebner_proj`. It agrees with this
SPEC that the comparator is an argument, and differs on the index type.

The Mathlib review of the Karatarakis series has stalled on a question
this design answers. The reviewers' concern is that reflection onto a
computable polynomial type only works when the coefficient type is
itself computable, and the proposal on the table is to scope tactics to
norm_num-able coefficients, or to follow Anne Baanen's suggestion of
proving `p : ℝ[X] = algebraMap ℚ[X] ℝ[X] p'` and computing in a
computable model of `ℚ[X]`. A Mathlib-free polynomial layer with a thin
Mathlib companion is what that plan needs underneath it. Coordination
should wait until this library exists and has been benchmarked against
both alternatives.

## Conformance

Fixtures follow the layout in [SPEC/testing.md](../testing.md): a JSONL
fixture and result stream, a Lean-side driver at
`conformance/HexMvPoly/EmitFixtures.lean` exposed as
`lean_exe hexmvpoly_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexMvPoly/mvpoly.jsonl`, and an oracle driver at
`scripts/oracle/mvpoly_sympy.py`. Adding it means appending one tuple to
`ORACLES` in `scripts/ci/run_oracles.sh`, not a new CI job:

```
"HexMvPoly|hexmvpoly_emit_fixtures|scripts/oracle/mvpoly_sympy.py|conformance-fixtures/HexMvPoly/mvpoly.jsonl"
```

A new fixture kind `mvpoly` carries the arity, the comparator name, and
the term list as `(exponent vector, coefficient)` pairs, so a record is
self-describing and records at different arities share one stream.

**Oracle choice.** SymPy's `Poly` covers arithmetic, degrees, evaluation,
substitution, and content over `ℚ` and `ℤ`, and is the right default
because it is already a project dependency pattern and its term
enumeration is order-explicit. Singular becomes the oracle when the
Gröbner layer arrives; it is not needed for this library. python-flint
covers multivariate polynomials only partially, so it is not the choice
here even though the rest of the polynomial stack uses it.

**Cases that must be present**, since these are what a plausible
implementation gets wrong:

- cancellation to zero, both in `add` and in `mul`, checking that no
  explicit zero coefficient survives;
- duplicate monomials passed to `ofTerms`, which must sum rather than
  overwrite;
- the zero polynomial and constants through every query
  (`totalDegree`, `degreeOf`, `vars`, `leadingCoeff`, `leadingTerm`);
- arity zero, where the only monomial is `Mono.zero`;
- non-injective `rename`, where distinct monomials collide and their
  coefficients must combine, including to zero;
- `subst` and `partialEval` producing collisions;
- `toUnivariate` and `ofUnivariate` at every main-variable position
  `i : Fin (n+1)`, including the first and last, with round trips;
- `reorder` between lex, grlex, and grevlex, checked by `coeff`
  agreement rather than by term order;
- monomial operations: `div` on the non-divisible case, `lcm` and `gcd`
  against pointwise max and min.

The companion adds randomised comparison against Mathlib's
`MvPolynomial (Fin n) R` through `equiv`, which is the strongest
available check and needs no external oracle.

## Benchmarking

Two suites, per [SPEC/benchmarking.md](../benchmarking.md), because the
two consumers stress different things and a single number would hide
both.

**Kernel suite.** `decide +kernel` on identities, reported as
elaboration wallclock. This is the suite that decides the
representation question left open under "Kernel reduction", so it must
run the production types (`Vector Nat n` keys, the real `DecidableEq`,
`ℚ` as well as `Int`) from a downstream module under the module system,
against both the `ExtTreeMap` form and a competently implemented sorted
form. Workload families: disjoint and interleaved addition,
low-collision and high-collision multiplication, cancellation-heavy
identities, sparse random supports, `rename` and `subst` collisions, and
real `sos` certificates. Vary arity, degree, term count, and comparator.

**Native suite.** Compiled throughput on the same families, which is
what CompPoly's consumers care about and what would justify retiring
their module.

**Comparators.** CompPoly and `MvSparsePoly` are the two that matter and
both are `informational` rather than required checks: they are
structurally different designs, and the point of measuring them is to
decide a design question rather than to hold a ratio. SymPy is not a
performance comparator.

**The threshold, written down in advance.** A second, kernel-specialised
representation is justified only if the kernel suite shows the sorted
form beating `ExtTreeMap` by more than 2× on at least two workload
families at the largest size that fits the bench time budget. Anything
less and the single representation stands.

Bench drivers live at `bench/HexMvPoly/Bench.lean`, and the kernel suite
belongs in the proof-probe family since it measures elaboration rather
than execution.

## File organisation

```
HexMvPoly/
  Mono.lean          -- Mono n, the monomial API, comparators, IsMonomialOrder
  Basic.lean         -- MvPoly, canonical form, BEq/DecidableEq, C/X/monomial
  Operations.lean    -- ring operations, coeff laws
  Query.lean         -- support, degrees, vars, leading term
  Eval.lean          -- eval, eval₂, Horner, partialEval
  Structural.lean    -- rename, reorder, subst, derivative, homogeneous parts
  Recursive.lean     -- toUnivariate, ofUnivariate, round trips
HexMvPoly.lean       -- umbrella
HexMvPolyMathlib/
  Equiv.lean         -- MvPoly n R cmp ≃+* MvPolynomial (Fin n) R
  Aeval.lean         -- aeval and its homomorphism lemmas
  Correspondence.lean-- coeff/eval/degree/rename/subst/recursive-view transport
HexMvPolyMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexMvPoly:
    deps: [HexPoly, HexBasic]
    mathlib: false
    done_through: 0
    status: draft
  HexMvPolyMathlib:
    deps: [HexMvPoly, HexPolyMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

`HexBasic` is a dependency for the reasons under "Kernel exposure", and
drops out when the upstream fix lands. `HexPoly` is needed for
`DensePoly` in the recursive view.

## Consumer surfaces

Generated from the current sources rather than read off by eye, since
the prose estimate understated both.

**`sos`** (`leanprover/sos` at the revision cloned for this SPEC), by
use count: `aeval` 66, `C` 25, `coeff` 22, `totalDegree` 21,
`monomials` 18, `toList` 15, `aeval_eq_eval` 9, `aeval_mul` 8,
`monomial` 7, `aeval_neg` 7, `X` 6, `eval` 5, `aeval_zero` 5,
`aeval_one` 5, `aeval_add` 5, `aeval_pow` 4, `aeval_sub` 3, `aeval_C` 3,
`support` 2, `bind₁` 1, `aeval_X` 1. Plus `Inhabited (CMvMonomial n)`,
which `SOS/EqElim.lean` and `SOS/Symmetry.lean` both declare locally, so
this library should provide `Inhabited (Mono n)` itself.

`totalDegree`, `monomials`, `toList`, and `support` together are the
iteration and query surface, and they are used in `for` loops rather
than incidentally, which is why term iteration needs a documented order
and complexity rather than being an afterthought.

**CompPoly's public multivariate surface**, taken as the capability
checklist: `C`, `X`, `monomial`, `coeff`, `ext`, `eval`,
`eval₂`, `evalHorner`, `aeval`, `bind`, `rename`, `support`,
`totalDegree`, `degreeOf`, `degrees`, `vars`, `leadingCoeff`,
`leadingMonomial`, `leadingTerm`, `restrictBy`, `restrictDegree`,
`restrictTotalDegree`, `npowBySq`, and the Horner-grouping machinery
(`HornerGroup`, `HornerTerm`, `hornerGroups`, `collectHornerGroups`,
`insertHornerGroupDesc`, `insertHornerTerm`, `sortHornerGroups`,
`evalSparseHornerGroups`, `hornerExponent`, `sumToIter`).

The `restrict*` family and the Horner grouping are the two blocks this
SPEC does not cover. `restrictDegree` and `restrictTotalDegree` are
straightforward filters and should be added. The Horner machinery is an
evaluation strategy rather than API, and whether it is worth porting is
a benchmark question.

Two further declarations are load-bearing and were missing from the API
above, because they are what CompPoly's own two internal consumers
actually call:

```lean
/-- Arity zero: the only monomial is `Mono.zero`. -/
def isEmptyRingEquiv : MvPoly 0 R cmp ≃+* R

/-- The recursive view as a ring equivalence, at the first variable. -/
def finSuccEquiv : MvPoly (n+1) R cmp ≃+* DensePoly (MvPoly n R cmp')
```

`finSuccEquiv` is `toUnivariate` at `i = 0` promoted to a ring
equivalence; the general-position `toUnivariate` is the more useful
form for Hex's own recursive algorithms, and `finSuccEquiv` should be
derived from it rather than defined separately. Both are required for
CompPoly's `Bivariate/CMvEquiv.lean` and `Univariate/CMvEquiv.lean` to
build against this library.

**What this evidence does and does not establish.** The tables above are
generated from the current sources, so they are reliable about which
declarations are called and how often. They are not a port: nothing has
been compiled against a stub of this API, signatures and instance
requirements have not been matched declaration by declaration, and the
`aeval` lemma set has not been checked against `sos`'s actual proof
obligations. The first implementation milestone should therefore be a
stub `MvPoly` with `sorry`-ed proofs that `sos` and the two CompPoly
equiv files are made to build against, before any algorithm work. That
is the cheapest way to convert this from a call-surface audit into
evidence.

## Before implementation

The design is settled: representation, comparator laws, the monomial
API, exposure, complexity, the operation set, correctness theorems,
conformance, benchmarking, file layout, and the consumer surfaces are
all above.

What remains is not SPEC work but decisions that want evidence:

1. **The coefficient question** under "Open questions". `ℚ` in the
   kernel is the plausible blocker for `sos`, and it is independent of
   everything here.
2. **The representation question**, which the kernel bench suite settles
   against the threshold written down under "Benchmarking".
3. **Whether to port CompPoly's Horner grouping**, which the native
   bench suite settles.

None of the three blocks starting implementation, and all three are
answered by work the SPEC already schedules.

## Open questions

- **Coefficient types.** The library is generic in `R`; CompPoly
  compatibility and the later Hex work both require that, so it is not
  in question. The open part is that `sos` needs `ℚ`, and Jovan
  Gerbscheid notes Lean has no `Rat` optimised for kernel reduction.
  Whether a kernel-friendly rational is needed alongside is a separate,
  separately benchmarked question, and it may well be the real blocker
  for tactic use rather than anything about the polynomial
  representation.
- **Sparse coefficients versus sparse exponents.** `Mono n` as a dense
  `Vector Nat n` is right for small `n`. Whether large `n` with few
  active variables wants a sparse exponent vector should be settled by
  the Gröbner and factorization benchmarks, not now.
- **Multiplication algorithm.** The benchmark above uses the naive
  double fold. Whether to accumulate output rows in a scratch structure
  (the multivariate analogue of Gustavson's algorithm) is a Phase 4
  question.
- **Relationship to `hex-poly`.** `toUnivariate` makes hex-mv-poly
  depend on hex-poly. Whether the dependency should instead run the
  other way, with `DensePoly R` a special case of the multivariate type,
  is worth a look, though the answer is probably no: the dense
  univariate representation is the right one for Berlekamp-Zassenhaus
  and should not pay for generality.
