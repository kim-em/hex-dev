# hex-mv-poly (computable multivariate polynomials, depends on hex-poly + hex-basic)

Multivariate polynomials in a fixed number of variables, with a
distributed representation keyed on exponent vectors, canonical form,
and arithmetic that reduces in the kernel. It is Mathlib-free. The companion
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
structure MvPoly (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [TransCmp cmp] [LawfulEqCmp cmp] where
  terms : Std.ExtTreeMap (Mono n) R cmp
  nonzero : ∀ (m : Mono n) (c : R), terms.get? m = some c → c ≠ 0
```

The binder types on `nonzero` are load-bearing: written as `∀ m c,
terms[m]? = ...` the `GetElem?` instance is stuck on a metavariable and
the declaration does not elaborate. `Vector Nat n` has a `TransCmp`
instance for `compare`, so that comparator remains available for
ordinary compiled use. The named `lex` order below deliberately uses
the exposed list route instead, because direct `Vector.compare` does not
reduce in downstream kernel replay.

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
zero values". The Phase 4 proof probes described below determine
whether this representation also meets the kernel-reduction budget.

Reusable map algorithms belong in `HexBasic/ExtTreeMap.lean`, in the
`Std.ExtTreeMap` namespace, with no Hex-specific types or polynomial
policy. That file is the designated upstream candidate. In particular,
joint ordered traversal and deletion-capable merge are map operations;
the coefficient-combination and zero-deletion policy passed to them
belongs in `HexMvPoly`.

The `nonzero` field makes the representation canonical: every
polynomial has exactly one representation. Operations restore it by
construction, using `ExtTreeMap.alter` to delete a key whose
coefficient cancels rather than storing an explicit zero. The
equivalent and slightly simpler invariant `∀ m, terms.get? m ≠ some 0`
is worth preferring.

Equality does not come for free. `deriving DecidableEq` fails on a
structure with a proof field, so the instance compares `terms` only and
recovers structure equality by proof irrelevance. It compares the
ordered term lists under `[DecidableEq R]`, then uses
`Std.ExtTreeMap.toList_inj` to recover map equality. Do not delegate to
the map's derived `BEq`: that routes through a different implementation
whose module-boundary reduction must not become part of the certificate
path.

This matters because `HexPoly/Dense.lean` already documents that
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
`toUnivariate`, carries it. `Std` supplies both classes for
`List.compareLex compare`; the named vector comparators still need
instances, proved by transporting those laws through `Vector.toList`.

`IsMonomialOrder cmp` is what leading-term algorithms need, and it is
strictly more than a faithful total order:

```lean
class IsMonomialOrder {n : Nat} (cmp : Mono n → Mono n → Ordering) : Prop
    extends Std.TransCmp cmp, Std.LawfulEqCmp cmp where
  zero_le  : ∀ m, cmp Mono.zero m ≠ .gt
  mul_mono : ∀ a b c,
    cmp a b = cmp (Mono.mul a c) (Mono.mul b c)
  wf       : WellFounded (fun a b => cmp a b = .lt)
```

Multiplication compatibility and well-foundedness are what make
multivariate division terminate and normal forms unique, so Gröbner
work and `leadingTerm` require this class while storage-only operations
require only the first two. Supply named `lex`, `grlex`, and `grevlex`
comparators with their orientation documented, each with an
`IsMonomialOrder` instance. The Mathlib-free layer must prove the three
named instances: lex is a finite lexicographic product of the
well-founded order on `Nat`, and the graded orders use the degree order
followed by their tie-breaker. The well-foundedness field is
mathematically derivable in greater generality from Dickson's lemma, but
keeping it in the class makes termination available to algorithms
without reproving it at each use.

## The monomial API

`Mono n` is not just a key type: Gröbner work, factorization, and the
recursive view all compute with exponent vectors directly, and those
operations should be specified here rather than improvised downstream.

```lean
namespace Hex.Mono

def zero : Mono n                                   -- the constant monomial
def unit (i : Fin n) : Mono n                       -- xᵢ
def mul (a b : Mono n) : Mono n                     -- pointwise addition
def scale (k : Nat) (m : Mono n) : Mono n           -- pointwise scaling
def dvd (a b : Mono n) : Bool                       -- pointwise ≤
def div (a b : Mono n) : Option (Mono n)            -- exact quotient, none if ¬ dvd
def lcm (a b : Mono n) : Mono n                     -- pointwise max
def gcd (a b : Mono n) : Mono n                     -- pointwise min
def degree (m : Mono n) : Nat                       -- total degree
def degreeOf (i : Fin n) (m : Mono n) : Nat
def support (m : Mono n) : List (Fin n)
def rename (f : Fin n → Fin k) (m : Mono n) : Mono k -- sum exponents in each fibre
def succAt (i : Fin n) (m : Mono n) : Mono n        -- mul m (unit i)
def splits (m : Mono n) : List (Mono n × Mono n)    -- pairs whose product is m
def prod [One R] [Mul R] (x : Fin n → R) (m : Mono n) : R
```

`mul` is the monoid operation the `mul_mono` field of `IsMonomialOrder`
refers to, so the class and this API have to agree on it. State
`IsMonomialOrder` in terms of `Mono.mul` rather than a bare `+`. The
laws worth naming are that `dvd` agrees with the existence of an exact
quotient, that `div` is a left inverse of `mul` on the divisible case,
`mul_assoc`, `mul_comm`, the scale/unit decomposition, `degree_mul`,
`rename_mul`, `splits_mem_iff`, `splits_nodup`, and the `lcm`/`gcd` lattice
laws, all of which the S-polynomial construction uses.

## Kernel reduction

The tactic consumers (`sos`, and anything in the `factor_poly` family
that grows a multivariate arm) check certificates with `decide +kernel`.
The representation therefore has to reduce in the kernel, not merely
compile.

`Std.ExtTreeMap` is the candidate representation, but it is not accepted
for certificate replay until a downstream module proves that the full
production equality and arithmetic path reduces. That probe uses
`module`, `public import`, the intended `@[expose]` closure,
`Vector Nat n` keys, the `nonzero` wrapper, and both `Int` and `Rat`
coefficients. Testing a bare container or a legacy non-module file does
not answer the question.

The comparative probe implements a competent canonical sorted-list
representation as well. Its addition is a linear merge, and its
multiplication uses translated-row merging or a produce-sort-combine
pass rather than repeated linear insertion. Workloads include disjoint
and interleaved addition, low- and high-collision multiplication,
cancellation-heavy identities, sparse random supports, rename and
substitution collisions, and real SOS certificate identities. They vary
arity, degree, term count, coefficient type, and monomial order.

These elaboration measurements live under the `mathlib: true`
`HexMvPolyMathlib` proof-probe root. They are not LeanBench targets and
do not define `main`. The Mathlib-free `HexMvPoly` bench contains only
compiled performance measurements. A second kernel-specialised
representation is justified only if the sorted form beats
`ExtTreeMap` by more than 2× on at least two workload families at the
largest size within the proof-probe time budget. Otherwise the single
representation stands. The `PolyOps`-style abstraction in
[future-work](../future-work.md) is where a second representation would
attach.

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

**Comparison.** `Vector.compareLex compare` has the relevant Std laws,
but direct `Vector.compare` is not the chosen kernel path because it
delegates to `Array.compareLex`, whose body is unavailable downstream
under the module system. Define the named lexicographic comparator
through the exposed `List.compareLex compare a.toList b.toList`.
Transport the Std laws with `Vector.compareLex_eq_compareLex_toList`;
graded lex and graded reverse lex use that comparator and the same
exposed list machinery.

The equality and construction constraints are shims for
[leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270)
and disappear when it lands. The comparison shim remains until
`Array.compareLex` itself is exposed upstream.

The kernel replay closure is everything a certificate check touches:
`Mono` operations, the comparator, `ExtTreeMap` lookup and `alter`,
arithmetic and equality, direct and Horner evaluation, substitution and
partial evaluation, and the recursive view. Each is `@[expose]`, and a
downstream module carries `decide +kernel` tests that fail if any of them
stops reducing. Storage-order and reporting queries such as
`totalDegree`, `vars`, and pretty-printing remain outside that closure
and expose their behavior through characterizing lemmas instead.

Operations whose kernel-friendly shape differs from the fast shape carry
a `@[csimp]` pair, as `Hex.Array.ofFn'` does. Multiplication is the
likely candidate: the scratch-accumulator version below is the one to
compile, and a simpler fold may be the one to reduce.

## Algorithms and complexity

Complexity is in terms of the term counts `s = p.termCount` and
`t = q.termCount`, arity `n`, the maximum exponent `d`, and the cost of
one coefficient operation. Monomial comparison is `O(n)`, which is not
constant and shows up in every tree operation.

| operation | algorithm | cost |
|---|---|---|
| `coeff` | `ExtTreeMap.get?` | `O(n log s)` |
| `monomial`, `C`, `X` | single insert | `O(n)` |
| `add` | fold `alter` of the smaller into the larger | `O(n · t log (s+t))` |
| `neg` | map over values | `O(s)` |
| `mul` | Gustavson-style: for each term of `p`, translate every term of `q` and accumulate into one output map | `O(n · s · t · log (s·t))` |
| `leadingTerm` | max entry in `cmp` order | `O(log s)` |
| `reorder` | rebuild under the new comparator | `O(n · s log s)` |
| `rename` | rebuild, combining collisions | `O(n · s log s)` |
| `eval` | Horner over the recursive view, or direct term sum with repeated-squaring powers | `O(s · n · log d)` coefficient operations in the direct form |
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
def termsList (p : MvPoly n R cmp) : List (Mono n × R)
def monomials (p : MvPoly n R cmp) : List (Mono n)
def foldTerms (f : α → Mono n → R → α) (init : α) (p : MvPoly n R cmp) : α
def termCount (p : MvPoly n R cmp) : Nat
def totalDegree (p : MvPoly n R cmp) : Nat
def degreeOf (i : Fin n) (p : MvPoly n R cmp) : Nat
def degrees (p : MvPoly n R cmp) : Mono n
def vars (p : MvPoly n R cmp) : List (Fin n)
def leadingMono (p : MvPoly n R cmp) : Option (Mono n)
def leadingCoeff (p : MvPoly n R cmp) : R
def leadingTerm (p : MvPoly n R cmp) : Option (Mono n × R)
def restrictBy (keep : Mono n → Bool) (p : MvPoly n R cmp) : MvPoly n R cmp
def restrictDegree (i : Fin n) (bound : Nat) (p : MvPoly n R cmp) :
    MvPoly n R cmp
def restrictTotalDegree (bound : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp

-- Evaluation
def eval [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) : R
def evalHorner [Lean.Grind.CommSemiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) : R
def eval₂ [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) : S
def eval₂Horner [Zero R] [Lean.Grind.CommSemiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) : S
def partialEval (s : Fin n → Option R) (p : MvPoly n R cmp) : MvPoly n R cmp

-- Structural
def derivative [Zero R] [NatCast R] [Add R] [Mul R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) : MvPoly n R cmp
def homogeneousComponent (d : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp
def rename (cmp' : Mono k → Mono k → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (f : Fin n → Fin k) (p : MvPoly n R cmp) : MvPoly k R cmp'
def reorder (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly n R cmp) : MvPoly n R cmp'
def subst (f : Fin n → MvPoly k R cmp') (p : MvPoly n R cmp) : MvPoly k R cmp'
def bind (f : R → S) (g : Fin n → MvPoly k S cmp')
    (p : MvPoly n R cmp) : MvPoly k S cmp'
def bind₁ (f : Fin n → MvPoly k R cmp')
    (p : MvPoly n R cmp) : MvPoly k R cmp'
```

The signatures above elide their typeclass bounds, and the elision
hides a real requirement: `[Zero R]` alone is not enough for any
operation that has to drop a cancelled term. The primitive canonical
layer (`C`, `monomial`, `ofTerms`, addition, negation, multiplication,
subtraction, and powers) carries `[BEq R] [LawfulBEq R]` alongside only
the operational classes it needs. It derives a local `DecidableEq` for
proof-relevant branches, so the executable operation does not depend on
which larger algebraic law bundle happened to supply equality. Negation
uses one deletion-capable `ExtTreeMap.filterMap` pass rather than assuming
that an arbitrary `Neg` operation preserves nonzero coefficients.
The polynomial equality instance remains the explicit
`[DecidableEq R]` ordered-term-list path described above.

Canonical arithmetic laws and semantic transformations use the
Mathlib-free `Lean.Grind.Semiring` / `Lean.Grind.Ring` classes;
representation helpers keep narrower `Zero`/`Add`/`Mul` bounds where
those suffice. Higher collision-producing structural transformations
currently state `[DecidableEq R]`, which coherently supplies the
primitive layer's lawful boolean equality. Write the real bounds per
declaration rather than a single blanket variable block. Direct
evaluation keeps the order `c * x₀^a₀ * x₁^a₁ * ⋯` and therefore needs
only a `Lean.Grind.Semiring`; fixed-order Horner nesting can move an
outer variable factor past inner-variable factors, so `evalHorner` and
`eval₂Horner` require a `Lean.Grind.CommSemiring`. `subst` keeps the
target comparator implicit because the codomain of `f` determines it;
that codomain carries the same `TransCmp` and `LawfulEqCmp` obligations
as every `MvPoly`.
In particular, the computational `derivative` states the narrower
`[Zero R] [NatCast R] [Add R] [Mul R] [DecidableEq R]` bounds directly,
matching the shape of `Hex.DensePoly.derivative` while retaining
canonical zero deletion. Its coefficient law uses
`[Lean.Grind.Semiring R] [DecidableEq R]`; the theorem module may expose
`Lean.Grind.Semiring.natCast` as a default-priority local instance.
Mathlib's `CommSemiring` already supplies `Zero`, `NatCast`, `Add`, and
`Mul`, so the companion needs no Mathlib-to-Grind adapter merely to call
the definition.

Constructor and query contracts are explicit. `ofTerms` sums duplicate
monomials and drops zeros. `support` and every term iteration is ordered
by `cmp`. `totalDegree`, `degreeOf`, `vars`, and `leadingCoeff` have
stated values on the zero polynomial. `rename`, `partialEval`, and
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
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n+1) R cmp) :
    DensePoly (MvPoly n R cmp')

/-- Inverse of `toUnivariate`, reinserting variable `i`. -/
def ofUnivariate (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (q : DensePoly (MvPoly n R cmp')) :
    MvPoly (n+1) R cmp
```

The main variable is `i : Fin (n+1)`, not `Fin n`: a polynomial in
`n+1` variables has `n+1` variables to choose from, and `Fin n` both
excludes the last one and makes the one-variable case `n = 0` have no
admissible index at all. The reindexing between the remaining `n`
variables and the original `n+1` is `Fin.succAbove i` and its partial
inverse, and the comparator on the remaining variables is an explicit
argument since nothing determines it from `cmp`. These conversions only
store and traverse terms, so they require the map comparator laws rather
than the stronger `IsMonomialOrder` laws used by leading-term algorithms.

Required theorems: coefficient characterisations in both directions,
both round trips (`ofUnivariate i cmp' (toUnivariate i cmp' p) = p` and
its converse). The Mathlib companion packages the round trips and ring
laws as equivalences, including the degenerate one-variable case.

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
theorem coeff_one       : coeff m 1 = if m = Mono.zero then 1 else 0
theorem coeff_ofTerms   : coeff m (ofTerms ts) =
    ((ts.filter fun t => t.1 == m).map fun t => t.2).sum
theorem coeff_add       : coeff m (p + q) = coeff m p + coeff m q
theorem coeff_sub       : coeff m (p - q) = coeff m p - coeff m q
theorem coeff_neg       : coeff m (-p) = -coeff m p
theorem coeff_mul       : coeff m (p * q)
    = (m.splits.map fun ab => coeff ab.1 p * coeff ab.2 q).sum
theorem pow_succ        : p ^ (k + 1) = p ^ k * p
theorem coeff_pow_succ  : coeff m (p ^ (k + 1)) = coeff m (p ^ k * p)
theorem coeff_reorder   : coeff m (reorder cmp' p) = coeff m p
theorem coeff_rename    : coeff m (rename cmp' f p)
    = ((p.termsList.filter fun t => Mono.rename f t.1 == m).map
        fun t => t.2).sum
theorem coeff_derivative : coeff m (derivative i p)
    = (((m.degreeOf i + 1 : Nat) : R) * coeff (m.succAt i) p)
theorem coeff_homogeneousComponent :
    coeff m (homogeneousComponent d p) =
      if m.degree == d then coeff m p else 0
theorem coeff_restrictBy :
    coeff m (restrictBy keep p) = if keep m then coeff m p else 0
theorem subst_eq :
    subst f p = (p.termsList.map fun t => C t.2 * t.1.prod f).sum
theorem partialEval_eq_subst :
    partialEval s p =
      subst (fun i => match s i with | some x => C x | none => X i) p
theorem eval_eq         :
    eval x p = (p.termsList.map fun t => t.2 * t.1.prod x).sum
theorem evalHorner_eq   : evalHorner x p = eval x p
theorem eval₂_eq        :
    eval₂ g x p = (p.termsList.map fun t => g t.2 * t.1.prod x).sum
theorem eval₂Horner_eq  : eval₂Horner g x p = eval₂ g x p
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
combines coefficients rather than dropping one. `subst_eq` and
`partialEval_eq_subst` make that second obligation explicit. All
coefficient laws quantify over every monomial, including monomials
outside the stored support.

## The Mathlib layer

`hex-mv-poly-mathlib` proves the following. As in the computational API
block, signatures here show the mathematical bounds and elide the
primitive `[BEq R] [LawfulBEq R]` arguments that maintain coherent
executable equality:

```lean
def equiv [CommSemiring R] [DecidableEq R] :
    MvPoly n R cmp ≃+* MvPolynomial (Fin n) R

/-- Arity zero: the only monomial is `Mono.zero`. -/
def isEmptyRingEquiv [CommSemiring R] [DecidableEq R] :
    MvPoly 0 R cmp ≃+* R

/-- The recursive view as a ring equivalence, at the first variable. -/
def finSuccEquiv [CommSemiring R] [DecidableEq R]
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] :
    MvPoly (n+1) R cmp ≃+* DensePoly (MvPoly n R cmp')

def oneVarEquiv [CommSemiring R] [DecidableEq R] :
    MvPoly 1 R cmp ≃+* DensePoly R

def aeval [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) :
    MvPoly n R cmp →ₐ[R] S
```

plus the homomorphism lemmas `aeval_add`, `aeval_mul`, `aeval_sub`,
`aeval_neg`, `aeval_pow`, `aeval_zero`, `aeval_one`, `aeval_C`, and
`aeval_X`. That list is what `sos`'s verifier uses today.

The `neg` and `sub` lemmas require ring assumptions, so the lemma set
splits by its real hypotheses. `aeval_eq_eval₂` states the general
coefficient-map correspondence, while `aeval_eq_eval` is the
compatibility specialization used by `sos`. Core `eval` only evaluates
into the coefficient type itself. The companion also owns the
transported `CommSemiring`, `CommRing`, and `Algebra R` instances on
`MvPoly`.

Those transported instances are parameterized by the ambient explicit
`[DecidableEq R]`; they do not bake in `Classical.decEq`. Results are
independent of that choice because equality decisions are subsingleton
and the canonical operations branch only on the proposition they
decide.

Following the project split, no *mathematical* theorems about `MvPoly`
belong in the Mathlib layer. What does belong, beyond the bare ring
equivalence, is a correspondence lemma for each public semantic
operation: coefficients, evaluation, degree, derivative, rename,
substitution, and both directions of the recursive view. Without those
a caller cannot transport anything except a ring identity.

`finSuccEquiv` is `toUnivariate` at `i = 0`, bundled using the core
round-trip and ring laws. The general-position functions remain the
Mathlib-free API. `isEmptyRingEquiv`, `finSuccEquiv`, and
`oneVarEquiv` live here because `≃+*` is a Mathlib structure. They are
also the declarations needed by CompPoly's two recursive-view
consumers.

## Relationship to existing implementations

Three implementations exist, and this SPEC is written knowing all three.

**CompPoly** (`CMvPolynomial n R`, Verified-zkEVM) is the closest:
`ExtTreeMap` keyed on `Vector ℕ n`, wrapped in a `Lawful` nonzero
invariant. Differences here are that the monomial order is an explicit
argument rather than `class MonomialOrder (n : ℕ)`, and that the
computational layer carries no Mathlib dependency.

Its public surface is the useful thing to take from it: a mature
multivariate library's declaration list is a better capability
checklist than anything derived from first principles, so this SPEC
treats matching it as a requirement and records the audit under
"Consumer surfaces". Whether CompPoly then retires its own module is
their call, not a goal of this SPEC. Two points of scope are worth
knowing when weighing that: ArkLib, CompPoly's principal downstream,
does not use the multivariate module at all (zero imports of
`CompPoly.Multivariate` and zero occurrences of `CMvPolynomial`). Its
dependency runs through univariate `CPolynomial`, the multilinear `MLE`,
and the finite-field modules. Within CompPoly the multivariate module has
exactly two consumers, `Bivariate/CMvEquiv.lean` and
`Univariate/CMvEquiv.lean`, both reaching it only through
`finSuccEquiv` and `isEmptyRingEquiv`. So the capability bar is real but
the downstream footprint is small, and nothing here is on ArkLib's path.
Anything aimed at ArkLib would target univariate and multilinear
polynomials, which is a different library.

**`MvSparsePoly R nvars`** (Michail Karatarakis, Mathlib PRs
[#41339](https://github.com/leanprover-community/mathlib4/pull/41339),
[#41348](https://github.com/leanprover-community/mathlib4/pull/41348),
[#41350](https://github.com/leanprover-community/mathlib4/pull/41350),
split from closed #41282/#41283) is a sorted list of
`(exponent-vector, coefficient)` pairs, canonical, with an `AlgEquiv` to
`MvPolynomial (Fin nvars) R` and the tactics `mv_decide`, `mv_compute`,
and `mv_mem`. Definitions by Mario Carneiro, prototype by James
Davenport. It is axiom-free and targets kernel reduction specifically.
The design agrees with this one on arity, canonicality, and the shape of
the equivalence, and differs on the container. `mv_mem` decides ideal
membership by multi-divisor normal form, which is the shape the Gröbner
item in [future-work](../future-work.md) wants.

**`MonomialOrderedPolynomial`** (WuProver) builds
`SortedAddMonoidAlgebra` on `SortedFinsupp σ R cmp`, generic in the
index type and with the comparator explicit, aimed at identity testing
and at Gröbner bases in `WuProver/groebner_proj`. It agrees with this
SPEC that the comparator is an argument, and differs on the index type.

Reflection onto a computable polynomial type only computes when the
coefficient type is itself computable. A tactic can therefore restrict
itself to coefficients it can normalise, or prove
`p : ℝ[X] = algebraMap ℚ[X] ℝ[X] p'` and compute in the `ℚ` model. The
Mathlib-free representation and its companion support the second route
without making the computational library depend on Mathlib. The kernel
proof probes compare it with the sorted-list alternative before either
representation is recommended for tactic use.

## Conformance

Fixtures follow the layout in [SPEC/testing.md](../testing.md). The
Lean drivers are `conformance/HexMvPoly/Conformance.lean` and
`conformance/HexMvPoly/EmitFixtures.lean`, with the latter exposed as
`lean_exe hexmvpoly_emit_fixtures`. The committed snapshot is
`conformance-fixtures/HexMvPoly/mvpoly.jsonl`, and the oracle driver is
`scripts/oracle/mvpoly_sympy.py`. Adding it extends the existing
conformance job. It requires all three of:

- append one tuple to `ORACLES` in `scripts/ci/run_oracles.sh`.
- add SymPy to the existing pip install line in `.github/workflows/ci.yml`.
- add a SymPy import to the `HEX_REQUIRE_ORACLES=1` dependency preflight
  in `scripts/ci/run_oracles.sh`, so a missing oracle dependency fails
  rather than producing a green skip.

It also requires the two Lean target registrations that make the
drivers build:

- append `HexMvPoly.Conformance` to the existing `HexConformance` globs
  in `lakefile.lean`.
- declare `lean_lib HexMvPolyMathlibProofProbe` with `srcDir := "bench"`
  and explicit `HexMvPolyMathlib.ProofProbe.*` globs, then append that
  target to `HEX_LIB_TARGETS` in the existing CI job.

The oracle tuple is:

```
"HexMvPoly|hexmvpoly_emit_fixtures|scripts/oracle/mvpoly_sympy.py|conformance-fixtures/HexMvPoly/mvpoly.jsonl"
```

A new fixture kind `mvpoly` carries the arity, the comparator name, and
the term list as `(exponent vector, coefficient)` pairs, so a record is
self-describing and records at different arities share one stream.

**Oracle choice.** SymPy's `Poly` covers arithmetic, degrees, evaluation,
substitution, and content over `ℚ` and `ℤ`, and is the right default
because its term enumeration is order-explicit. SymPy is a new CI
dependency for this project, which is why both the install step and
oracle preflight must change. Its mode is `if_available`; release CI
sets `HEX_REQUIRE_ORACLES=1`, making the preflight the hard gate without
misclassifying a third-party pip dependency as an `always` oracle.
Singular becomes the oracle when the
Gröbner layer arrives. It is not needed for this library. python-flint
covers multivariate polynomials only partially, so it is not the choice
here even though the rest of the polynomial libraries use it.

**Cases that must be present**, since these are what a plausible
implementation gets wrong:

- cancellation to zero, both in `add` and in `mul`, checking that no
  explicit zero coefficient survives.
- duplicate monomials passed to `ofTerms`, which must sum rather than
  overwrite.
- the zero polynomial and constants through every query
  (`totalDegree`, `degreeOf`, `vars`, `leadingCoeff`, `leadingTerm`).
- arity zero, where the only monomial is `Mono.zero`.
- non-injective `rename`, where distinct monomials collide and their
  coefficients must combine, including to zero.
- `subst` and `partialEval` producing collisions.
- `toUnivariate` and `ofUnivariate` at every main-variable position
  `i : Fin (n+1)`, including the first and last, with round trips.
- `reorder` between lex, grlex, and grevlex, checked by `coeff`
  agreement rather than by term order.
- monomial operations: `div` on the non-divisible case, `lcm` and `gcd`
  against pointwise max and min.

The companion adds theorem-level transport and instance-coherence checks
against Mathlib's `MvPolynomial (Fin n) R` through `equiv`. These check
that the public correspondence API applies under lex, grlex, and grevlex
and that importing the bridge does not replace executable notation with a
noncomputable path. They are deliberately not described as an independent
randomized oracle: Mathlib's representation is noncomputable. The core
fixture stream and SymPy comparison provide the independent randomized
coverage.

## Benchmarking

Two suites, per [SPEC/benchmarking.md](../benchmarking.md), because the
two consumers stress different things and a single number would hide
both.

**Kernel suite.** `decide +kernel` on identities, reported as
elaboration wallclock. This is a build-only
`HexMvPolyMathlib` proof probe, not a LeanBench target. It runs the
production types (`Vector Nat n` keys, the real `DecidableEq`, `Rat` as
well as `Int`) from a downstream module under the module system,
against both the `ExtTreeMap` form and a competently implemented sorted
form. Workload families are disjoint and interleaved addition,
low-collision and high-collision multiplication, cancellation-heavy
identities, sparse random supports, `rename` and `subst` collisions, and
real `sos` certificates. They vary arity, degree, term count, and
comparator.

**Native suite.** Compiled throughput on the same families, which is
what CompPoly's consumers care about and what would justify retiring
their module.

**Comparators.** CompPoly and `MvSparsePoly` are the two that matter and
both are `informational` rather than required checks: they are
structurally different designs, and the point of measuring them is to
decide a design question rather than to hold a ratio. SymPy is not a
performance comparator. Since both Lean comparators import Mathlib,
their adapters run as external comparator drivers over the shared input
corpus rather than as imports of the Mathlib-free LeanBench target.
The core registration owns the five native-family comparisons. The
Mathlib companion separately registers `MvSparsePoly` for the kernel
families, where the representation decision is made.

**The threshold, written down in advance.** A second, kernel-specialised
representation is justified only if the kernel suite shows the sorted
form beating `ExtTreeMap` by more than 2× on at least two workload
families at the largest size that fits the bench time budget. The ratio
is the median production workload time divided by the median sorted
workload time after subtracting the same round's matched import-only
module build from each arm. Raw fresh-module wall times are still
reported, together with the maximum raw ratio attainable if the sorted
workload itself took zero time; an import-dominated raw ratio is not
used for this decision.

Both baseline-subtracted medians must exceed the robust variability
envelope of the round-matched import baseline. The record separately
calibrates pair-order noise with same-module controls at two build
magnitudes, interpolates a robust median/IQR/Tukey envelope at each
substantive build magnitude, and is invalid when a control's IQR exceeds
10% of its build magnitude. A baseline-limited ratio or a comparison
whose arm delta is unresolved against the interpolated null envelope
does not count toward the threshold. Reference and candidate arms use
the same coefficient type, arity, comparator, support stream, and
identity; the report records those axes for every pair. Anything short
of two resolved greater-than-2× workload ratios leaves the single
representation standing.

When a workload includes materially different input construction, a matched
construction-only pair is subtracted round by round after import subtraction.
The resulting net ratio counts only when both net arms exceed the sum of the
full-workload and construction-control null envelopes. This prevents a faster
constructor from being reported as a faster arithmetic operation.

The native driver lives at `bench/HexMvPoly/Bench.lean`. Kernel probes
live below `bench/HexMvPolyMathlib/ProofProbe/`, contain no `main`,
import no `LeanBench`, and are registered through
`HexMvPolyMathlib.proof_probes`.

Because the native registration names two comparators, Phase 4 also
commits the five required comparator plots under
`reports/figures/hex-mv-poly-comparator-<family>.svg`, generated by
`scripts/plots/hex-mv-poly-comparator.py --family <family>`.

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
  Recursive.lean     -- zero-arity, one-variable, and finSucc ring equivalences
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
    status: active
    phase4:
      comparators:
        - tool: "CompPoly CMvPolynomial"
          class: informational
          rationale: "CompPoly uses the same ExtTreeMap representation behind a Mathlib-dependent API; the comparison records integration and implementation overhead rather than gating release."
        - tool: "canonical sorted-list MvSparsePoly proxy"
          class: informational
          rationale: "The pinned Mathlib revision has no MvSparsePoly, so a local canonical sorted-list proxy records compiled throughput for the alternative algorithmic shape. The native comparison is informational; only the registered kernel proof probes can decide whether a second representation is justified."
      input_families:
        - name: sparse-addition
          description: Disjoint and interleaved sparse supports across lexicographic, graded lexicographic, and graded reverse lexicographic order.
        - name: sparse-multiplication
          description: Low-collision and high-collision products varying arity, degree, term count, coefficient type, and comparator.
        - name: cancellation-arithmetic
          description: Cancellation-heavy integer and rational arithmetic measured as compiled Mathlib-free computation.
        - name: structural-collisions
          description: Sparse rename, partial-evaluation, and substitution cases where distinct source terms collide.
        - name: sum-of-squares-arithmetic
          description: Representative sum-of-squares-shaped identities measured as compiled Mathlib-free arithmetic.
  HexMvPolyMathlib:
    deps: [HexMvPoly, HexPolyMathlib]
    mathlib: true
    done_through: 0
    status: active
    proof_probes: [bench/HexMvPolyMathlib/ProofProbe]
    phase4:
      comparators:
        - tool: "canonical sorted-list MvSparsePoly proxy"
          class: informational
          rationale: "Mathlib MvSparsePoly is not yet available in the pinned Mathlib revision, so a local canonical sorted-list proxy with linear merge addition and balanced translated-row multiplication is used to decide whether HexMvPoly needs a second representation."
      input_families:
        - name: kernel-sparse-addition
          description: Disjoint, interleaved, and scattered supports checked under lex and grevlex, including an arity-eight case.
        - name: kernel-sparse-multiplication
          description: Low-collision integer and high-collision rational products checked across lex and arity-eight grevlex representations.
        - name: kernel-cancellation-identities
          description: Cancellation-heavy integer and rational identities checked from a downstream module with decide +kernel.
        - name: kernel-structural-collisions
          description: Rename and substitution identities whose distinct source terms collide in the destination support.
        - name: kernel-sos-certificates
          description: Representative sum-of-squares certificate identities checked from a downstream module with decide +kernel.
```

`HexBasic` is a dependency for the reasons under "Kernel exposure", and
drops out when the upstream fix lands. `HexPoly` is needed for
`DensePoly` in the recursive view. The `HexMvPolyMathlib` root and this
active registry entry land atomically; the active status is required
because the consumer-compile acceptance milestone depends on that root.

## Consumer surfaces

Acceptance includes the public declarations used by `sos` and the two
CompPoly recursive-view consumers.

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

Core `bind` is CompPoly's coefficient-and-variable mapping operation;
`bind₁` is the same-coefficient compatibility name for `subst`. Both
are present in the API block above rather than left as unstated consumer
renames.

**CompPoly's public multivariate surface**, taken as the capability
checklist: `C`, `X`, `monomial`, `coeff`, `ext`, `eval`,
`eval₂`, `evalHorner`, `aeval`, `bind`, `rename`, `support`,
`totalDegree`, `degreeOf`, `degrees`, `vars`, `leadingCoeff`,
`leadingMonomial`, `leadingTerm`, `restrictBy`, `restrictDegree`,
`restrictTotalDegree`, `npowBySq`, and the Horner-grouping machinery
(`HornerGroup`, `HornerTerm`, `hornerGroups`, `collectHornerGroups`,
`insertHornerGroupDesc`, `insertHornerTerm`, `sortHornerGroups`,
`evalSparseHornerGroups`, `hornerExponent`, `sumToIter`).

The `restrict*` family is part of the public query API above. CompPoly's
Horner-grouping declarations are an evaluation strategy rather than a
compatibility surface. The native benchmarks determine whether to port
them. The Mathlib companion supplies `isEmptyRingEquiv` and
`finSuccEquiv`, which are the declarations used by
`Bivariate/CMvEquiv.lean` and `Univariate/CMvEquiv.lean`.

The first implementation milestone is an API stub that makes the `sos`
search and verifier plus the two CompPoly equivalence files build. The
stub may use `sorry` for proofs, but it must use the final signatures and
instance requirements. Algorithm work starts only after that compile
check, because it is the acceptance test for the surface listed here.

## Implementation order

1. Define `Mono`, the comparator classes, `MvPoly`, canonical
   construction, and the exact consumer-facing signatures. At this
   point add a minimal downstream `decide +kernel` probe for production
   monomial comparison, polynomial equality, addition, and
   multiplication over both `Int` and `Rat`; do not defer representation
   viability until after the semantic layers are built.
2. Compile `sos` and the two CompPoly recursive-view consumers against
   the API stub.
3. Implement arithmetic, structural operations, coefficient laws, and
   the recursive view.
4. Add conformance fixtures and the Mathlib correspondence.
5. Run the module-boundary kernel probes and native benchmarks. Keep
   `ExtTreeMap` as the compiled representation. If the recorded threshold
   selects the sorted form, record the justified kernel-specialized second
   representation under [future-work](../future-work.md), where the
   representation abstraction belongs.

## Open questions

- **Coefficient types.** The library is generic in `R`. CompPoly
  compatibility and the later Hex work both require that, so it is not
  in question. The open part is that `sos` needs `Rat`, whose
  kernel-reduction cost must be measured separately from the polynomial
  container. If that cost dominates, a kernel-friendly rational
  representation is a separate library decision.
- **Sparse coefficients versus sparse exponents.** `Mono n` as a dense
  `Vector Nat n` is right for small `n`. Whether large `n` with few
  active variables wants a sparse exponent vector should be settled by
  the Gröbner and factorization benchmarks, not now.
- **Horner grouping.** `evalHorner` is required, but CompPoly's public
  intermediate grouping types are not. Add them only if native
  benchmarks show that callers need to construct or reuse groups.
- **Relationship to `hex-poly`.** `toUnivariate` makes hex-mv-poly
  depend on hex-poly. Whether the dependency should instead run the
  other way, with `DensePoly R` a special case of the multivariate type,
  is worth a look, though the answer is probably no: the dense
  univariate representation is the right one for Berlekamp-Zassenhaus
  and should not pay for generality.
