# hex-truncated-series (fixed-precision truncated power series, depends on hex-basic)

Power series over a commutative ring, truncated at a precision fixed in
the type, with the ring operations, precision changes, Newton iteration
for inverse, square root, `exp` and `log`, and composition and
reversion. Mathlib-free. The companion `hex-truncated-series-mathlib`
identifies the type with `PowerSeries R` modulo `X ^ n` and identifies
each operation with its Mathlib counterpart where one exists.

This SPEC expands the "Truncated power series" entry of
[future-work](../future-work.md). It does not specify fast polynomial
division, fast polynomial remainder, or any conversion to `DensePoly`.
Those belong to the planned `hex-poly-fast`, which depends on both this
library and hex-poly. The reason is given under "Placement in the DAG".

## Why this library exists

**Newton iteration on a truncated series is the primitive under fast
polynomial division.** Dividing `f` by `g` in degree `d` is inverting
the reversal of `g` to precision `d + 1` and multiplying. hex-poly
divides schoolbook, so every consumer that divides large polynomials
pays `O(d²)` where `O(M(d))` is available. Half-gcd, fast modular
composition, and fast Padé approximation all reduce to the same
inversion.

**The series operations are wanted for their own sake.** `exp`, `log`,
square root, composition and reversion of series appear in generating
function manipulation, in Hensel-style lifting where the modulus is a
power of `x` rather than a power of `p`, and in the coefficient
extraction that combinatorial identities need. None of that requires a
polynomial type.

**Nothing in the tree computes with a truncated series today.**
`HexBerlekampZassenhaus/QuadraticNormRecover.lean:74` has a one-off
formal logarithm of a series with constant term `1`, written for the
quadratic-norm recovery step and correct only there. That is the whole
of it. A library with a stated precision contract replaces that
one-off and makes the next such need a call rather than another
one-off.

**The precision contract is the interesting theorem, and it is easy to
get wrong.** An operation on inputs correct to precision `n` must
return a result correct to precision `n`, and the operations that lose
precision must lose a stated amount. Writing that down once, with the
hypotheses each algorithm actually needs, is most of the value here.

## Placement in the DAG

The dependency is hex-basic and nothing else.

```text
hex-basic ── hex-truncated-series ── hex-truncated-series-mathlib
```

The planned consumer joins this library to hex-poly:

```text
hex-poly ─────────────┐
                      ├── hex-poly-fast  (planned)
hex-truncated-series ──┘
```

**No edge runs from this library to hex-poly, and none may be added.**
Reversal of a `DensePoly`, fast division, fast remainder, and fast
`gcd` all live in hex-poly-fast, above both. If instead this library
converted to and from `DensePoly` it would depend on hex-poly, and
hex-poly's own fast division would then depend on this library, which
is a cycle in the release graph as well as in the build. The release
graph is the harder constraint: `scripts/release/released.yml` lists
repositories in topological order and rewrites each one's Lake pins, so
a cycle is not merely inconvenient there, it has no valid publication
order.

The graph with the planned consumer is acyclic, and it is acyclic for a
reason that survives future additions: this library names no polynomial
type at all. Its whole interface is coefficient vectors of a fixed
length. A reviewer checking acyclicity does not have to trace hex-poly's
imports, only to check that `HexTruncatedSeries/*.lean` imports nothing
but `HexBasic` and `Std`.

The companion adds an edge to Mathlib and to nothing else, so the
Mathlib-side graph is `hex-truncated-series-mathlib → hex-truncated-series`
and `hex-truncated-series-mathlib → Mathlib`. It does not depend on
hex-poly-mathlib, because it states nothing about polynomials.

## Why hex-basic and not hex-poly

Three reasons.

**`DensePoly` carries a normalisation invariant this type must not
have.** `DensePolyNormalized` (`HexPoly/Dense.lean:26`) says the
coefficient array has no trailing zeros, which is what makes structural
equality agree with equality of polynomials. A truncated series at
precision `n` has exactly `n` coefficients, trailing zeros included, and
its equality is equality of all `n` of them. Reusing `DensePoly` would
mean renormalising after every operation and would conflate "the
coefficient is zero" with "the coefficient is beyond the precision",
which is the one distinction the whole precision contract rests on.

**hex-basic supplies three things this library needs and hex-poly
cannot use.** `Hex.instDecidableEqVector` and `Hex.Vector.ofFn'`
(`HexBasic/ArrayDecEq.lean`, `HexBasic/OfFn.lean`) are kernel-reducible
replacements for the `Vector` instances in Lean core, whose bodies are
unavailable across a module boundary so that `decide` stalls on them.
`HexBasic.Fold` is the `List.foldl` algebra over a bare
`Lean.Grind.Semiring` that the convolution sum below is stated with.
hex-poly has no dependencies at all, which is why its own
`DecidableEq (DensePoly R)` carries a hand-written copy of the same
workaround with a comment saying it cannot import `HexBasic.ArrayDecEq`
(`HexPoly/Dense.lean:45-54`). Building the series type on hex-basic
avoids repeating that.

**A fixed-length vector is the right shape for Newton iteration.** Every
step writes a prefix of a buffer of known size. `Vector R n` says the
size is known and lets `Hex.Vector.modify` reuse a uniquely owned
buffer, per design principle 3. An array whose length is a runtime
value would reallocate per step.

The one thing lost is the convolution fold, roughly twenty lines and two
lemmas, which hex-poly also has (`HexPoly/Euclid/MulRing.lean`). That
duplication is deliberate and is cheaper than either a cycle or a new
hex-basic home that hex-poly still could not import. The open questions
record the alternative.

## Scope

In scope: the type and its coefficient semantics; the commutative ring
structure; truncation, zero extension, multiplication and division by
powers of `x`, derivative and integral; inversion, square root, `exp`,
`log`, composition, and reversion, each with its own hypotheses; the
Newton driver and its step-count theorem; and the companion's
correspondence with `PowerSeries R`.

Not in scope, and deliberately: any conversion to or from `DensePoly`;
fast polynomial division, remainder, or `gcd`; multipoint evaluation;
half-gcd; multivariate series; series with a variable precision carried
at runtime rather than in the type; Laurent series and negative
valuations; and any search for a square root of the constant term,
which is a problem in the coefficient ring and belongs there.

## The representation

```lean
namespace Hex

/-- A power series over `R` truncated at precision `n`: the coefficients
of `x^0` through `x^(n-1)`, with no normalisation invariant. -/
structure TSeries (R : Type u) (n : Nat) where
  /-- The stored coefficients in ascending degree order. -/
  coeffs : Vector R n

namespace TSeries

variable {R : Type u} {n : Nat} [Lean.Grind.CommRing R] [DecidableEq R]

/-- The `i`th coefficient, and `0` for `i ≥ n`. Every theorem below is
stated with this total reading rather than with a `Fin n` index. -/
@[expose] def coeff (a : TSeries R n) (i : Nat) : R :=
  if h : i < n then a.coeffs[i] else 0

/-- Tabulate a series from a coefficient function. -/
@[expose] def ofFn (f : Nat → R) : TSeries R n :=
  ⟨Hex.Vector.ofFn' fun i => f i.1⟩

theorem coeff_ofFn (f : Nat → R) (i : Nat) (hi : i < n) :
    (ofFn (n := n) f).coeff i = f i

/-- Two series at the same precision are equal when they agree at every
index below the precision. -/
@[ext] theorem ext {a b : TSeries R n} (h : ∀ i, i < n → a.coeff i = b.coeff i) :
    a = b

instance : DecidableEq (TSeries R n)
```

`coeff` returning `0` above the precision is a convenience for stating
theorems, not a claim about the series. The distinction matters and is
the subject of "Degenerate precisions" below: `a.coeff n = 0` says
nothing about the series `a` approximates.

The precision lives in the type. A caller that needs a precision known
only at runtime writes `(n : Nat) → TSeries R n` and passes it, which is
what the composition and reversion routines do internally. A runtime
precision field on the structure was rejected because it would put an
inequality side condition on every coefficient lemma and would defeat
the `Vector` length reuse that makes the iteration allocate once.

## Coefficientwise semantics

The whole contract is coefficientwise, and there is no separate
semantic function to relate the type to. `TSeries R n` **is** the ring
`R[[x]] / (x^n)`, presented by its coefficients, and the companion
proves that identification rather than the Mathlib-free layer assuming
it.

The convolution sum is stated Mathlib-free as a fold:

```lean
/-- The `i`th coefficient of a product of two coefficient functions. -/
@[expose] def convCoeff (f g : Nat → R) (i : Nat) : R :=
  (List.range (i + 1)).foldl (fun acc j => acc + f j * g (i - j)) 0
```

`HexBasic.Fold` supplies the `foldl` algebra over `Lean.Grind.Semiring`
that the lemmas about `convCoeff` need, so this is a short definition
with short proofs rather than a re-derivation of fold associativity.

## The ring structure

```lean
instance : Zero (TSeries R n)
instance : One (TSeries R n)
instance : Add (TSeries R n)
instance : Neg (TSeries R n)
instance : Sub (TSeries R n)
instance : Mul (TSeries R n)

/-- The constant series. -/
def C (c : R) : TSeries R n
/-- The series `x`, which is `0` when `n ≤ 1`. -/
def X : TSeries R n
/-- `a ^ k` by square-and-multiply. -/
def pow (a : TSeries R n) (k : Nat) : TSeries R n

theorem coeff_zero (i) : (0 : TSeries R n).coeff i = 0
theorem coeff_one  (i) (hi : i < n) : (1 : TSeries R n).coeff i = if i = 0 then 1 else 0
theorem coeff_add  (a b) (i) (hi : i < n) : (a + b).coeff i = a.coeff i + b.coeff i
theorem coeff_neg  (a)   (i) (hi : i < n) : (-a).coeff i = -a.coeff i
theorem coeff_mul  (a b) (i) (hi : i < n) : (a * b).coeff i = convCoeff a.coeff b.coeff i
theorem coeff_C    (c)   (i) (hi : i < n) : (C c : TSeries R n).coeff i = if i = 0 then c else 0
theorem coeff_X          (i) (hi : i < n) : (X : TSeries R n).coeff i = if i = 1 then 1 else 0

instance : Lean.Grind.CommRing (TSeries R n)
```

`pow` is square-and-multiply, not iterated multiplication, per design
principle 7. Every operation above is total and needs no hypothesis
beyond `Lean.Grind.CommRing R`.

**Multiplication also has a bounded form, and the Newton iterations use
it.** Computing only the coefficients below a bound `m` is what makes a
doubling iteration cost a geometric series rather than a fixed multiple
of the full-precision cost:

```lean
/-- The product, with every coefficient at index `m` or above set to
zero. Costs `O(m²)` coefficient operations rather than `O(n²)`. -/
def mulUpTo (m : Nat) (a b : TSeries R n) : TSeries R n

theorem coeff_mulUpTo (m) (a b) (i) (hi : i < n) :
    (mulUpTo m a b).coeff i = if i < m then (a * b).coeff i else 0
```

`mulUpTo n = (· * ·)` up to the propositional equality above, and
`mulUpTo` is the single place a later fast multiplication is installed.
That is the reason the iterations are written against it rather than
against `*`.

## Degenerate precisions

**Precision zero.** `TSeries R 0` has exactly one element, `0 = 1`, and
it is the zero ring. `Lean.Grind.CommRing` does not require
nontriviality, so the instance holds and nothing needs a special case.
Every coefficient theorem above carries `i < n`, so at `n = 0` they are
all vacuous, and `coeff i = 0` for every `i`.

This is not a curiosity, and it is where a careless hypothesis becomes
wrong. In the zero ring **every** element is a unit, every element has a
square root, and every element is invertible under composition. So an
operation that is partial at positive precision is total at precision
zero, and its success condition has to say so. Concretely:

- `a.coeff 0 = 0` for every `a : TSeries R 0`, so a hypothesis "the
  constant term is a unit" is *false* at precision zero over any
  nontrivial `R`, while the conclusion it guards is *true* there.
- A hypothesis "the constant term is `1`" is likewise false, while
  "`(a - 1).coeff 0 = 0`" is true. The two agree for `n ≥ 1`, and only
  the second is right at `n = 0`.

The rule this library follows, stated once and applied everywhere: **a
hypothesis about a coefficient is written as an equation that is
automatically satisfied out of range, and a success condition is written
as an existence statement in `TSeries R n` rather than as a condition on
a coefficient.** So `log` takes `(a - 1).coeff 0 = 0` and not
`a.coeff 0 = 1`, and `inv?` succeeds exactly when the argument is a unit
of `TSeries R n`, which at `n = 0` is always.

**Precision one.** `TSeries R 1` is `R`, by `coeff 0`. `X = 0` there, so
composition and reversion are the identity on the single element `0` and
succeed with no hypothesis on a linear coefficient (there is no linear
coefficient). Precision zero is where a hypothesis on the constant term
is false while its conclusion holds, and precision one is where a
hypothesis on the linear term is.

**Precision two and the first real hypothesis.** At `n = 2` the linear
coefficient exists, and reversion is the first operation whose
hypothesis has content. `exp` and `log` first need a division by an
integer other than `1` at `n = 3`.

## Precision changes

```lean
/-- Discard the coefficients at index `m` and above. -/
def truncate (a : TSeries R n) (m : Nat) (h : m ≤ n) : TSeries R m
/-- Pad with zeros to a larger precision. See the warning below. -/
def extend (a : TSeries R n) (m : Nat) (h : n ≤ m) : TSeries R m
/-- Multiply by `x ^ k`, discarding the top `k` coefficients. -/
def mulXPow (a : TSeries R n) (k : Nat) : TSeries R n
/-- Divide by `x ^ k`, or `none` when the bottom `k` coefficients are
not all zero. The precision drops by `k`. -/
def divXPow? (a : TSeries R n) (k : Nat) : Option (TSeries R (n - k))
/-- The index of the lowest nonzero coefficient, or `none` when every
stored coefficient is zero. -/
def valuation? (a : TSeries R n) : Option Nat
/-- The formal derivative. The precision drops by one. -/
def deriv (a : TSeries R n) : TSeries R (n - 1)

theorem coeff_truncate (i) (hi : i < m) : (a.truncate m h).coeff i = a.coeff i
theorem coeff_extend   (i) (hi : i < m) : (a.extend m h).coeff i = a.coeff i
theorem truncate_extend : (a.extend m h).truncate n h' = a
theorem coeff_mulXPow  (i) (hi : i < n) :
    (a.mulXPow k).coeff i = if k ≤ i then a.coeff (i - k) else 0
theorem coeff_deriv    (i) (hi : i < n - 1) :
    a.deriv.coeff i = ((i + 1 : Nat) : R) * a.coeff (i + 1)
```

`truncate` is a ring homomorphism and the theorem saying so is the
statement the whole library is organised around:

```lean
theorem truncate_mul (a b : TSeries R n) (h : m ≤ n) :
    (a * b).truncate m h = a.truncate m h * b.truncate m h
```

**`extend` is not a ring homomorphism, and the SPEC says so loudly
because the type does not.** At `n = 2` take `a = b = X`. Then
`a * b = 0`, so `extend 3 (a * b) = 0`, while
`extend 3 a * extend 3 b = X ^ 2 ≠ 0`. Zero padding invents information:
it asserts that the coefficients above the old precision are zero, which
is true only when the input is known to be a polynomial of degree below
`n`. `extend` is therefore documented as valid only for such inputs, it
carries no multiplicativity lemma, and no routine in this library calls
it on a value produced by a Newton iteration.

**Precision preservation and loss**, for inputs at precision `n`:

| operation | output precision | notes |
|---|---|---|
| `+`, `-`, `*`, `pow`, `C`, `X` | `n` | exact |
| `mulUpTo m` | `n`, correct below `m` | the bounded form |
| `truncate m` | `m` | exact, a ring homomorphism |
| `extend m` | `m` | not a ring homomorphism, see above |
| `mulXPow k` | `n` | the top `k` input coefficients are discarded |
| `divXPow? k` | `n - k` | genuine loss of `k`, recorded in the type |
| `deriv` | `n - 1` | genuine loss of one |
| `integrate` | `n + 1` | a gain, needs `1/k` for `1 ≤ k ≤ n` |
| `inv`, `sqrt`, `exp`, `log` | `n` | preserved, by the Newton contract |
| `comp` | `n` | preserved, given `b.coeff 0 = 0` |
| `rev` | `n` | preserved, given `b.coeff 1` a unit |

The two rows with a genuine loss put it in the type rather than in a
docstring. A caller who wants `n` coefficients out of `divXPow? k`
computes at precision `n + k`, and the type is what tells them.

## What each algorithm needs

The generic part of the interface is the ring structure and the
precision changes, and it needs nothing beyond `Lean.Grind.CommRing R`
and `DecidableEq R`. Each algorithm on top carries its own hypotheses,
stated separately, because they are genuinely different hypotheses
satisfied by different coefficient rings.

```lean
/-- A partial inverse operation on the coefficient ring. -/
class UnitOps (R : Type u) where
  inv? : R → Option R

/-- The laws `inv?` must satisfy: sound on `some`, and complete, so that
`inv?` detects every unit. -/
class LawfulUnitOps (R : Type u) [Lean.Grind.CommRing R] [UnitOps R] : Prop where
  inv?_eq  : ∀ a u, UnitOps.inv? a = some u → a * u = 1
  inv?_isSome : ∀ a, (∃ u, a * u = 1) → (UnitOps.inv? a).isSome

/-- Inverses of the integers `1` through `m` in `R`. Precision-indexed,
because that is what the algorithms actually need. -/
class NatInverses (R : Type u) [Lean.Grind.CommRing R] (m : Nat) where
  invNat : Nat → R
  invNat_eq : ∀ k, 1 ≤ k → k ≤ m → (k : R) * invNat k = 1
```

**`NatInverses` is indexed by the precision on purpose, and that index
is the point of the class.** Over `ℤ` the instance holds at `m = 1` and
fails at `m = 2`, so `exp` and `log` over `ℤ` exist up to precision `2`
and not beyond, which is correct: `exp(x)` truncated at precision `3` is
`1 + x + x²/2`, and `x²/2 ∉ ℤ[x]`. A class stated as "`R` is a
`ℚ`-algebra", or an unstated assumption that a coefficient can be
divided by a small integer, would either exclude precision `2` over `ℤ`
or would be false. Over `ZMod p` the instance holds exactly for
`m < p`, which is again the true condition and is not "`p` is large".

`NatInverses R m` implies `NatInverses R m'` for `m' ≤ m`. That is
supplied as `NatInverses.mono`, a `def` and not an `instance`, since as
an instance it loops.

Instances shipped here: `Rat` for every `m`, `Int` for `m ≤ 1`, and
`UnitOps Rat`, `UnitOps Int`. The `ZMod64 p` instances are **not**
here, because `ZMod64` is hex-mod-arith's type and depending on
hex-mod-arith would add an edge this library does not need. They belong
in whichever library has both types in scope, which in practice is
hex-poly-fast or a consumer. The open questions record the alternative.

Per-algorithm hypotheses, collected:

| algorithm | needs |
|---|---|
| `invOfUnit a u` | `a.coeff 0 * u = 1` |
| `inv?` | `[UnitOps R] [LawfulUnitOps R]` |
| `sqrtOfRoot a r v` | `r * r = a.coeff 0` and `(2 * r) * v = 1` |
| `exp` | `a.coeff 0 = 0` and `[NatInverses R (n - 1)]` |
| `log` | `(a - 1).coeff 0 = 0` and `[NatInverses R (n - 1)]` |
| `comp a b` | `b.coeff 0 = 0` |
| `revOfUnit b v` | `b.coeff 0 = 0` and `b.coeff 1 * v = 1` |

Note what is **not** in the table. `comp` needs no invertibility of any
kind. `revOfUnit` needs no integer inverses, and the section on
reversion explains why the obvious formula would have needed them.

## Failure behaviour

Two forms per partial algorithm, and no third form.

**A witness-taking total form.** `invOfUnit`, `sqrtOfRoot`, `revOfUnit`
take the witness that makes the algorithm work as an argument and are
total functions with no failure branch. They are the primary form, they
are what the correctness theorems are stated about, and they mirror
Mathlib's `PowerSeries.invOfUnit`.

**An `Option`-returning form** that looks for the witness using the
coefficient ring's `UnitOps`, and returns `none` when there is none.

There is **no** total form that falls back to a junk value on failure.
Design principle 8 requires any such form to be classified as
`unreachable-by-pipeline-invariant` or `audited-emergency-value`, and
neither classification applies here: an inverse of a series whose
constant term is a nonunit does not exist, so no invariant makes the
branch unreachable and no value is mathematically safer than reporting
failure. A caller who wants a total function supplies the witness.

The success conditions, each with the precision-zero disjunct that
"Degenerate precisions" requires:

```lean
theorem inv?_isSome_iff (a : TSeries R n) :
    (inv? a).isSome = true ↔ n = 0 ∨ ∃ u, a.coeff 0 * u = 1

theorem rev?_isSome_iff (b : TSeries R n) :
    (rev? b).isSome = true ↔ n ≤ 1 ∨ (b.coeff 0 = 0 ∧ ∃ v, b.coeff 1 * v = 1)
```

**A caller must not read `(inv? a).isSome` as "the constant term of `a`
is a unit".** At `n = 0` it is `true` and the constant term is `0`. The
right reading is "`a` is a unit of `TSeries R n`", which is what the
theorem says and what the caller almost always wants.

`sqrt` has no searching form. Finding a square root of the constant term
is a problem in `R`: over `ZMod p` it is Tonelli-Shanks, over `ℤ` it is
an integer square root with an exactness test, and over `ℚ` it is that
twice. Putting a `SqrtOps R` class here would oblige this library to
carry instances for rings it does not depend on. The root is an
argument, the caller supplies it, and the choice of root is a real
choice: `r` and `-r` give the two square roots when `2` is a unit.

## Newton iteration and the step count

Every doubling algorithm here uses one driver, and the driver is
structurally recursive on the step count rather than fuel-bounded.

```lean
/-- `newton step init k` applies `step` `k` times, passing the target
precision `2 ^ (j + 1)` at step `j`. -/
def newton (step : TSeries R n → Nat → TSeries R n)
    (init : TSeries R n) : Nat → TSeries R n
  | 0     => init
  | j + 1 => step (newton step init j) (2 ^ (j + 1))

/-- The number of doublings that reaches precision `n` from precision
`1`: zero when `n ≤ 1`, and `⌈log₂ n⌉` otherwise. -/
@[expose] def steps (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

theorem two_pow_steps_ge (n : Nat) : n ≤ 2 ^ steps n
```

**There is no fuel argument and therefore no fallback branch to
classify.** A fuel-bounded formulation would need a `none` or a junk
value on exhaustion, which design principle 8 would then require a
classification for, and the classification would be
`unreachable-by-pipeline-invariant` resting on exactly the theorem
`two_pow_steps_ge` above. Recursing on the step count directly discharges
that obligation by construction. Well-founded recursion on the precision,
halving, would also work and was rejected: well-founded definitions do
not reduce in the kernel, and "Kernel exposure" below needs these to.

`steps n` is `⌈log₂ n⌉`. The looser `Nat.log2 n + 1` is also a correct
bound and is easier to prove things about; it costs at most one extra
doubling, which is one extra full-precision multiplication. Either is
acceptable, and the SPEC states the tight form so that a later
implementation using the loose one is a recorded choice rather than an
accident.

**The step is bounded, which is what makes the total cost geometric.**
Step `j` calls `mulUpTo (2 ^ (j + 1))`, so it costs `O(M(2^j))` and the
sum over `j < steps n` is `O(M(n))` for any `M` growing at least
linearly. Writing every step at full precision `n` would be correct and
would cost `O(M(n) · log n)`, which is the mistake this paragraph
exists to prevent.

The correctness statement common to all four Newton algorithms, with
`op` standing for the operation and `P` for its defining equation:

```lean
theorem newton_correct (j : Nat) (i : Nat) (hi : i < min n (2 ^ j)) :
    P (newton step init j) i
```

Agreement to precision `min n (2 ^ j)` after `j` steps, hence full
agreement at `j = steps n`. Each algorithm instantiates it.

## Inverse

```lean
/-- The inverse of `a`, given an inverse `u` of its constant term. -/
def invOfUnit (a : TSeries R n) (u : R) : TSeries R n
def inv? [UnitOps R] (a : TSeries R n) : Option (TSeries R n)

theorem invOfUnit_mul (a : TSeries R n) (u : R) (hu : a.coeff 0 * u = 1) :
    a * invOfUnit a u = 1

theorem invOfUnit_unique (a b : TSeries R n) (u : R)
    (hu : a.coeff 0 * u = 1) (hb : a * b = 1) : b = invOfUnit a u
```

The iteration is `b ↦ b * (2 - a * b)`, started from `C u`, with both
products taken through `mulUpTo` at the step's target precision. At
`n = 0` the answer is the unique element and `hu` is unsatisfiable over
a nontrivial `R`, which is why `inv?` and not `invOfUnit` carries the
`n = 0` case.

`invOfUnit_unique` is worth having and is short: the ring is
commutative, `a` is a unit, and inverses of a unit are unique. It is
what lets every later theorem say "the inverse" rather than "an
inverse".

**Against a naive baseline, Newton inversion wins nothing at schoolbook
multiplication.** The linear recurrence `b_i = -u · Σ_{j<i} a_{i-j} b_j`
computes the same answer in `O(n²)` coefficient operations, and so does
this iteration. The Newton form is specified anyway because it is the
form that becomes `O(M(n))` the moment `mulUpTo` becomes subquadratic,
and hex-poly-fast is the library that makes it so. The benchmark
requirement below is therefore "within a small constant of the
recurrence", not "faster than the recurrence", and a SPEC that promised
the latter at schoolbook multiplication would be promising something
false.

## Square root

```lean
/-- The square root of `a` with constant term `r`, given `v` inverting
`2 * r`. -/
def sqrtOfRoot (a : TSeries R n) (r v : R) : TSeries R n

theorem sqrtOfRoot_sq (a : TSeries R n) (r v : R)
    (hr : r * r = a.coeff 0) (hv : (2 * r) * v = 1) :
    sqrtOfRoot a r v * sqrtOfRoot a r v = a

theorem sqrtOfRoot_coeff_zero (hr : r * r = a.coeff 0) (hv : (2 * r) * v = 1)
    (h : 0 < n) : (sqrtOfRoot a r v).coeff 0 = r

theorem sqrt_unique (s t : TSeries R n) (r v : R) (hv : (2 * r) * v = 1)
    (hs : s * s = t * t) (h0 : 0 < n)
    (hsr : s.coeff 0 = r) (htr : t.coeff 0 = r) : s = t
```

**One hypothesis, `2 * r` invertible, rather than two.** In a
commutative ring a product is a unit exactly when both factors are, so
`(2 * r) * v = 1` says precisely that `2` is a unit and `r` is a unit,
and it is the quantity the iteration divides by. Splitting it into two
hypotheses would state the same thing less usefully.

Both halves are needed and neither implies the other, which two examples
show. Over `ZMod 2`, `r = 1` is a unit and `1 + x` has no square root at
precision `2`: `(1 + ax)² = 1 + a²x²`, whose coefficient of `x` is `0`,
never `1`. Over `ℤ`, `2` is not a unit either, and even where `r` is
chosen well the iteration divides by `2r`: `4 + x` has constant root
`r = 2`, and its square root `2 + x/4 + …` is not in `ℤ[[x]]`.

The uniqueness proof is three lines and is the reason the constant root
is an argument. If `s² = t²` with `s` and `t` sharing the constant term
`r`, then `(s - t)(s + t) = 0` and `s + t` has constant term `2r`, a
unit, so `s + t` is a unit of `TSeries R n` and `s = t`. The two roots
of a series with a unit constant term are `s` and `-s`, and they are
distinguished exactly by which root of the constant term they carry.

The iteration is on the **inverse** square root, `z ↦ z * (3 - a * z²) *
v'` where `v'` inverts `2`, followed by `sqrt a = a * z`. This avoids an
inversion inside the loop, which is the standard reason to prefer it,
and it needs `2` invertible, which the hypothesis already gives.

## `exp` and `log`

```lean
/-- The integral with zero constant term. -/
def integrate [NatInverses R n] (a : TSeries R n) : TSeries R (n + 1)

def log [UnitOps R] [NatInverses R (n - 1)] (a : TSeries R n) : TSeries R n
def exp [UnitOps R] [NatInverses R (n - 1)] (a : TSeries R n) : TSeries R n

theorem coeff_integrate (i) (hi : i < n + 1) :
    (integrate a).coeff i = if i = 0 then 0 else NatInverses.invNat i * a.coeff (i - 1)

/-- `log` is characterised by its derivative, `(log a)' = a' / a`. Both
sides are at precision `n - 1`, which is where the `NatInverses` index
comes from. -/
theorem deriv_log (a : TSeries R n) (h : (a - 1).coeff 0 = 0) :
    (log a).deriv = a.deriv * (invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1)
theorem log_coeff_zero (a : TSeries R n) (h : (a - 1).coeff 0 = 0) (h0 : 0 < n) :
    (log a).coeff 0 = 0

theorem exp_coeff_zero (a : TSeries R n) (h : a.coeff 0 = 0) (h0 : 0 < n) :
    (exp a).coeff 0 = 1
theorem log_exp (a : TSeries R n) (h : a.coeff 0 = 0) : log (exp a) = a
theorem exp_log (a : TSeries R n) (h : (a - 1).coeff 0 = 0) : exp (log a) = a
theorem exp_add (a b : TSeries R n) (ha : a.coeff 0 = 0) (hb : b.coeff 0 = 0) :
    exp (a + b) = exp a * exp b
```

`log a = integrate (deriv a * inv a)`, at precision `n - 1` inside and
`n` outside. `exp` is Newton on `y ↦ y * (1 + a - log y)`, started from
`1`.

**The index `n - 1` in the `NatInverses` hypothesis is exact, and the
truncated subtraction is doing real work.** `integrate` from precision
`n - 1` to precision `n` divides by `1` through `n - 1`. At `n = 0` and
`n = 1` the hypothesis is `NatInverses R 0`, which every ring satisfies
vacuously, and indeed `exp` and `log` need no division at those
precisions. At `n = 2` it is `NatInverses R 1`, which every ring
satisfies since `1` is a unit. At `n = 3` it first has content, and
`ℤ` first fails: `log (1 + x)` at precision `3` is `x - x²/2`.

**`log`'s hypothesis is `(a - 1).coeff 0 = 0` and not `a.coeff 0 = 1`.**
The two agree whenever `n ≥ 1`, and at `n = 0` the first is true (both
sides are out of range) while the second is false over a nontrivial `R`.
Since `log` is total at precision `0`, the first is the hypothesis that
does not exclude a case the conclusion covers.

**Mathlib's `PowerSeries.exp` is not general enough to transport, and
that is a fact about Mathlib rather than about this library.**
`PowerSeries.exp` (`Mathlib/RingTheory/PowerSeries/Exp.lean:48`) is
defined for `[Algebra ℚ A]`, so it does not exist over `ZMod p` at any
precision, while `exp` here exists over `ZMod p` at every precision
below `p`. The companion therefore states the `[Algebra ℚ R]`
correspondence with Mathlib's series and keeps the functional equations
above as the general statements. This is recorded in "The Mathlib layer"
as a candidate for upstreaming rather than as a gap here.

## Composition

```lean
/-- `a ∘ b`, the substitution of `b` into `a`. -/
def comp (a b : TSeries R n) : TSeries R n
def comp? (a b : TSeries R n) : Option (TSeries R n)

/-- The defining equation: `a ∘ b` is `Σ_{k < n} a_k · b^k`, written as a
fold because there is no `Finset` here. -/
theorem comp_spec (a b : TSeries R n) (h : b.coeff 0 = 0) :
    comp a b = (List.range n).foldl (fun acc k => acc + C (a.coeff k) * b.pow k) 0

theorem comp_X_right (a) : comp a X = a
theorem comp_X_left  (b) (h : b.coeff 0 = 0) : comp X b = b
theorem comp_mul (a a' b) (h : b.coeff 0 = 0) : comp (a * a') b = comp a b * comp a' b
```

**The hypothesis `b.coeff 0 = 0` is not a convenience.** With
`b.coeff 0 = c` nonzero, the constant coefficient of `a ∘ b` is
`Σ_k a_k c^k`, an infinite sum with no meaning in a general commutative
ring. Take `a = 1 + x + x² + …` and `b = 1`: the answer would be
`1 + 1 + 1 + …`. Composition of formal power series is defined only when
the inner series has zero constant term, and the case where the constant
term is nilpotent, which does work, is refused: nilpotence is not
decidable in a general `R`, admitting it would put a further class on
the interface, and no consumer in this tree wants it. `comp?` returns
`none` when `b.coeff 0 ≠ 0`, and `n = 0` succeeds because the
coefficient is out of range there.

Two algorithms, with the second the intended one:

- **Horner**, `a_{n-1}`, then `acc ↦ acc * b + C a_k` downward. `n`
  truncated multiplications, `O(n · M(n))`.
- **Brent-Kung**, splitting `a` into `⌈√n⌉ blocks` of `⌈√n⌉` coefficients,
  computing the powers `b^0 … b^{⌈√n⌉}` once, evaluating each block by a
  coefficient-matrix product, then combining by Horner in `b^{⌈√n⌉}`.
  `O(√n)` truncated multiplications plus `O(n²)` coefficient operations
  for the block products. Brent and Kung, "Fast algorithms for
  manipulating formal power series" (JACM 25, 1978).

Brent-Kung is a real improvement even at schoolbook multiplication,
`O(n^{2.5})` against Horner's `O(n³)`, so unlike inversion the fast
route pays before hex-poly-fast exists. The crossover between them is a
measured number and this SPEC does not guess it. The quasi-linear
composition algorithms published since 2024 are out of scope and are
recorded in the open questions.

## Reversion

```lean
/-- The compositional inverse of `b`, given `v` inverting `b.coeff 1`. -/
def revOfUnit (b : TSeries R n) (v : R) : TSeries R n
def rev? [UnitOps R] (b : TSeries R n) : Option (TSeries R n)

theorem revOfUnit_comp (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1) :
    comp b (revOfUnit b v) = X ∧ comp (revOfUnit b v) b = X

theorem revOfUnit_coeff_one (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1)
    (h : 1 < n) : (revOfUnit b v).coeff 1 = v
```

The iteration is Newton on `y ↦ y - (comp b y - X) * inv (comp b.deriv y)`,
started from `C 0 + C v * X`, doubling the precision each step.

**The route is Newton and not Lagrange inversion, and the reason is the
whole point of this section.** Lagrange inversion computes the answer in
closed form,

```text
[x^k] rev(b) = (1/k) · [x^{k-1}] (x / b)^k,
```

and that formula divides by `k` for every `k < n`. It therefore needs
`NatInverses R (n - 1)` and does not exist over `ℤ` beyond precision
`2`. But the reversion **does** exist over `ℤ`: reverting `x + x²` gives
`x - x² + 2x³ - 5x⁴ + …`, integer coefficients throughout. So a library
that implemented reversion by Lagrange inversion would carry a
hypothesis its own answers do not need, and would refuse an input it can
compute. The Newton route uses only `comp`, which needs no invertibility
at all, and `inv` of a series whose constant term is `b.coeff 1`, which
the stated hypothesis already provides. It has no integer division
anywhere.

This is the concrete case behind the general rule for this library: an
algorithm's hypotheses are the hypotheses **that algorithm** needs, and
choosing an algorithm whose hypotheses exceed the operation's is a
design error rather than a harmless implementation detail. Lagrange
inversion stays available as a second route, used only when
`NatInverses` is in scope, where it is a useful cross-check in the
conformance suite.

Cost is `O(log n)` compositions, dominated by the last, so `O(comp(n))`.

## Degenerate-input audit

Every operation at precision `0`, and at a noninvertible constant or
linear term. This table is the checklist a reviewer runs against the
implementation.

| operation | `n = 0` | `n = 1` | constant term a nonunit | `coeff 1` a nonunit |
|---|---|---|---|---|
| `+`, `-`, `*`, `pow` | total, the zero ring | total, `≅ R` | total | total |
| `C c` | `= 0 = 1` | `= c` | total | total |
| `X` | `= 0` | `= 0` | total | total |
| `truncate m` | `m = 0` only | fine | total | total |
| `extend m` | zeros | fine | total | total |
| `mulXPow k` | `= 0` | `= 0` for `k ≥ 1` | total | total |
| `divXPow? k` | `some` at precision `0` | `some` iff `k = 0` or `coeff 0 = 0` | total | total |
| `valuation?` | `none` | `none` iff `coeff 0 = 0` | total | total |
| `deriv` | precision `0` | precision `0` | total | total |
| `integrate` | precision `1`, no inverse used | precision `2`, uses `1/1` | total | total |
| `invOfUnit a u` | returns the unique element, `hu` unsatisfiable | `= C u` | hypothesis fails, no call | irrelevant |
| `inv?` | `some`, unconditionally | `some` iff `coeff 0` a unit | `none` | irrelevant |
| `sqrtOfRoot a r v` | unique element, `hv` unsatisfiable | `= C r` | `hv` fails when `2r` is a nonunit | irrelevant |
| `exp` | `= 0 = 1`, no inverse used | `= 1` | needs `coeff 0 = 0`, not unitality | irrelevant |
| `log` | `= 0 = 1`, no inverse used | `= 0` | needs `(a-1).coeff 0 = 0` | irrelevant |
| `comp a b` | `= 0` | `= C (a.coeff 0)` | needs `b.coeff 0 = 0` | irrelevant |
| `comp?` | `some` | `some` iff `b.coeff 0 = 0` | `none` | irrelevant |
| `revOfUnit b v` | unique element, `hv` unsatisfiable | `= 0`, `hv` unsatisfiable | needs `coeff 0 = 0` | hypothesis fails |
| `rev?` | `some` | `some` | `none` when `coeff 0 ≠ 0` | `none` for `n ≥ 2` |

Three rows deserve their statement in prose because an implementation
gets them wrong in the same way each time.

**`inv?` and `rev?` succeed at precision `0` with no test.** The
constant term is out of range and the answer is the unique element of
the zero ring, which does satisfy `a * b = 1`. An implementation that
tests `UnitOps.inv? (a.coeff 0)` first returns `none` there over any
nontrivial `R`, contradicting `inv?_isSome_iff`. The test is guarded by
`0 < n`.

**`rev?` succeeds at precision `1` with no test on the linear term.**
There is no linear term, `X = 0`, and the only series with zero constant
term is `0`, whose compositional inverse is itself. An implementation
that tests `UnitOps.inv? (b.coeff 1)` returns `none`.

**`exp` and `log` at precisions `0` and `1` use no integer inverse.**
The `NatInverses R (n - 1)` hypothesis is `NatInverses R 0`, which is
vacuous, so these calls typecheck over `ℤ` and over any ring at all. An
implementation that fetches `invNat 1` unconditionally still typechecks
(the instance provides `invNat` as a total function) but computes with a
value the laws say nothing about. The fixture set covers precision `0`
and `1` over `ℤ` for exactly this reason.

## Complexity

`M(m)` is the cost of `mulUpTo m` in coefficient operations: `O(m²)`
schoolbook, and whatever hex-poly-fast later installs.

| operation | algorithm | cost |
|---|---|---|
| `+`, `-`, `truncate`, `extend`, `deriv`, `integrate` | coefficientwise | `O(n)` |
| `*` | convolution | `M(n)` |
| `pow k` | square-and-multiply | `O(log k) · M(n)` |
| `invOfUnit` | Newton, bounded steps | `O(M(n))` |
| `sqrtOfRoot` | Newton on the inverse root | `O(M(n))` |
| `log` | `integrate (deriv · inv)` | `O(M(n))` |
| `exp` | Newton with a `log` per step | `O(M(n))` |
| `comp` | Horner | `O(n · M(n))` |
| `comp` | Brent-Kung | `O(√n · M(n) + n²)` |
| `rev` | Newton with a `comp` per step | `O(comp(n))` |

The geometric sum is the load-bearing claim in four of those rows and it
holds only because the step is bounded: `Σ_{j < ⌈log₂ n⌉} M(2^j) =
O(M(n))` whenever `M` is at least linear and superadditive.

At schoolbook multiplication every row above except the two composition
rows and the reversion row ties the corresponding naive linear
recurrence, and the table should be read as a description of what
happens when `M` improves rather than as a claim of a present-day win.

## Kernel exposure

The replay closure is `coeff`, `add`, `mul`, `convCoeff`, and equality
on `TSeries R n`, together with whatever the coefficient ring exposes.
Each is `@[expose]`, and a downstream module carries a `decide +kernel`
test over `TSeries Int 8` that fails if any of them stops reducing.

Equality is where this would silently break. `Vector`'s derived
`DecidableEq` does not reduce across a module boundary, which is why
hex-basic carries `Hex.instDecidableEqVector`
(`HexBasic/ArrayDecEq.lean`) and why `Hex.Vector.ofFn'`
(`HexBasic/OfFn.lean`) exists beside it. Both are `scoped`, so
`HexTruncatedSeries` modules activate them inside `namespace Hex` and
they do not leak to consumers. A module that forgets gets a stuck
`decide`, which is loud rather than silent.

The Newton driver is in the closure, which is the second reason it is
structurally recursive on the step count. A well-founded recursion on
the precision would not reduce, and the `decide +kernel` test would fail
on `inv` at any precision.

The composition and reversion routines are **not** in the closure. They
are search-free but expensive, no proof term mentions them, and exposing
them would put a `Brent-Kung` block decomposition into the kernel for no
benefit.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexTruncatedSeries/EmitFixtures.lean` exposed as
`lean_exe hextruncatedseries_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexTruncatedSeries/series.jsonl`, and an oracle
driver at `scripts/oracle/series_sympy.py`. One tuple appended to
`ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexTruncatedSeries|hextruncatedseries_emit_fixtures|scripts/oracle/series_sympy.py|conformance-fixtures/HexTruncatedSeries/series.jsonl"
```

**The oracle is SymPy's `sympy.polys.ring_series`.** It is a truncated
power series implementation with the same operation set and the same
"precision is an argument" convention: `rs_mul`, `rs_pow`, `rs_trunc`,
`rs_series_inversion`, `rs_nth_root`, `rs_exp`, `rs_log`, `rs_subs` for
composition, and `rs_series_reversion`. SymPy is already installed for
the oracle job (`.github/workflows/ci.yml:77`), so no new dependency is
needed. python-flint is a performance comparator rather than the oracle;
see "Benchmarking".

**Coefficient domains are chosen so that every emitted operation has an
oracle.** Over `Rat`, SymPy's `ring('x', QQ)` covers the whole surface,
so every operation is emitted there. Over `Int`, `ring('x', ZZ)` covers
the ring operations, `inv` at unit constant term, composition and
reversion, and it covers `exp` and `log` only at precisions `0` through
`2`; those are exactly the precisions where `NatInverses Int (n - 1)`
holds, so nothing is emitted that cannot be checked. Testing.md's rule 2
forbids emitting an operation on an input class that gets a weaker
contract, so the `Int` fixtures at precision `3` and above simply do not
include `exp` and `log`.

Cases that must be present:

- Every operation at precision `0` and at precision `1`, over `Int` and
  over `Rat`. This is the audit table above turned into fixtures, and it
  is the half of the suite most likely to catch a real bug.
- `inv?` on an input with a nonunit constant term over `Int` (`2 + x`),
  expecting `none`, at precisions `0`, `1`, and `4`. Precision `0` must
  give `some`.
- `rev?` on `x + x²` over `Int` at precisions `0` through `6`, checking
  the integer coefficients `0, 1, -1, 2, -5, 14` and checking that no
  integer division happened. Precisions `0` and `1` must give `some`.
- `rev?` on `2x + x²` over `Int`, expecting `none` for `n ≥ 2` (the
  linear coefficient `2` is not a unit of `ℤ`) and `some` for `n ≤ 1`.
- `sqrtOfRoot` over `Rat` on `1 + x` with `r = 1` and with `r = -1`,
  checking the two answers are negatives of each other.
- `sqrtOfRoot` over `Int` on `4 + x` with `r = 2`, which must be refused
  by the checked form because `2 * r = 4` is not a unit of `ℤ`.
- `exp` and `log` over `Rat` at precisions `1` through `16`, with
  `log (exp a) = a` and `exp (a + b) = exp a * exp b` checked in Lean as
  differential tests beside the oracle comparison.
- Composition where the inner series has a nonzero constant term,
  expecting `none` from `comp?` at every precision above `0`.
- Composition of `1/(1-x)` with `x + x²` at precision `12`, which is the
  case where a Horner implementation and a Brent-Kung implementation
  must agree; both routes are emitted and compared.
- Reversion by the Newton route and by Lagrange inversion over `Rat`,
  compared against each other and against SymPy. Over `Int` only the
  Newton route is emitted, since Lagrange inversion has no `Int`
  instance to run under, and that asymmetry is itself the check that the
  hypothesis is where the SPEC says it is.
- `extend` followed by `*` against `*` followed by `extend` on `X` at
  precision `2`, recording the documented disagreement so that a later
  "simplification" that makes `extend` multiplicative fails the suite.
- `divXPow?` at `k` larger than the precision, and `divXPow?` on an
  input whose bottom `k` coefficients are not all zero.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexTruncatedSeries/Bench.lean`. Native and kernel: the kernel
suite measures `decide +kernel` on a `TSeries Int 8` product, which is
what a downstream proof pays.

Families:

- **Multiplication**, precisions 8 to 4096 over `Int` and `Rat`. The
  baseline every other family is read against.
- **Inverse**, the same ladder, Newton against the linear recurrence.
- **`exp` and `log`**, precisions 8 to 1024 over `Rat`.
- **Square root**, the same ladder over `Rat`.
- **Composition**, precisions 8 to 512, Horner against Brent-Kung. This
  family is what fixes the crossover the SPEC declines to guess.
- **Reversion**, precisions 8 to 512, Newton against Lagrange inversion
  over `Rat`.

**Comparators.** FLINT's truncated series operations on `fmpq_poly`
(`fmpq_poly_inv_series`, `fmpq_poly_exp_series`, `fmpq_poly_log_series`,
`fmpq_poly_sqrt_series`, `fmpq_poly_compose_series`,
`fmpq_poly_revert_series`) are `informational`, not `gating`. The
rationale is structural and is the same one hex-poly records for
`fmpz_poly`: FLINT's series routines are built on a tuned
Karatsuba/Toom-Cook/FFT multiplication, and this library multiplies
schoolbook until hex-poly-fast exists, so the ratio measures the
multiplication gap rather than anything about the Newton iterations.
The comparator is reclassified to `gating` when hex-poly-fast lands, and
the SPEC of that library is where the goal is written.

Two required internal checks, which matter more than the external one:

- **Newton inversion within `2x` of the linear recurrence** at every
  precision on the ladder. Not faster: at schoolbook multiplication they
  are both `O(n²)` and the recurrence has the smaller constant. A
  regression past `2x` means the step is not bounded, which is the one
  implementation mistake that turns `O(M(n))` into `O(M(n) log n)`.
- **Brent-Kung faster than Horner above precision 64**, by a margin that
  grows with the precision. Composition is the one family where the fast
  route pays before hex-poly-fast exists, so this check is the evidence
  that Brent-Kung was implemented rather than declared.

The bench target imports `HexBasic` and `Std` only, so the Mathlib-free
requirement of [SPEC/benchmarking.md](../benchmarking.md) is met without
further argument.

## The Mathlib layer

`hex-truncated-series-mathlib` identifies the type with `PowerSeries R`
modulo `X ^ n` and identifies each operation with its Mathlib
counterpart.

```lean
/-- Truncation of a power series to precision `n`. -/
def ofPowerSeries (f : PowerSeries R) : TSeries R n

theorem coeff_ofPowerSeries (f) (i) (hi : i < n) :
    (ofPowerSeries (n := n) f).coeff i = PowerSeries.coeff i f

/-- Truncation is a surjective ring homomorphism with kernel `(X ^ n)`. -/
def ofPowerSeriesHom : PowerSeries R →+* TSeries R n
theorem ofPowerSeriesHom_surjective : Function.Surjective (ofPowerSeriesHom (R := R) (n := n))
theorem ker_ofPowerSeriesHom :
    RingHom.ker (ofPowerSeriesHom (R := R) (n := n))
      = Ideal.span {(PowerSeries.X : PowerSeries R) ^ n}

/-- Hence the identification the library is named for. -/
def quotEquiv :
    (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R) ^ n}) ≃+* TSeries R n
```

`quotEquiv` is `RingHom.quotientKerEquivOfSurjective` applied to the two
theorems above, so the substance is the surjectivity and the kernel
computation and the equivalence is a corollary. Stating the ring
homomorphism first is what makes each operation's correspondence a
single equation rather than a transport through an equivalence.

The operation correspondences, each of the form "truncating commutes
with the operation":

```lean
theorem ofPowerSeries_invOfUnit (f : PowerSeries R) (u : Rˣ) :
    ofPowerSeries (n := n) (f.invOfUnit u) = invOfUnit (ofPowerSeries f) u.inv

theorem ofPowerSeries_subst (f g : PowerSeries R) (hg : PowerSeries.HasSubst g) :
    ofPowerSeries (n := n) (f.subst g) = comp (ofPowerSeries f) (ofPowerSeries g)

theorem ofPowerSeries_substInvOfIsUnit (g : PowerSeries R)
    (h0 : PowerSeries.constantCoeff g = 0) (hu : IsUnit (PowerSeries.coeff 1 g)) :
    ofPowerSeries (n := n) (g.substInvOfIsUnit hu) = revOfUnit (ofPowerSeries g) _

theorem ofPowerSeries_exp [Algebra ℚ R] (f : PowerSeries R)
    (h : PowerSeries.constantCoeff f = 0) :
    ofPowerSeries (n := n) ((PowerSeries.exp R).subst f) = exp (ofPowerSeries f)

theorem ofPowerSeries_logOf [Algebra ℚ R] (f : PowerSeries R)
    (h : PowerSeries.constantCoeff f = 1) :
    ofPowerSeries (n := n) (PowerSeries.logOf f) = log (ofPowerSeries f)
```

`Lean.Grind.CommRing R` follows from Mathlib's `CommRing R` through
`Mathlib/Algebra/Ring/GrindInstances.lean`, so the companion states its
theorems with Mathlib's class and the Mathlib-free layer's instances
apply.

**Three notes on what Mathlib has and does not have**, because they
decide the shape of the companion.

Mathlib's reversion is `PowerSeries.substInvOfIsUnit`
(`Mathlib/RingTheory/PowerSeries/Substitution.lean:566`), with
`subst_substInvOfIsUnit_left` and `subst_substInvOfIsUnit_right` under
exactly the hypotheses this library uses: zero constant coefficient and
a unit linear coefficient. So the reversion correspondence is a genuine
transport and not a restatement.

Mathlib's `exp` and `logOf` need `[Algebra ℚ A]`
(`Mathlib/RingTheory/PowerSeries/Exp.lean:43`,
`Mathlib/RingTheory/PowerSeries/Log.lean:82`), which is strictly stronger
than `NatInverses R (n - 1)`. The two correspondence theorems above are
therefore stated under `[Algebra ℚ R]` and cover less than the
Mathlib-free `exp` and `log` do. Nothing is lost: the functional
equations `log_exp`, `exp_log`, and `exp_add` are proved Mathlib-free
and hold over `ZMod p` at every precision below `p`, where Mathlib's
`exp` does not exist. A precision-indexed `PowerSeries.expTrunc` would
fix this upstream and is recorded in the open questions.

Mathlib has no square root of a power series. `Mathlib/RingTheory/
PowerSeries/Binomial.lean` has `binomialSeries`, which would give
`(1 + X)^(1/2)` over a `BinomialRing`, but that hypothesis is not the
one this library uses and the special case is not stated. The companion
therefore proves an existence and uniqueness statement itself,

```lean
theorem exists_unique_sq (f : PowerSeries R) (r : R)
    (hr : r * r = PowerSeries.constantCoeff f) (hu : IsUnit (2 * r)) :
    ∃! s : PowerSeries R, s * s = f ∧ PowerSeries.constantCoeff s = r
```

which is the `PowerSeries` version of `sqrt_unique` above and is a good
upstream candidate.

Following the project split, no theorem about `TSeries` belongs in the
companion beyond these and one correspondence lemma per public
operation.

## Milestones

1. **The type and the ring.** `TSeries`, `coeff`, `ofFn`, `ext`,
   `DecidableEq`, the ring operations, `mulUpTo`, and the
   `Lean.Grind.CommRing` instance. The `decide +kernel` test lands here,
   because that is when the `Vector` instance choice is still cheap to
   change.

2. **Precision changes.** `truncate`, `extend`, `mulXPow`, `divXPow?`,
   `valuation?`, `deriv`, `integrate`, `NatInverses`, and the
   preservation and loss theorems. `truncate_mul` is the theorem the
   rest of the library rests on and it is proved here.

3. **The Newton driver and inversion.** `newton`, `steps`,
   `two_pow_steps_ge`, `invOfUnit`, `inv?`, `invOfUnit_mul`,
   `invOfUnit_unique`, and the degenerate-precision cases of
   `inv?_isSome_iff`. At the end of it the library has a working
   quasi-linear-ready inverse and the hardest infrastructure proof is
   done.

4. **Square root, `exp`, and `log`**, with the functional equations and
   the `NatInverses Int 1` boundary case exercised.

5. **Composition and reversion.** Horner first, then Brent-Kung, then
   Newton reversion, then Lagrange inversion as the second route under
   `NatInverses`.

6. **The companion**, and the conformance and bench suites.

## File organisation

```
HexTruncatedSeries/
  Defs.lean         -- TSeries, coeff, ofFn, ext, DecidableEq
  Ring.lean         -- convCoeff, the ring operations, mulUpTo, pow
  Precision.lean    -- truncate, extend, mulXPow, divXPow?, deriv, integrate
  Classes.lean      -- UnitOps, LawfulUnitOps, NatInverses and its instances
  Newton.lean       -- the driver, steps, two_pow_steps_ge
  Inverse.lean      -- invOfUnit, inv?, uniqueness
  Sqrt.lean         -- sqrtOfRoot and uniqueness
  ExpLog.lean       -- exp, log, the functional equations
  Comp.lean         -- Horner and Brent-Kung
  Revert.lean       -- Newton reversion, and Lagrange as the second route
HexTruncatedSeries.lean
HexTruncatedSeriesMathlib/
  Basic.lean        -- ofPowerSeries, the ring homomorphism, the kernel, quotEquiv
  Ops.lean          -- the ring and precision correspondences
  Newton.lean       -- inverse, sqrt, exp, log, subst, substInv correspondences
HexTruncatedSeriesMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexTruncatedSeries:
    deps: [HexBasic]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: FLINT fmpq_poly truncated series routines via python-flint
          class: informational
          rationale: "FLINT's series routines run on a tuned Karatsuba/Toom-Cook/FFT multiplication while this library multiplies schoolbook until hex-poly-fast exists, so the measured ratio reports the multiplication gap rather than the Newton iterations. Reclassified to gating when hex-poly-fast lands."
      input_families:
        - name: multiplication
          description: truncated products at precisions 8 to 4096 over Int and Rat
        - name: inverse
          description: Newton inversion against the linear recurrence on the same ladder
        - name: exp-log
          description: exp and log at precisions 8 to 1024 over Rat
        - name: sqrt
          description: square root at a supplied constant root over Rat
        - name: composition
          description: Horner against Brent-Kung at precisions 8 to 512
        - name: reversion
          description: Newton reversion against Lagrange inversion over Rat
  HexTruncatedSeriesMathlib:
    deps: [HexTruncatedSeries]
    mathlib: true
    done_through: 0
    status: planned
```

`HexBasic` is the only computational dependency, and the check that
matters when the library is scaffolded is that it stays that way:
`scripts/check_dag.py` cross-checks `libraries.yml` against the
lakefile, so an accidental `import HexPoly` fails there rather than at
release time.

## Open questions

- **Where the convolution fold should live.** hex-poly has it
  (`HexPoly/Euclid/MulRing.lean`) and this library will have its own,
  because hex-poly declares no dependencies and so cannot import
  `HexBasic`. The same constraint already forces hex-poly to hand-copy
  `HexBasic.ArrayDecEq`'s workaround (`HexPoly/Dense.lean:45-54`). Giving
  hex-poly a dependency on hex-basic would let both use one copy of both
  things, and it is a change to hex-poly rather than to this library, so
  it is recorded here and decided there.
- **Whether `ZMod64 p` instances belong here.** `NatInverses (ZMod64 p) m`
  for `m < p` and `UnitOps (ZMod64 p)` are the instances that make `exp`,
  `log`, and `sqrt` useful over a small prime field, and they need
  hex-mod-arith. Adding that dependency would give the series library a
  second edge for the sake of two instances. The alternative is that
  hex-poly-fast, or a small `hex-truncated-series-modular`, supplies
  them. The measurement that settles it is whether any consumer wants
  the modular instances without also wanting hex-poly.
- **The Horner/Brent-Kung crossover**, and whether Brent-Kung's block
  size should be `⌈√n⌉` or tuned. Both are measured numbers and this
  SPEC does not guess them.
- **Whether quasi-linear composition belongs here later.** Composition
  of power series in `O(M(n) log n)` was published in 2024 (Kinoshita
  and Li) and supersedes Brent-Kung asymptotically. It is out of scope
  now because its constant factor is unmeasured in this setting and
  because Brent-Kung is the algorithm with an accessible correctness
  argument. Worth revisiting once composition is a measured bottleneck
  in a real consumer.
- **Whether a precision-indexed `exp` belongs upstream.** Mathlib's
  `PowerSeries.exp` needs `[Algebra ℚ A]` and so cannot speak about
  `ZMod p` at any precision, while the truncated `exp` here exists at
  every precision below `p`. An upstream `PowerSeries.expTrunc` under a
  precision-indexed hypothesis would let the companion transport rather
  than restate. The same applies to the square root, where Mathlib has
  no statement at all.
- **Whether `steps n` should be `⌈log₂ n⌉` or `Nat.log2 n + 1`.** The
  loose bound costs at most one extra full-precision multiplication and
  may have a much easier proof of `two_pow_steps_ge`. This is a decision
  to make with the proof in hand, and the cost of getting it wrong is
  one multiplication.
