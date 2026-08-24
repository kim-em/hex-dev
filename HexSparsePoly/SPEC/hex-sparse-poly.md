# hex-sparse-poly (canonical sparse univariate polynomials, depends on hex-poly + hex-basic)

Univariate polynomials stored as a sorted array of exponent/coefficient
terms, for inputs whose exponents are large and whose number of nonzero
coefficients is small. Mathlib-free. The companion
`hex-sparse-poly-mathlib` supplies the ring equivalence with
`Polynomial R` and the correspondence lemmas.

This SPEC expands the "Sparse univariate polynomials" bullet of
[future-work](../../SPEC/future-work.md). It sits beside
[hex-poly](../../HexPoly/SPEC/hex-poly.md) rather than inside it, and it
converts to and from `DensePoly R` explicitly at a named boundary. It
does **not** introduce a common interface over the two representations.
The reasoning is under "No swappable polynomial abstraction" below, and
the same decision is recorded in
[future-work](../../SPEC/future-work.md) under "Swappable polynomial
representations (deferred)".

## Why this library exists

**Dense storage is linear in the exponent. Sparse storage is linear in
the number of terms.** `x^1000000 − 1` is two terms against a million
coefficients. `DensePoly` allocates and traverses the million either
way: `size` is the coefficient count, addition is a coefficientwise
zip, and multiplication is the schoolbook convolution over the whole
array. Nothing about that is wrong, and it is the right shape for the
degrees the factorisation work actually sees, but it makes a two-term
polynomial of degree `10^6` cost a million operations to add to itself.

**Substituting a power of `x` is the operation that produces such
inputs.** `f(x^k)` multiplies every exponent by `k` and leaves the
coefficients alone. In the sparse representation the cost is one pass
over the terms, and for `k ≥ 1` the result has the same number of terms
as the input.
In the dense representation the cost and the size are both `k` times the
input degree.

**The identified consumer is the cyclotomic construction.**
`Φ_{p^k}(x) = Φ_p(x^{p^{k-1}})`, so the sparse family among the
cyclotomics is exactly the one this representation stores well: `Φ_p`
has degree `p − 1` and all `p` of its coefficients are `1`, so it is
dense, and the `p^k` members are that dense polynomial with its
exponents scaled. The
cyclotomic library specified in [hex-cyclotomic](../../SPEC/Libraries/hex-cyclotomic.md)
builds `ZPoly` and leaves sparse output to an adapter over this library
at a consumer that holds both. That adapter is downstream and is not a
dependency in either direction: nothing here knows what a cyclotomic
polynomial is.

**Dense stays the default.** Berlekamp-Zassenhaus, hex-poly-z,
hex-resultant, and hex-number-field all hold `DensePoly` and see full
coefficient vectors at moderate degree. On those inputs the sparse
representation costs a constant factor more on every operation that
scans the coefficients, and asymptotically more on the two the
complexity table below records: `coeff`, which is `O(log t)` here
against `O(1)` there, and multiplication, which carries a logarithmic
factor the dense convolution does not. This library is for the other
shape of input and does not ask any existing consumer to change.

**One library, honestly sized.** There is one identified consumer today.
The scope below is therefore the representation, its arithmetic, the
operations that keep sparsity, the conversions, and the measurements
that say where the crossover is. It is not a second polynomial
ecosystem.

## No swappable polynomial abstraction

This library introduces no `PolyOps` class, no `LawfulPolyOps` class,
and no drop-in replacement of `DensePoly` by `SparsePoly` at a consumer.
Callers name the representation they hold and convert explicitly.

The reason is that the two representations do not have the same useful
operations. `DensePoly` has `O(1)` coefficient access by index and this
library has `O(log t)`. `DensePoly` has no cheap `f(x^k)` and this
library has no cheap remainder sequence. The complexity of the *same*
named operation differs by a factor of the degree in both directions
depending on the input, so a caller written against an interface cannot
predict its own cost, which is the one thing a polynomial caller most
needs to predict.

Normalisation differs too. `DensePoly` maintains "no trailing zeros",
which is a condition on one end of the array. This library maintains
"strictly increasing exponents and no stored zeros", which is a
condition on every adjacent pair and every entry. An interface that
tried to state a shared canonical-form law would state neither.

The resolution is the one [future-work](../../SPEC/future-work.md) already
records: build the second representation with explicit conversions
first, and reconsider a common interface only after several real
consumers have shown which operations belong in it. Today there is one
consumer, so there is no evidence to design against.

## Scope

In scope: the canonical representation and its construction from
arbitrary term arrays; addition, subtraction, negation, multiplication,
powering, scalar multiplication, and monomial multiplication;
evaluation, derivative, and substitution; equality and decidable
equality; `toDense` and `ofDense` with the homomorphism laws and both
round trips; and gcd and division defined by conversion through
`DensePoly`.

Not in scope: a sparse gcd or a sparse division algorithm (see "Gcd and
division convert through the dense representation"); factorisation of
any kind; multivariate sparsity, which is
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md); and cyclotomic
polynomials, which are a downstream consumer.

## Representation

```lean
namespace Hex

/-- A term array is canonical when its exponents are strictly increasing
and no stored coefficient is zero. -/
@[expose]
def SparsePolyCanonical {R : Type u} [Zero R] [DecidableEq R]
    (terms : Array (Nat × R)) : Prop :=
  terms.toList.Pairwise (fun a b => a.1 < b.1) ∧ ∀ t ∈ terms, t.2 ≠ 0

/-- A univariate polynomial over `R` as a canonical sorted array of
`(exponent, coefficient)` terms. -/
structure SparsePoly (R : Type u) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  canonical : SparsePolyCanonical terms
```

Exponents ascend, matching `DensePoly`'s ascending index order and the
`#p[a₀, a₁, …]` literal, so a reader moving between the two files reads
both left to right in increasing degree.

The top-level predicate name follows `DensePolyNormalized`
(`HexPoly/Dense.lean:26`), which is the existing sibling and is
`@[expose]` for the same reason: the invariant appears in the type of
every constructor, so a downstream kernel `decide` has to see its body.

**Both halves of the invariant are load-bearing, and each rules out a
different failure.**

*Duplicate exponents.* `#[(1, 2), (1, 3)]` and `#[(1, 5)]` denote the
same polynomial. A merely sorted invariant (`≤` between adjacent
exponents) admits the first, so structural equality would not be
semantic equality and `DecidableEq` would report `5x ≠ 5x`. Strict
increase forbids duplicates and sortedness together, in one condition.
Every operation that can produce two terms at the same exponent (`mul`,
`ofTerms` on unsorted input, `compose`, and `substPow 0`) must combine
them.

*Stored zeros.* `#[(0, 0)]` and `#[]` denote the same polynomial, so an
invariant that only ordered the exponents would again break structural
equality. The zero-free condition forbids it. The cases that produce a
zero coefficient in a term that is structurally present are worth
listing, because each is a place an implementation forgets to
canonicalise:

- addition and subtraction at a matching exponent: `(x + 1) + (−x − 1)`
  cancels at both exponents and the result is the empty array;
- multiplication when coefficient products cancel in a sum, and
  multiplication over a coefficient ring with zero divisors, where a
  single product `c * d` is zero with `c` and `d` nonzero;
- scalar multiplication by a zero divisor, and by zero;
- the derivative in positive characteristic: over `ZMod64 p` the
  derivative of `x^p` is `p·x^(p-1) = 0`, so the term disappears rather
  than acquiring a zero coefficient, and the derivative of a `p`-sparse
  polynomial can be the zero polynomial;
- `substPow 0`, which maps every term to exponent `0` and can sum to
  zero.

`Pairwise` rather than a condition on adjacent pairs: `<` on `Nat` is
transitive, so the two are equivalent, and the pairwise form is the one
induction over the array wants. The implementation checks the adjacent
form, which is linear, and the equivalence is a lemma.

Going through `terms.toList` in the predicate is deliberate and matches
the `DecidableEq` route below.

`Nat` exponents are unbounded, so there is no overflow condition to
state and no bound to carry. The size hazard moves entirely to
`toDense`, which allocates `degree + 1` coefficients. That is stated
where `toDense` is specified.

Per design principle 10, `terms` is read through the API below
(`coeff`, `support`, `numTerms`, `degree?`, `leadingCoeff`, and the
ordered `toTerms` and `foldTerms`) and not directly by consumers, so the
parallel-array variant in the open questions stays available.

**Equality does not come for free.** `deriving DecidableEq` elaborates
on a structure with a proof field, and using it here would still be
wrong: a derived instance delegates to a generated `decEq` whose body is
unavailable across a module boundary, so a downstream `decide` stalls.
`HexBasic/ArrayDecEq.lean` records that gap alongside the two others it
works around, and names `Vector` as the standard-library type whose own
instance is derived and therefore has it.

So the instance is written by hand. It compares `terms` and recovers
structure equality by proof irrelevance, and the array comparison routes
through `List` equality rather than `Array.instDecidableEq`, whose
nonempty case delegates to the non-`@[expose]`
`Array.instDecidableEqImpl`. That is the hazard `HexPoly/Dense.lean`
documents at its own instance and
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) repeats, recorded in
[progress/lean4-array-decidableeq-module-repro.md](../../progress/lean4-array-decidableeq-module-repro.md),
which is the reproduction the workaround exists for. The pinned
toolchain still needs it.

Unlike hex-poly, which has no dependencies and therefore carries a local
copy of the workaround, this library depends on hex-basic and activates
the scoped `Hex.instDecidableEqArray` from `HexBasic/ArrayDecEq.lean`
instead. That instance already carries the `@[csimp]` redirect back to
`Array.instDecidableEq`, so compiled code keeps the `Array` comparison
and the `List` conversion happens only during kernel reduction.

The stored element type is `Nat × R`, and `Prod`'s `DecidableEq` is
written out in `Init.Core` rather than derived, so it is not
expected to be a second stall. "Not expected" is not "checked": the
module-boundary probe in the conformance list below exercises the
production equality path under `module` and `public import`, which is
what decides it.

## Canonical construction

`ofTerms` is the only constructor that accepts arbitrary input, and it
is where the invariant is established for input that has not been
canonicalised. The specialised operations below build canonical arrays
directly and prove that they do, each on its own.

```lean
namespace Hex.SparsePoly

/-- Add `c · x^e` to `s`, combining with an existing term at `e` and
deleting the term when the sum is zero.

Kernel-facing specification (a single ordered `List` insert); compiled
code uses `Hex.SparsePoly.addTermImpl`, the value-equal binary search and
in-place array update selected by `Hex.SparsePoly.addTerm_eq_impl`. -/
@[expose]
noncomputable def addTerm [Add R] (s : SparsePoly R) (e : Nat) (c : R) :
    SparsePoly R

/-- The canonical polynomial with the given terms. Exponents may repeat
and may appear in any order, and coefficients at equal exponents are summed
and zero results are dropped. -/
@[expose]
noncomputable def ofTerms [Add R] (ts : Array (Nat × R)) : SparsePoly R :=
  ts.foldl (fun s t => s.addTerm t.1 t.2) 0

def monomial (e : Nat) (c : R) : SparsePoly R
def C (c : R) : SparsePoly R
def X [One R] : SparsePoly R

instance : Zero (SparsePoly R)      -- the empty term array
instance [One R] : One (SparsePoly R)

/-- The coefficient at `e`. Kernel-facing specification (an ordered
`List` lookup); compiled code uses `Hex.SparsePoly.coeffImpl`, the
value-equal binary search selected by `Hex.SparsePoly.coeff_eq_impl`. -/
@[expose]
noncomputable def coeff (s : SparsePoly R) (e : Nat) : R

def support (s : SparsePoly R) : Array Nat
def numTerms (s : SparsePoly R) : Nat
def degree? (s : SparsePoly R) : Option Nat
def leadingCoeff (s : SparsePoly R) : R
def isZero (s : SparsePoly R) : Bool

/-- The stored terms in increasing exponent order. -/
def toTerms (s : SparsePoly R) : List (Nat × R)

/-- Fold over the stored terms in increasing exponent order, `O(t)`. -/
def foldTerms {β : Type v} (s : SparsePoly R) (f : β → Nat → R → β)
    (init : β) : β
```

`toTerms` and `foldTerms` are how a consumer iterates. Without them the
encapsulation rule above would leave a serializer, a fixture emitter, or
a downstream sparse algorithm with no ordered access short of calling
`coeff` once per support entry, which is `O(t log t)` for something that
should cost `O(t)`. `foldTerms` is the one used in the emitter and in
the correspondence proofs. [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md)
carries the same pair for the same reason.

`addTerm` does one of three things at `e`: insert a new term when
`c ≠ 0` and `e` is absent, replace the existing coefficient by the sum
when the sum is nonzero, and delete the term when the sum is zero. All
three preserve the invariant, and the proof that they do is the one
nontrivial proof in the milestone. Both hazards listed above are handled
here for arbitrary input, and each specialised operation below discharges
them again for its own output.

Following design principle 11, the public `addTerm` and `coeff` are
`noncomputable` specifications written as ordered `List` operations, and
the binary search lives in `addTermImpl` and `coeffImpl` behind a proved
`@[csimp]` equality. The reason is the same one the principle gives: an
`Array` search inside a loop does not reduce cheaply in the kernel, and
both of these are in the `decide` closure below. `DensePoly.eval`,
`DensePoly.compose`, and `DensePoly.derivative` are the existing
instances of exactly this split.

`ofTerms` is a fold of `addTerm`, so canonicality is immediate by
induction and the characterisation needs no reordering:

```lean
/-- The coefficient of `ofTerms ts` at `e` is the sum, in input order, of
the coefficients of the terms of `ts` at `e`. -/
theorem coeff_ofTerms [Add R] (hzero : ∀ c : R, 0 + c = c)
    (ts : Array (Nat × R)) (e : Nat) :
    (ofTerms ts).coeff e =
      (ts.filter (fun t => t.1 = e)).foldl (fun a t => a + t.2) 0
```

The `hzero` hypothesis is not decoration and `[Add R]` alone does not
give it: `addTerm` inserts `c` where the fold on the right computes
`0 + c`, so the two agree only once `0` is a left identity. It is an
explicit hypothesis rather than a `Std.LawfulLeftIdentity` instance
argument, because `HexBasic/Fold.lean` deliberately keeps its identity
instances file-local to avoid a second global resolution path, so a
class-valued version would make every caller install a local instance.
A coefficient type with `Lean.Grind.Semiring` discharges `hzero` from
`add_zero` and `add_comm`.

Nothing else is needed. In particular the sort-and-combine twin needs no
more, **because the sort is stable**: a stable sort by exponent preserves
the input order inside each equal-exponent block, so the combining pass
computes the same left fold per exponent that `ofTerms` computes, and
neither associativity nor commutativity is used. If an implementation
ever reorders within a block or reduces it as a tree, that equality needs
`List.foldl_add_perm` from `HexBasic/Fold.lean` and a
`Lean.Grind.Semiring` coefficient type instead. Stability is therefore a
requirement on the implementation and not a detail of it.

`ofTerms` as written above is the kernel-facing specification for the
same reason `addTerm` is: it is a fold of a small insert, it has no
sort, and it reduces. Its `@[csimp]` twin sorts the input by exponent
(stably), combines each equal-exponent block in one pass, and drops the
zeros, which is `O(m log m)` on `m` input terms against the
specification's `O(m²)` worst case. `mul` is defined through `ofTerms`,
so this is the only place the sort appears.

The literal
`#sp[(e₀, c₀), (e₁, c₁), …]` abbreviates `ofTerms #[…]`, mirroring
`#p[…]` for `DensePoly`, and inherits the same "any order, duplicates
summed, zeros dropped" behaviour.

`coeff` binary searches the term array, so it is `O(log t)` rather than
`DensePoly`'s `O(1)`. `degree? 0 = none`, matching
`DensePoly.degree?`. `leadingCoeff` of the zero polynomial is `0`.

Canonicality is what makes the extensionality theorem true, and
everything below is proved from it:

```lean
@[ext] theorem ext_coeff {s t : SparsePoly R} (h : ∀ e, s.coeff e = t.coeff e) :
    s = t
```

## Arithmetic

```lean
def add [Add R] (s t : SparsePoly R) : SparsePoly R
def neg [Sub R] (s : SparsePoly R) : SparsePoly R
def sub [Sub R] (s t : SparsePoly R) : SparsePoly R
def mul [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R
def pow [One R] [Add R] [Mul R] (s : SparsePoly R) (n : Nat) : SparsePoly R
def scale [Mul R] (c : R) (s : SparsePoly R) : SparsePoly R
def mulMonomial [Mul R] (e : Nat) (c : R) (s : SparsePoly R) : SparsePoly R

instance [Add R] : Add (SparsePoly R)
instance [Sub R] : Sub (SparsePoly R)
instance [Sub R] : Neg (SparsePoly R)
instance [Add R] [Mul R] : Mul (SparsePoly R)
instance [One R] [Add R] [Mul R] : Pow (SparsePoly R) Nat
instance [Add R] [Mul R] : Dvd (SparsePoly R)
```

`Add`, `Sub`, `Neg`, and `Mul` are registered under the hypotheses
`HexPoly/Operations.lean` uses for `DensePoly` (lines 380, 417, 460, and
972), so `+`, `-`, and `*` are available on `SparsePoly` and the theorem
statements below and in the conversion section can use them. `Pow` is
registered from `pow`, which `Mul` and `One` do not synthesize on their
own, and which [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) lists
among its instances for the same reason. `Dvd` is `∃ r, q = p * r`,
matching `HexPoly/Euclid/DivGcd.lean:1194` rather than declaring a second
convention.

Typeclass hypotheses go on the individual operations, as in
[hex-poly](../../HexPoly/SPEC/hex-poly.md), rather than on the type.
The laws are stated against `Lean.Grind.Semiring` and
`Lean.Grind.CommRing`, which is what the existing libraries use where a
full ring is needed. No Mathlib class appears here. The `≃+*` lives in
the companion.

`add` is a linear merge of two sorted arrays. At a matching exponent it
sums and, when the sum is zero, emits nothing. This is the cancellation
case, and it is `O(s + t)` with no search and no sort.

`neg` takes `[Sub R]` and not `[Neg R]`, matching
`DensePoly`'s `Neg` instance (`HexPoly/Operations.lean:460`), which is
specified as subtraction from zero and compiled as a coefficient map.
Over a ring, `0 − c = 0` exactly when `c = 0`, so the exponents and the
term count are unchanged. `[Sub R]` alone does not supply that fact, so
the implementation applies the same zero filter as `scale`, and the laws
below carry the ring hypothesis under which the filter removes nothing.

`scale c s` maps the coefficients and must drop the terms whose product
is zero. `c = 0` gives the zero polynomial, and a zero divisor `c` can
delete an interior term while leaving its neighbours, so the result is
not a coefficientwise image of the input array.

`mulMonomial e c s` adds `e` to every exponent and multiplies every
coefficient by `c`. The exponent map is strictly monotone, so no
re-sorting and no combining is needed and the only canonicalisation is
dropping the terms whose coefficient product is zero. This is the cheap
shift, `O(s)`, and it is what `mul` is built from.

**Multiplication.** The specification is the pairwise product,
canonicalised:

```lean
def mul (s t : SparsePoly R) : SparsePoly R :=
  ofTerms (s.terms.flatMap fun a => t.terms.map fun b => (a.1 + b.1, a.2 * b.2))
```

Every pair of exponents contributes, exponent sums collide freely, and
`ofTerms` combines the collisions and drops what cancels. This is
kernel-facing and obviously correct, and its cost is `O(s·t)` products
plus the `ofTerms` fold.

Three implementation shapes are worth measuring behind a `@[csimp]`
equality, and the SPEC does not choose between them in advance:

1. **Produce, sort, combine.** Build the `s·t` products, sort by
   exponent, combine adjacent equal exponents. `O(s·t·log(s·t))`, with
   the whole product array resident.
2. **Heap merge.** Keep `min(s, t)` shifted copies of the smaller
   operand in a heap keyed on the current exponent and pop in order, so
   the output is produced sorted and only the heap is resident.
   `O(s·t·log(min(s, t) + 1))`, written with the `+ 1` because a
   one-term operand makes the heap trivial and the logarithm zero. It is
   Johnson's algorithm as used by Monagan and Pearce for sparse
   multiplication.
3. **Accumulate in a map.** Fold the products into an
   `Std.ExtTreeMap Nat R`, then read the ordered term list.
   `O(s·t·log(s·t))` with a different constant and no separate sort.

The heap is the one with the better bound and the worse constant. The
results of the "sparse-multiplication" bench family below determine which
one is implemented, and the specification does not change whichever wins.

*Measured (Phase 4, see
[reports/hex-sparse-poly-performance.md](../../reports/hex-sparse-poly-performance.md)):*
the `Std.ExtTreeMap` accumulation wins both collision shapes by about
3× over sort-and-combine (6.0 ms vs 18.0 ms at 256 low-collision terms;
2.7 ms vs 8.4 ms at 256 high-collision terms), and the heap merge's
constant loses it every measured size (75.6 ms and 42.2 ms at the same
points), exactly the outcome the paragraph above anticipated. The
tree accumulation is therefore the selected `@[csimp]` implementation;
all three candidates agreed on result hashes at every common
parameter.

`pow` is binary powering over `mul`. A caller wanting `f(x^k)` should
call `substPow` rather than powering, and the SPEC says so because
getting this wrong is the whole cost difference the library exists for.

The laws, stated as theorems rather than through a class:

```lean
theorem coeff_add [Lean.Grind.Semiring R] (s t : SparsePoly R) (e : Nat) :
    (s.add t).coeff e = s.coeff e + t.coeff e
theorem coeff_mulMonomial [Lean.Grind.Semiring R] (s) (e c f) :
    (mulMonomial e c s).coeff f = if e ≤ f then c * s.coeff (f - e) else 0
theorem add_comm, add_assoc, add_zero, mul_comm, mul_assoc, mul_one, mul_zero,
  left_distrib, right_distrib
```

with `mul_comm` under `Lean.Grind.CommRing`. As implemented, the
multiplicative laws (and `coeff_mul`) all sit at `Lean.Grind.CommRing`:
they are proved by transport through `toDense`, and the dense layer
proves its own multiplication laws at that class. Every consumer type
in the project is a `CommRing`, and if the dense laws are ever weakened
to `Semiring` the sparse statements follow at no cost, exactly as with
`divModMonic_spec` below. Every public operation
carries its own coefficient lemma in the same shape (`coeff_zero`,
`coeff_one`, `coeff_C`, `coeff_X`, `coeff_monomial`, `coeff_neg`,
`coeff_sub`, `coeff_scale`, `coeff_pow`), since the coefficient function
is what `ext_coeff` reduces every equality to. `coeff_mul` is the
convolution, and it is proved by transport through `toDense` rather than
by a double sum over the term arrays. The conversion section says why.

## Evaluation, derivative, and substitution

```lean
def eval [Add R] [Mul R] (s : SparsePoly R) (x : R) : R
def derivative [NatCast R] [Mul R] (s : SparsePoly R) : SparsePoly R
def substPow [Add R] (s : SparsePoly R) (k : Nat) : SparsePoly R
def substScale [Mul R] (s : SparsePoly R) (a : R) : SparsePoly R
def compose [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R
```

The hypotheses match the corresponding `DensePoly` operations
(`eval`, `derivative`, and `compose` in `HexPoly/Operations.lean`), so
the agreement theorems below need no extra assumption on either side.
`substPow` needs `[Add R]` only for the `k = 0` case, which sums the
coefficients.

**Evaluation runs Horner over the exponent gaps.** Reading the terms
from the top, the accumulator is multiplied by `x^(eᵢ − eᵢ₋₁)` before
each coefficient is added, and the whole is multiplied by `x^e₀` at the
end. Each gap power is one binary powering, so, writing `m` for the
term count and `n` for the degree, the cost is `m` additions and
`Σᵢ O(log gapᵢ)` multiplications, which is `O(m · log(n/m + 1))` by
concavity, against `DensePoly`'s `O(n)`. For
`x^1000000 − 1` that is about forty multiplications rather than a
million.

```lean
theorem eval_toDense [Lean.Grind.Semiring R] (s : SparsePoly R) (x : R) :
    s.eval x = s.toDense.eval x
```

`Lean.Grind.Semiring` and not `Lean.Grind.CommRing`. Gap Horner and
dense Horner run in the same orientation and the gap form only skips the
zero coefficients, so the proof needs associativity of multiplication,
`x^a * x^b = x^(a+b)`, and the zero and one laws. It does not commute a
coefficient past a power of `x`, so commutativity is not required. That
is a different situation from `DensePoly.eval_mul_commring`, which is
multiplicativity of evaluation and does need it.

**The derivative must canonicalise.** `c · x^e` maps to
`(e : R) * c · x^(e-1)`, and the `e = 0` term is dropped. The exponent
map `e ↦ e − 1` is strictly monotone on the terms that survive, so the
order is preserved and nothing needs re-sorting or combining. What is
needed is the zero filter, because `(e : R) * c` can vanish: over
`ZMod64 p` every exponent divisible by `p` produces a zero coefficient,
and the derivative of `x^p + x^(2p)` is the zero polynomial, so a
polynomial all of whose exponents are divisible by `p` has zero
derivative. An
implementation that maps the array without filtering produces a
structurally nonzero representation of `0`, which then compares unequal
to `0`. This is the invariant hazard most likely to be missed, so it
gets one of the invariant cases in the conformance list below rather
than only an oracle case.

**Substituting a power of `x` is the operation that stays sparse.**
`substPow s k` multiplies every exponent by `k`. For `k ≥ 1` the map is
strictly monotone, so the term count, the coefficients, and the order
are all unchanged and the cost is `O(t)` with no canonicalisation at
all. For `k = 0` every term lands on exponent `0`, so the result is
`C (Σ coefficients)` and the sum can be zero. The `k = 0` case is
therefore not a special case to reject but a canonicalisation to
perform, and it is a conformance case.

`substScale s a` maps `c · x^e` to `(c · a^e) · x^e`, computing the
powers of `a` from the exponent gaps as `eval` does. Exponents are
unchanged. Coefficients can vanish when `a` is a zero divisor or zero,
so the zero filter applies.

**General substitution does not stay sparse and does not promise to.**
`compose s t` is `Σ cₑ · t^e`, computed in increasing exponent with the
powers of `t` obtained by binary powering from the gaps.

Its cost is not a function of the output size. If `t` has `u` terms then
the fully expanded `t^e` has up to `u^e` products, canonicalisation may
collapse many of them, and a later accumulation may cancel a large
intermediate down to a small result. So the honest bound is the sum of
the multiplication costs over the powering and accumulation schedule,
each priced by whichever `mul` implementation is selected, and the
complexity table records it that way rather than in terms of the answer.
The specification is the coefficient identity and the agreement with
`DensePoly.compose`.

```lean
theorem coeff_derivative, derivative_add, derivative_mul
theorem substPow_eq_compose (s) (k) : s.substPow k = s.compose (monomial k 1)
theorem substScale_eq_compose (s) (a) : s.substScale a = s.compose (monomial 1 a)
theorem coeff_substScale (s) (a) (e) : (s.substScale a).coeff e = s.coeff e * a ^ e
theorem eval_substPow (s) (k) (x) : (s.substPow k).eval x = s.eval (x ^ k)
theorem eval_compose (s t) (x) : (s.compose t).eval x = s.eval (t.eval x)
```

Each agreement with a `DensePoly` operation is declared once, in the
conversion section below, under the name `<operation>_toDense`. This
section states only the facts that are about the sparse operations
themselves.

`substPow_eq_compose` is the statement that the fast path and the
general path agree, and it is what lets the cyclotomic adapter use
`substPow` and reason with `compose`. `substScale_eq_compose` is the
same statement for argument scaling, with the degree-one monomial
`a · x` in place of `x^k`.

## Conversion to and from the dense representation

```lean
/-- The array-level workers, stated separately so the round trips can
name their hypotheses. -/
def coeffsOfTerms (ts : Array (Nat × R)) : Array R
def termsOfCoeffs (cs : Array R) : Array (Nat × R)

def toDense (s : SparsePoly R) : DensePoly R

/-- Kernel-facing specification (an ordered `List` walk); compiled code
uses `Hex.SparsePoly.ofDenseImpl`, the value-equal array pass selected by
`Hex.SparsePoly.ofDense_eq_impl`. -/
@[expose]
noncomputable def ofDense (p : DensePoly R) : SparsePoly R
```

`toDense` allocates `degree + 1` coefficients and writes each stored
term into its slot. `ofDense` keeps the nonzero coefficients with their
indices, and it carries the same `noncomputable` specification and
`@[csimp]` twin as `addTerm` and `coeff`, for the same reason: it is in
the `decide` closure and an array pass inside a loop does not reduce
cheaply.

Semantics first, since the coefficient statements are what everything
else is proved from:

```lean
theorem coeff_toDense (s : SparsePoly R) (e : Nat) : s.toDense.coeff e = s.coeff e
theorem coeff_ofDense (p : DensePoly R) (e : Nat) : (ofDense p).coeff e = p.coeff e
```

Both conversions are ring homomorphisms, which is what makes the dense
library usable as the specification of this one:

```lean
theorem toDense_zero, toDense_one, toDense_add, toDense_neg, toDense_mul
theorem ofDense_zero, ofDense_one, ofDense_add, ofDense_neg, ofDense_mul
theorem toDense_monomial (e c) : (monomial e c).toDense = DensePoly.monomial e c
theorem eval_toDense, derivative_toDense, compose_toDense, substPow_toDense
theorem substScale_toDense (s : SparsePoly R) (a : R) :
    (s.substScale a).toDense = s.toDense.compose (DensePoly.monomial 1 a)
```

The degree boundary transports too, and the Euclidean section needs it
separately from the coefficients, since a leading coefficient is a
coefficient *at the degree* and `coeff_toDense` alone says nothing about
where the degree is:

```lean
theorem degree?_toDense (s : SparsePoly R) : s.toDense.degree? = s.degree?
theorem leadingCoeff_toDense (s : SparsePoly R) :
    s.toDense.leadingCoeff = s.leadingCoeff
theorem monic_toDense (s : SparsePoly R) : s.toDense.Monic ↔ s.Monic
```

`toDense_mul` is where `coeff_mul` comes from: the convolution is
already proved for `DensePoly`, and transporting it is shorter than
redoing the double sum over the sparse term arrays.

### The round trips and the hypotheses they need

On the bundled types both directions hold unconditionally, because each
type carries its canonical form as a field:

```lean
theorem ofDense_toDense (s : SparsePoly R) : ofDense s.toDense = s
theorem toDense_ofDense (p : DensePoly R) : (ofDense p).toDense = p
```

That is the useful statement, and it is also the statement that hides
where the content is. The content is visible at the array level, where
each direction needs exactly one canonicality hypothesis and is false
without it:

```lean
theorem terms_coeffs {ts : Array (Nat × R)}
    (h : SparsePolyCanonical ts) : termsOfCoeffs (coeffsOfTerms ts) = ts

theorem coeffs_terms {cs : Array R}
    (h : DensePolyNormalized cs) : coeffsOfTerms (termsOfCoeffs cs) = cs
```

Both hypotheses are necessary, and each half of
`SparsePolyCanonical` is necessary separately:

- Drop the zero-free half: `ts = #[(0, 0)]` has
  `coeffsOfTerms ts = #[0]`, and `termsOfCoeffs #[0] = #[]`, so the
  round trip returns `#[] ≠ ts`.
- Drop the strictly-increasing half for duplicates:
  `ts = #[(1, 2), (1, 3)]` writes exponent `1` twice, so
  `coeffsOfTerms ts` is `#[0, 2]` or `#[0, 3]` depending on the write
  order and the round trip returns `#[(1, 2)]` or `#[(1, 3)]`. Neither
  is `ts`, and neither is the `#[(1, 5)]` the polynomial actually
  denotes. The workers are conversions, not canonicalisers. Summing
  duplicates is `ofTerms`'s job and happens before this point.
- Drop it for ordering: `ts = #[(1, 2), (0, 3)]` comes back as
  `#[(0, 3), (1, 2)]`, a different array denoting the same polynomial.
- Drop `DensePolyNormalized`: `cs = #[1, 0]` has
  `termsOfCoeffs cs = #[(0, 1)]` and comes back as `#[1]`.

The last one is the reason `toDense_ofDense` is a theorem about
`DensePoly` rather than about arrays: it is `DensePoly`'s own
"no trailing zeros" invariant that makes the sparse round trip exact,
so this library depends on that invariant as much as on its own.

The bundled statements follow from the array statements by structure eta
and proof irrelevance, and `ofDense_toDense` is also a one-line
consequence of `ext_coeff` with `coeff_toDense` and `coeff_ofDense`.
Both routes should exist. The coefficient route is the one that
generalises to every other operation.

### `toDense` is linear in the degree, and callers must know it

`toDense` on a polynomial of degree `n` allocates `n + 1` coefficients
whatever the term count. On `x^1000000 − 1` that is a million-element
array built to hold two nonzero entries. Nothing here is wrong, but it
is the one operation in this library whose cost is not governed by the
term count, and it is the operation every convenience route reaches
for.

Consequences, each stated so an implementation cannot drift into them
silently:

- No operation specified above is implemented by conversion. `add`,
  `mul`, `eval`, `derivative`, `substPow`, `substScale`, and `compose`
  are sparse algorithms, and the dense agreement theorems are the
  specification rather than the implementation.
- `toDense` never appears in a term the kernel reduces. A `decide`
  over a conversion of a high-degree input would build that array inside
  the kernel.
- The bench families below record the conversion cost separately from
  the algorithm cost wherever a route converts.

There is no guarded `toDense?` in the first version. Whether one is
needed is an open question below, and the answer depends on whether any
consumer converts a polynomial it did not construct.

## Gcd and division convert through the dense representation

```lean
def Monic [One R] (s : SparsePoly R) : Prop := s.leadingCoeff = 1

def divModMonic [One R] [Add R] [Sub R] [Mul R]
    (s t : SparsePoly R) (_ht : t.Monic) : SparsePoly R × SparsePoly R
def divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (s t : SparsePoly R) : SparsePoly R × SparsePoly R
def gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (s t : SparsePoly R) : SparsePoly R
def divExactMonic? [One R] [Add R] [Sub R] [Mul R]
    (s t : SparsePoly R) (ht : t.Monic) : Option (SparsePoly R)

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Div (SparsePoly R)
instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Mod (SparsePoly R)
```

`Div` and `Mod` are registered from `divMod` under the same hypotheses
`DensePoly` uses (`HexPoly/Euclid/DivGcd.lean:1186` and `:1190`), so `/`
and `%` mean the same thing on both representations.

Each is defined by `ofDense` of the corresponding `DensePoly` operation
applied to `toDense` of the inputs, and inherits that operation's
hypotheses unchanged. `divModMonic` takes the monicity proof as an
argument, matching `DensePoly.divModMonic`
(`HexPoly/Euclid/DivGcd.lean:1001`), and `monic_toDense` above is what
carries the hypothesis across. `divMod` and `gcd` want a coefficient
type with division, exactly as
[hex-poly](../../HexPoly/SPEC/hex-poly.md) states them.
`divExactMonic?` is `divModMonic` with a zero-remainder test.

The contracts are transports of the dense ones, so they carry the dense
law packages rather than assuming them, and they carry no hypothesis the
dense library does not already need.
`HexPoly/Euclid/DivGcd.lean` keeps two packages: `DivModLaws` at line
1389 for the division identity and the remainder bound, and `GcdLaws` at
line 1418 for the three divisibility statements. Each theorem below names
the one it needs:

```lean
theorem divMod_spec [Lean.Grind.CommRing R] [Div R] [DensePoly.DivModLaws R]
    (s t : SparsePoly R) :
    (divMod s t).1 * t + (divMod s t).2 = s
theorem divMod_degree_lt [Lean.Grind.CommRing R] [Div R] [DensePoly.DivModLaws R]
    (s t : SparsePoly R) :
    0 < t.degree?.getD 0 → (divMod s t).2.degree?.getD 0 < t.degree?.getD 0

theorem divModMonic_spec [Lean.Grind.CommRing R] [Div R] [DensePoly.DivModLaws R]
    (s t) (ht : t.Monic) :
    (divModMonic s t ht).1 * t + (divModMonic s t ht).2 = s

theorem gcd_dvd_left [Div R] [DensePoly.GcdLaws R] (s t) : gcd s t ∣ s
theorem gcd_dvd_right [Div R] [DensePoly.GcdLaws R] (s t) : gcd s t ∣ t
theorem dvd_gcd [Div R] [DensePoly.GcdLaws R] (d s t) :
    d ∣ s → d ∣ t → d ∣ gcd s t

theorem divExactMonic?_eq_some [Lean.Grind.CommRing R] [Div R]
    [DensePoly.DivModLaws R] (s t) (ht : t.Monic) :
    divExactMonic? s t ht = some q ↔ s = q * t
theorem divExactMonic?_isSome [Lean.Grind.CommRing R] [Div R]
    [DensePoly.DivModLaws R] (s t) (ht : t.Monic) :
    (divExactMonic? s t ht).isSome = true ↔ t ∣ s
```

**`divModMonic_spec` carries `[Div R]` and `[DivModLaws R]` even though
`divModMonic` itself does not**, and that is not an oversight to be
tidied away later. The dense library proves the monic identity by
`divModMonic_eq_divMod_of_monic` (`HexPoly/Euclid/DivGcd.lean:1654`),
which routes through `divMod` and needs both, so there is no
unconditional dense statement to transport. Stating the sparse one
without them would promise something the dense layer does not supply.
If an unconditional dense `divModMonic_spec` is ever proved, the sparse
statement follows and the hypotheses come off here at no cost.

The remainder-degree statements use `degree?.getD 0` because that is the
shape `DensePoly.DivModLaws` states them in, and `degree?_toDense` is
what moves them across. `divExactMonic?_eq_some` needs no `t ≠ 0` side
condition, unlike the `divExact?` of
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md): a monic divisor is nonzero.

**No claim is made that any of this stays sparse.** Sparsity survives
in special cases and not in general, and the special cases are what make
a sparse gcd look more promising than it is. The famous one is
`gcd(x^n − 1, x^m − 1) = x^{gcd(n, m)} − 1`, whose whole remainder
sequence is two-term, because `x^n − 1` reduced modulo `x^m − 1` is
`x^{n mod m} − 1`. A generic pair does not behave that way. Over `ℚ`,

```
x^25 − 1  mod  (x^5 + x + 1)  =  −5x^4 − 10x^3 − 10x^2 − 4x − 1
```

turns two two-term and three-term inputs into a remainder with every
coefficient nonzero, and the same reduction at degree `1000` modulo
`x^7 + x + 1` fills all seven coefficients with 44-digit integers. The
sequence continues from there.

So the cost of `gcd` on inputs of degree `n` is the dense cost at degree
`n` plus a constant number of `O(n)` conversions (two `toDense` and one
`ofDense` for `gcd`, two of each for `divMod`), whatever the term count,
and the conversions are linear in `n` in space as well as time. A caller
with a two-term input of degree `10^6` should expect a gcd to cost what a
dense gcd at degree `10^6` costs.

This is a deliberate placement rather than a gap to be filled later.
[future-work](../../SPEC/future-work.md) records that a sparse division
algorithm should be measured before it is committed to, and the
"convert-gcd" bench family below is that measurement: it records the
conversion share of the total, which is the number that says whether a
sparse remainder sequence could pay for itself. Until that measurement
exists, this SPEC authorises the conversion route and nothing more.

Exact division by an arbitrary, possibly nonmonic integer polynomial is
not specified here. That is hex-poly-z's `divExact?`, which
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md) schedules, and a consumer that wants
it already depends on hex-poly-z and can apply it to `toDense`. Adding a
second one here would be inventing an operation this library has no
consumer for.

The one case that does stay sparse is division by a monomial, and it is
not a shift, because `Nat` exponents do not go negative:

```lean
def divMonomial? [Mul R] (s : SparsePoly R) (e : Nat) : Option (SparsePoly R)
```

`divMonomial? s e` returns `none` unless every stored exponent is at
least `e`, and otherwise subtracts `e` from each. Subtraction is total on
the terms that pass the check, the order is preserved, and no coefficient
changes, so the result is canonical with no filtering. Dividing by
`c · x^e` for a nonunit `c` would additionally have to divide or check
each coefficient. That is a coefficient-ring question rather than a
representation one, and it already has a name in a library this one
depends on: `HexBasic.ExactDivLaws` with its total `exactDiv`. Offering
it here would mean carrying that contract through the whole API for one
operation, so it is not offered.

## Complexity

`s` and `t` terms in the two inputs, `n` the larger degree (the largest
exponent, not the term count), and costs in coefficient operations.

| operation | this library | `DensePoly` |
|---|---|---|
| `coeff` (`@[csimp]` twin) | `O(log s)` | `O(1)` |
| `degree?`, `leadingCoeff`, `numTerms` | `O(1)` | `O(1)` |
| `toTerms`, `foldTerms` | `O(s)` | `O(n)` |
| `addTerm` (`@[csimp]` twin) | `O(log s)` search, `O(s)` shift | `O(n)` |
| `divMonomial? e` | `O(s)` | `O(n)` |
| `ofTerms` (specification) | `O(m²)` on `m` input terms: `m` inserts, each `O(log m)` search and `O(m)` shift | |
| `ofTerms` (`@[csimp]` twin) | `O(m log m)` | |
| `add`, `sub` | `O(s + t)` | `O(n)` |
| `scale`, `mulMonomial`, `neg` | `O(s)` | `O(n)` |
| `mul` (sort and combine) | `O(s·t·log(s·t))` | `O(n²)` |
| `mul` (heap) | `O(s·t·log(min(s, t) + 1))` | `O(n²)` |
| `eval` | `O(s·log(n/s + 1))` mults | `O(n)` |
| `derivative` | `O(s)` | `O(n)` |
| `substPow k`, `k ≥ 1` | `O(s)` | `O(k·n)` |
| `substScale` | `O(s·log(n/s + 1))` | `O(n)` |
| `compose s t` | `O(s)` powerings; the sum of the `mul` costs over the powering and accumulation schedule, on the intermediate sizes | the same sum on dense sizes |
| `toDense` | `O(n)` time and space | |
| `ofDense` | `O(n)` time, `O(s)` space | |
| `gcd` | dense cost at `n`, plus three `O(n)` conversions | dense cost at `n` |
| `divMod`, `divModMonic` | dense cost at `n`, plus four `O(n)` conversions | dense cost at `n` |

There is no single crossover. Addition crosses near `s ≈ n`, since
`O(s + t)` against `O(n)` is a comparison of the same shape.
Multiplication does not: sort-and-combine compares `s·t·log(s·t)` with
`n²`, which crosses at a different and coefficient-dependent point. The
crossover is therefore measured per operation, and the "crossover" bench
family below reports one number per operation rather than one for the
library.

*Measured (Phase 4, on the reference host in
[reports/hex-sparse-poly-performance.md](../../reports/hex-sparse-poly-performance.md)):*
addition crosses at `t ≈ n/8` (degree 4096, `Int`); multiplication at
`t ≈ n/4` on the sort route (degree 1024, `Int`), shifting toward
`n/3` with the selected tree twin; gap-Horner evaluation is still 20×
ahead of dense Horner at `t = n/128` (degree 65536, `ZMod64 7`) with
parity extrapolating to `t ≈ n/6`. In the convert-gcd family the
conversions are only ≈ 5% of the sparse-remainder pair's total, so a
future sparse division algorithm could recover essentially the whole
dense cost there. Everything in the left column that is `O(s)` against an `O(n)`
right column is the reason the library exists. `coeff` and
multiplication's logarithmic factor are the price.

## Kernel exposure

This library has no tactic consumer today, so the kernel requirement is
the always-on cross-check discipline of design principle 11 rather than
certificate replay. What must reduce under `decide`: `SparsePolyCanonical`,
`addTerm`, `ofTerms`, `coeff`, `ofDense`, `add`, `mul` as specified, and
the `DecidableEq` instance. Each is `@[expose]` and a downstream module
carries a `decide`-based test that fails if any of them stops reducing.

Those are exactly the names whose public bodies are the `noncomputable`
`List`-shaped specifications given above. The `Array` versions
(`addTermImpl`, `coeffImpl`, `ofDenseImpl`, the sort-and-combine
`ofTerms` twin, and whichever multiplication implementation is selected)
stay out of the reduction closure by construction: `@[csimp]` redirects
each occurrence that reaches code generation, and proof-mode and kernel
`decide` continue to see the specification. That split is what keeps a
binary search out of a kernel loop.

`toDense` is also out of the closure, for the size reason above rather
than for a reduction reason.

The `DecidableEq` routing through `List` equality is part of this and
not an optimisation. See the representation section.

## Conformance

Fixtures follow [SPEC/testing.md](../../SPEC/testing.md). Two Lean drivers, as
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) has:
`conformance/HexSparsePoly/Conformance.lean`, holding the `#guard`
property checks, registered in `HexConformance`; and
`conformance/HexSparsePoly/EmitFixtures.lean`, exposed as
`lean_exe hexsparsepoly_emit_fixtures`. A committed snapshot at
`conformance-fixtures/HexSparsePoly/sparsepoly.jsonl`, and an oracle
driver at `scripts/oracle/sparsepoly_sympy.py`. One tuple appended to
`ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexSparsePoly|hexsparsepoly_emit_fixtures|scripts/oracle/sparsepoly_sympy.py|conformance-fixtures/HexSparsePoly/sparsepoly.jsonl"
```

SymPy is the oracle, mode `if_available`, using the sparse polynomial
elements of `sympy.polys.rings`, which store a dictionary keyed on the
exponent and handle an exponent of `10^6` without materialising a
coefficient vector. The oracle reconstructs each polynomial from the
serialized terms rather than from Lean's output, as
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md)'s oracle does.
python-flint's `fmpz_poly` is dense, so it is a comparator at low degree
and is not the oracle for the high-exponent cases.

**Invariant cases**, which the oracle cannot see and which are checked
in Lean by comparing term arrays directly:

- `ofTerms` on an empty array, on unsorted input, on input with repeated
  exponents, on input containing zero coefficients, and on input where
  the repeated exponents sum to zero.
- `add` cancelling at the lowest exponent, at an interior exponent, at
  the highest exponent, and everywhere at once (`s + (−s) = 0`).
- `mul` where two nonzero products land on the same exponent and
  cancel: `(x + 1) * (x − 1) = x² − 1` over `Int`, checked on the term
  array so that a stored `(1, 0)` fails the test. This is the collision
  hazard the invariant section names, and it needs no exotic coefficient
  ring.
- `mul` over `ZMod64 n` for composite `n`, where a single coefficient
  product is zero with both factors nonzero. `ZMod64` needs only
  `ZMod64.Bounds n`, not primality, so this ring is available without a
  Mathlib import.
- `compose` where contributions from different terms collide at one
  exponent and cancel.
- `scale` by zero and by a zero divisor, checking that interior terms
  are deleted and their neighbours are not.
- `derivative` over `ZMod64 p` of `x^p` (zero), of `x^p + x^(2p)` (zero),
  and of `x^p + x` (one term), checking the zero filter.
- `substPow 0` on an input whose coefficients sum to zero and on one
  whose coefficients do not.
- Equality: every canonicalisation case above compared against the
  hand-written canonical array, and `DecidableEq` exercised under
  `module` with `public import` so the array-equality hazard is caught.

**Round-trip cases**: `ofDense_toDense` and `toDense_ofDense` on the
zero polynomial, a constant, a monomial, a dense random polynomial, a
polynomial with interior zero coefficients, and a polynomial whose
constant term is zero. Also the negative cases as `#guard`s on the
array-level workers, one per bullet in the round-trip section, so the
necessity of each hypothesis is checked and not only asserted.

**Oracle cases**: addition, subtraction, multiplication, powering,
evaluation, derivative, `substPow`, `substScale`, and `compose` on

- disjoint supports and heavily overlapping supports;
- binomials and trinomials at degrees `10^3`, `10^4`, and `10^6`,
  including `x^1000000 − 1` squared and its derivative, which no dense
  route in the suite may touch;
- `Φ_p(x^{p^{k-1}})` shapes for small `p` and `k`, which is the
  cyclotomic consumer's access pattern;
- inputs over `Int`, over `Rat`, and over `ZMod64 p`;
- evaluation of a high-exponent polynomial in `ZMod64 p`, where the oracle
  can compute the answer and a dense evaluation could not run.

**The conformance project needs one dependency the library does not.**
`ZMod64` is hex-mod-arith, and this library depends only on hex-poly and
hex-basic. The monorepo hides that, since everything builds together,
but the released split repository would not: its conformance project has
to pin hex-mod-arith (and hex-arith below it) even though its library
does not. The manifest entry records that pin, and the alternative,
defining a small zero-divisor ring inside the conformance driver, is
rejected because a hand-rolled ring in a test is a second thing to get
right.

**Cross-library case**: `gcd` and `divMod` on inputs of moderate degree
compared against the same computation done entirely in `DensePoly`,
which is a differential test of the conversions rather than of the
Euclidean algorithm.

## Benchmarking

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), with drivers at
`bench/HexSparsePoly/Bench.lean`. Native only, plus a small kernel
family for the `decide` closure listed under kernel exposure.

Families:

- **sparse-arithmetic**: `add` and `mul` of `t`-term inputs for
  `t` in 2 to 64 at degrees `10^3` to `10^6`. The required property is
  that the time depends on `t` and not on the degree.
- **sparse-multiplication**: the three multiplication shapes on
  low-collision inputs (disjoint exponent sums) and high-collision
  inputs (arithmetic-progression exponents, where the `s·t` pairwise
  sums land on only `s + t − 1` distinct exponents).
  These results determine the `@[csimp]` implementation, so the family
  is measured before the implementation is chosen rather than after.
- **crossover**: the same operations against `DensePoly` at matched
  degree with the term count swept from `2` to `n`, locating the density
  ratio at which dense wins **for each operation separately**, since the
  complexity table above shows they do not share one. These numbers are
  the library's main output to the rest of the project, and they belong
  in the SPEC once measured.
- **evaluation**: gap Horner against dense Horner across the same sweep.
- **substitution-power**: `substPow` on `Φ_p` shapes against the dense
  route, which is the cyclotomic adapter's cost.
- **convert-gcd**: `gcd` and `divMod` through the conversions, recording
  the conversion time and the dense time separately. Two contrasting
  shapes, because they bound the question from both sides: the
  `x^n − 1`, `x^m − 1` pair, whose remainder sequence stays two-term and
  where a sparse algorithm would win by an enormous margin, and generic
  sparse pairs, where it would not. The measurement that decides whether
  a sparse division algorithm is worth specifying.

**Comparators.** SymPy's sparse ring elements, `informational`: SymPy is
the oracle and is Python, so the ratio is reported for context and does
not determine acceptance.
FLINT's `fmpz_poly` via python-flint, `informational` and restricted to
the crossover family: it is a dense representation, so above the
crossover the comparison measures the choice of representation rather
than the quality of either implementation, and a threshold there would
be meaningless. No external comparator is registered with
`class: gating`, so none of them has a required threshold, and that is
the justification.

Two required internal checks, which matter more than the external ones:

- `mul` and `add` on the sparse families must be faster than the same
  operation on `toDense` of the same inputs by a factor that grows with
  `n/t`, and the crossover family must locate the ratio where that stops
  being true.
- `substPow s k` must be independent of `k` up to the cost of
  multiplying the exponents, since it does not touch the coefficients.
  A regression here means an implementation started materialising the
  intermediate degrees.

## The Mathlib layer

`hex-sparse-poly-mathlib` identifies the type with `Polynomial R`:

```lean
def denseEquiv [CommRing R] [DecidableEq R] : SparsePoly R ≃+* DensePoly R
def equiv [CommRing R] [DecidableEq R] : SparsePoly R ≃+* Polynomial R :=
  denseEquiv.trans HexPolyMathlib.equiv

theorem coeff_equiv (s : SparsePoly R) (e : Nat) : (equiv s).coeff e = s.coeff e
theorem equiv_toDense (s : SparsePoly R) : HexPolyMathlib.equiv s.toDense = equiv s
theorem equiv_support (s : SparsePoly R) : (equiv s).support = s.support.toList.toFinset
theorem equiv_eval (s : SparsePoly R) (x : R) : (equiv s).eval x = s.eval x
theorem equiv_derivative (s : SparsePoly R) :
    Polynomial.derivative (equiv s) = equiv s.derivative
theorem equiv_compose (s t : SparsePoly R) : (equiv s).comp (equiv t) = equiv (s.compose t)
theorem equiv_substPow (s : SparsePoly R) (k : Nat) :
    (equiv s).comp (Polynomial.X ^ k) = equiv (s.substPow k)
theorem equiv_substScale (s : SparsePoly R) (a : R) :
    (equiv s).comp (Polynomial.C a * Polynomial.X) = equiv (s.substScale a)
```

`equiv` is **defined** by composition, and the step that makes the
composition available is `denseEquiv`. `toDense` is a function, not an
equivalence, so it cannot be handed to `RingEquiv.trans` directly:
`denseEquiv` packages `toDense` with `ofDense` as its inverse, the two
round trips as `left_inv` and `right_inv`, and `toDense_add` and
`toDense_mul` as the `map_add'`/`map_mul'` fields, which is all
`RingEquiv` carries; the zero and one images then follow from the
equivalence structure, with `toDense_zero` and `toDense_one` remaining
the core's direct statements of the same facts. That is the reason the
Mathlib-free layer proves the additive and multiplicative transports in
the first place, and `denseEquiv` is where they are used.

`denseEquiv` needs no Mathlib beyond `RingEquiv` itself. Both it and
`equiv` are stated at Mathlib's `[CommRing R]`, because
`denseEquiv.map_mul'` reuses `toDense_mul`, which sits at
`Lean.Grind.CommRing` per the law-placement note above; if the dense
multiplication laws are ever weakened to semirings, both statements
drop to `[Semiring R]` at no cost, matching
[hex-poly-mathlib](../../HexPolyMathlib/SPEC/hex-poly-mathlib.md)'s
`equiv` (`HexPolyMathlib/PolynomialEquivalence.lean:510`). The
individual correspondence lemmas mention `equiv` and therefore share
its class; only helpers that never mention it (the dense
`eval_toPolynomial`, in hex-poly-mathlib) sit at `[Semiring R]`.

`equiv_support` is the one statement that is genuinely about this
representation rather than transported through the dense one: it says
the stored exponents are exactly Mathlib's `support`, which is the sense
in which the representation is the sparse one. It needs both halves of
`SparsePolyCanonical`. Strict increase gives one stored coefficient per
exponent, so the stored value at an exponent is the semantic
coefficient rather than a partial sum, and the zero-free condition then
makes every stored exponent one where that coefficient is nonzero, which
is what `Polynomial.support` collects. Drop either half and the stored
exponents can include one whose semantic coefficient is zero.

Following the project split, no theorem about `SparsePoly` belongs in
the companion beyond these and one correspondence lemma per public
operation.

## Prerequisite changes in other libraries

None. `DensePoly`, `DensePolyNormalized`, `DensePoly.coeff`,
`DensePoly.monomial`, `DensePoly.compose`, `DensePoly.derivative`,
`DensePoly.Monic`, and the `divMod`/`gcd` family with their `DivModLaws`
and `GcdLaws` packages all exist with the hypotheses this SPEC uses.
`HexBasic/ArrayDecEq.lean` supplies the array equality instance, and
`HexBasic/Fold.lean` supplies the `List.foldl` addition algebra that the
sort-and-combine proof needs if the sort is ever made unstable.

One candidate for promotion, not a prerequisite: if the stable
sort-by-key with a combining fold that the `@[csimp]` twin uses proves
reusable, it belongs in hex-basic rather than here, in the same way that
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) puts its reusable map
algorithms in `HexBasic/ExtTreeMap.lean`. The sparse matrix work
described in [future-work](../../SPEC/future-work.md) canonicalises coordinate
form the same way and would be the second consumer. Write it here
first and promote it when that happens.

## Milestones

1. **The representation.** `SparsePolyCanonical`, `SparsePoly`,
   `addTerm` with its invariant proof, `ofTerms`, `coeff`, `ext_coeff`,
   `DecidableEq` over hex-basic's scoped array instance, the accessors,
   and `toTerms` / `foldTerms`. Each of `addTerm`, `coeff`, and
   `ofTerms` lands as the `List`-shaped specification together with its
   `@[csimp]` twin, since retrofitting that split after the proofs are
   written is the expensive order. The invariant proofs in this milestone
   are what the whole library rests on, and the cancellation and
   duplicate cases have their conformance checks written first.

2. **Arithmetic.** `add`, `neg`, `sub`, `scale`, `mulMonomial`, `mul` as
   specified, `pow`, the operator instances, and the ring laws. The
   `@[csimp]` multiplication twin is written after the bench family that
   determines it.

3. **The conversions.** `coeffsOfTerms`, `termsOfCoeffs`, `toDense`,
   `ofDense`, the homomorphism laws, `degree?_toDense` with
   `leadingCoeff_toDense` and `monic_toDense`, and both round trips at
   the array level and the bundled level. At the end of this milestone
   `coeff_mul` is available by transport.

4. **Evaluation, derivative, substitution.** Gap Horner, the derivative
   with its zero filter, `substPow`, `substScale`, and `compose`, with
   the dense agreement theorems.

5. **Gcd and division through the conversions**, with the transported law
   packages and `divMonomial?`, and the bench families, including the
   per-operation crossover measurements and the conversion share in
   "convert-gcd". Those numbers are written back into this SPEC when they
   exist.

6. **The companion**, `denseEquiv` first and `equiv` by composition.

## File organisation

```
HexSparsePoly/
  Basic.lean      -- SparsePolyCanonical, SparsePoly, addTerm, ofTerms,
                  --   coeff (each with its @[csimp] twin), ext_coeff,
                  --   DecidableEq, accessors, toTerms, foldTerms
  Arith.lean      -- add, neg, sub, scale, mulMonomial, mul, pow,
                  --   the operator instances, ring laws
  Dense.lean      -- coeffsOfTerms, termsOfCoeffs, toDense, ofDense,
                  --   homomorphism laws, degree/leadingCoeff/Monic
                  --   transport, round trips
  Eval.lean       -- eval, derivative, substPow, substScale, compose
  Euclid.lean     -- divModMonic, divMod, gcd, divExactMonic?,
                  --   divMonomial?, the transported law packages
HexSparsePoly.lean
HexSparsePolyMathlib/
  Equiv.lean      -- denseEquiv, equiv, and the correspondence lemmas
HexSparsePolyMathlib.lean
```

`Dense.lean` comes before `Eval.lean` because the evaluation and
derivative theorems are stated against the dense operations.

`libraries.yml` gains:

```yaml
  HexSparsePoly:
    deps: [HexPoly, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: SymPy sparse ring elements (sympy.polys.rings)
          class: informational
          rationale: "SymPy is the conformance oracle and is Python, so the ratio is reported for context and does not determine acceptance."
        - tool: FLINT fmpz_poly via python-flint
          class: informational
          rationale: "fmpz_poly is dense, so above the crossover the comparison measures the choice of representation rather than the quality of either implementation. Recorded on the crossover family only."
      input_families:
        - name: sparse-arithmetic
          description: addition and multiplication of 2 to 64 term inputs at degrees 10^3 to 10^6
        - name: sparse-multiplication
          description: low-collision and high-collision products across the three candidate implementations
        - name: crossover
          description: the same operations against DensePoly with the term count swept from 2 to the degree, locating one crossover per operation
        - name: evaluation
          description: gap Horner against dense Horner across the same sweep
        - name: substitution-power
          description: substPow on the cyclotomic shapes against the dense route
        - name: convert-gcd
          description: gcd and divMod through the conversions on the sparse-remainder x^n-1 pair and on generic sparse pairs, recording the conversion share separately
  HexSparsePolyMathlib:
    deps: [HexSparsePoly, HexPolyMathlib, HexPoly]
    mathlib: true
    done_through: 0
    status: planned
```

## Open questions

- **Whether `toDense` needs a guarded variant.** A `toDense?` returning
  `none` above a degree cap would stop a caller from allocating a
  million coefficients by accident, at the cost of an `Option` at every
  use site and a cap that has to be chosen. The answer depends on
  whether any consumer ever converts a polynomial it did not construct.
  The cyclotomic adapter does not.
- **Which multiplication implementation wins.** The heap has the better
  bound and the worse constant, the sort has the simplest proof, and the
  `Std.ExtTreeMap` accumulation reuses machinery
  [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) already exercises.
  The "sparse-multiplication" family decides, and the specification does
  not change either way.
- **Whether the terms should be two parallel arrays.**
  `exps : Array Nat` and `coeffs : Array R` avoid boxing the pair and
  give better locality on the exponent scan, which is the inner loop of
  the merge and of `coeff`. `Array (Nat × R)` keeps the invariant and
  the proofs in one place and cannot desynchronise the lengths. This is
  the same choice coordinate form faces in the sparse matrix item of
  [future-work](../../SPEC/future-work.md), and design principle 10 is what
  keeps it changeable: no consumer reads `terms`.
- **Whether descending exponent order would suit the consumers better.**
  Leading-term algorithms want the top term first, and evaluation reads
  from the top. Ascending is chosen to match `DensePoly`'s index order
  and the `#p[…]` literal, and the cost of the choice is that `eval` and
  the leading-term operations read the array from the back.
- **Whether the derivative should cast the exponent or add repeatedly.**
  `(e : R) * c` needs `[NatCast R]`, which
  `DensePoly.derivative` already requires, and repeated addition needs
  only `[Add R]` but costs `O(e)` per term, which is exactly the
  exponent-linear cost this library exists to avoid. The cast is the
  right default. A coefficient type without `NatCast` has no derivative
  here.
- **Whether a sparse division algorithm is worth specifying.** The
  "convert-gcd" family answers it. Until then, gcd and division convert,
  and this SPEC promises nothing about the sparsity of a remainder
  sequence.
