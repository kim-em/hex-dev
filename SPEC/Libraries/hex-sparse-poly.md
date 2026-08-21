# hex-sparse-poly (canonical sparse univariate polynomials, depends on hex-poly + hex-basic)

Univariate polynomials stored as a sorted array of exponent/coefficient
terms, for inputs whose exponents are large and whose number of nonzero
coefficients is small. Mathlib-free. The companion
`hex-sparse-poly-mathlib` supplies the ring equivalence with
`Polynomial R` and the correspondence lemmas.

This SPEC expands the "Sparse univariate polynomials" bullet of
[future-work](../future-work.md). It sits beside
[hex-poly](../../HexPoly/SPEC/hex-poly.md) rather than inside it, and it
converts to and from `DensePoly R` explicitly at a named boundary. It
does **not** introduce a common interface over the two representations.
The reasoning is under "No swappable polynomial abstraction" below, and
the same decision is recorded in
[future-work](../future-work.md) under "Swappable polynomial
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
over the terms and the result has the same number of terms as the input.
In the dense representation the cost and the size are both `k` times the
input degree.

**The identified consumer is the cyclotomic construction.**
`Φ_{p^k}(x) = Φ_p(x^{p^{k-1}})`, so the sparse family among the
cyclotomics is exactly the one this representation stores well: `Φ_p`
itself has `p − 1` nonzero coefficients and is dense, and the `p^k`
members are that dense polynomial with its exponents scaled. The
cyclotomic library specified in [future-work](../future-work.md) builds
`ZPoly` and offers sparse output as an optional adapter over this
library. That adapter is downstream: nothing here knows what a
cyclotomic polynomial is.

**Dense stays the default.** Berlekamp-Zassenhaus, hex-poly-z,
hex-resultant, and hex-number-field all hold `DensePoly` and see full
coefficient vectors at moderate degree, where the sparse representation
is a constant factor worse on every operation and asymptotically worse
on none. This library is for the other shape of input and does not ask
any existing consumer to change.

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

The resolution is the one [future-work](../future-work.md) already
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
- the derivative in positive characteristic: over `ZMod p` the
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
(`coeff`, `support`, `numTerms`, `degree?`, `leadingCoeff`) and not
directly by consumers, so the parallel-array variant in the open
questions stays available.

**Equality does not come for free.** `deriving DecidableEq` fails on a
structure with a proof field, so the instance compares `terms` and
recovers structure equality by proof irrelevance. It must compare the
term arrays through `List` equality rather than through
`Array.instDecidableEq`, whose nonempty case delegates to a
non-`@[expose]` implementation that is unavailable downstream. That is
the same hazard `HexPoly/Dense.lean` documents and
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) repeats, recorded in
[progress/lean4-array-decidableeq-module-repro.md](../../progress/lean4-array-decidableeq-module-repro.md).
This library stores `Array (Nat × R)`, so it is exposed to it twice
over: through the array and through the pair.

## Canonical construction

One function establishes the invariant, and every other constructor is
defined from it.

```lean
namespace Hex.SparsePoly

/-- Add `c · x^e` to `s`, combining with an existing term at `e` and
deleting the term when the sum is zero. -/
def addTerm [Add R] (s : SparsePoly R) (e : Nat) (c : R) : SparsePoly R

/-- The canonical polynomial with the given terms. Exponents may repeat
and may appear in any order, and coefficients at equal exponents are summed
and zero results are dropped. -/
def ofTerms [Add R] (ts : Array (Nat × R)) : SparsePoly R :=
  ts.foldl (fun s t => s.addTerm t.1 t.2) 0

def monomial (e : Nat) (c : R) : SparsePoly R
def C (c : R) : SparsePoly R
def X [One R] : SparsePoly R

instance : Zero (SparsePoly R)      -- the empty term array
instance [One R] : One (SparsePoly R)

def coeff (s : SparsePoly R) (e : Nat) : R
def support (s : SparsePoly R) : Array Nat
def numTerms (s : SparsePoly R) : Nat
def degree? (s : SparsePoly R) : Option Nat
def leadingCoeff (s : SparsePoly R) : R
def isZero (s : SparsePoly R) : Bool
```

`addTerm` locates `e` by binary search, then does one of three things:
insert a new term when `c ≠ 0` and `e` is absent, replace the existing
coefficient by the sum when the sum is nonzero, and delete the term when
the sum is zero. All three preserve the invariant, and the proof that
they do is the one nontrivial proof in the milestone. Both hazards
listed above are handled here and nowhere else.

`ofTerms` is a fold of `addTerm`, so canonicality is immediate by
induction and the characterisation needs no reordering:

```lean
/-- The coefficient of `ofTerms ts` at `e` is the sum, in input order, of
the coefficients of the terms of `ts` at `e`. -/
theorem coeff_ofTerms [Add R] (ts : Array (Nat × R)) (e : Nat) :
    (ofTerms ts).coeff e =
      (ts.filter (fun t => t.1 = e)).foldl (fun a t => a + t.2) 0
```

The only law this needs is that `0` is a left identity for `+`, because
`addTerm` inserts `c` where the fold on the right computes `0 + c`. It
needs neither associativity nor commutativity, since both sides
accumulate in input order.

It is the sort-and-combine implementation that needs more: sorting
reorders the terms at a given exponent, so proving the fast
implementation equal to `ofTerms` needs addition to be associative and
commutative. `Lean.Grind.Semiring` supplies both (`add_assoc` and
`add_comm`), and `HexBasic/Fold.lean` already carries the
`Std.Associative` and `Std.LawfulIdentity` instances that the
`List.foldl` reordering lemmas want, which is why hex-basic is a
dependency and not an incidental import.

Following design principle 11, `ofTerms` as written above is the
kernel-facing specification: it is a fold of a small insert, it has no
sort, and it reduces. The `@[csimp]` twin sorts the input by exponent
(stable), combines each equal-exponent block in one pass, and drops the
zeros, which is `O(m log m)` on `m` input terms against the
specification's `O(m²)` worst case. `mul` is defined through `ofTerms`,
so this is the only place the sort appears.

`ofTerms` is what a consumer holding a list of terms calls, and it is
the one construction that accepts arbitrary input. The literal
`#sp[(e₀, c₀), (e₁, c₁), …]` abbreviates `ofTerms #[…]`, mirroring
`#p[…]` for `DensePoly`, and inherits the same "any order, duplicates
summed, zeros dropped" behaviour.

`coeff` binary searches the term array, so it is `O(log t)` rather than
`DensePoly`'s `O(1)`. `degree? 0 = none`, matching
`DensePoly.degree?`. `leadingCoeff` of the zero polynomial is `0`.

The extensionality theorem is what canonicality buys, and everything
below is proved from it:

```lean
@[ext] theorem ext_coeff {s t : SparsePoly R} (h : ∀ e, s.coeff e = t.coeff e) :
    s = t
```

## Arithmetic

```lean
def add [Add R] (s t : SparsePoly R) : SparsePoly R
def neg [Neg R] (s : SparsePoly R) : SparsePoly R
def sub [Sub R] (s t : SparsePoly R) : SparsePoly R
def mul [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R
def pow [One R] [Add R] [Mul R] (s : SparsePoly R) (n : Nat) : SparsePoly R
def scale [Mul R] (c : R) (s : SparsePoly R) : SparsePoly R
def mulMonomial [Mul R] (e : Nat) (c : R) (s : SparsePoly R) : SparsePoly R
```

Typeclass hypotheses go on the individual operations, as in
[hex-poly](../../HexPoly/SPEC/hex-poly.md), rather than on the type.
The laws are stated against `Lean.Grind.Semiring` and
`Lean.Grind.CommRing`, which is what the existing libraries use where a
full ring is needed. No Mathlib class appears here. The `≃+*` lives in
the companion.

`add` is a linear merge of two sorted arrays. At a matching exponent it
sums and, when the sum is zero, emits nothing. This is the cancellation
case, and it is `O(s + t)` with no search and no sort.

`neg` maps the coefficients. Over a ring, `−c = 0` exactly when `c = 0`,
so the exponents and the term count are unchanged. `[Neg R]` alone does
not supply that fact, so the implementation applies the same zero filter
as `scale`, and the laws below carry the ring hypothesis under which the
filter removes nothing.

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
   `O(s·t·log min(s, t))`, and it is Johnson's algorithm as used by
   Monagan and Pearce for sparse multiplication.
3. **Accumulate in a map.** Fold the products into an
   `Std.ExtTreeMap Nat R`, then read the ordered term list.
   `O(s·t·log(s·t))` with a different constant and no separate sort.

The heap is the one with the better bound and the worse constant. The
bench family "sparse-multiplication" below is what picks the
implementation, and the specification does not change whichever wins.

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

with `mul_comm` under `Lean.Grind.CommRing`. `coeff_mul` is the
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
end. Each gap power is one binary powering, so the cost is `t`
additions and `Σᵢ O(log gapᵢ)` multiplications, which is
`O(t · log(n/t + 1))` by concavity, against `DensePoly`'s `O(n)`. For
`x^1000000 − 1` that is about forty multiplications rather than a
million.

```lean
theorem eval_eq_toDense [Lean.Grind.CommRing R] (s : SparsePoly R) (x : R) :
    s.eval x = s.toDense.eval x
```

The commutative hypothesis is the same one
[hex-poly](../../HexPoly/SPEC/hex-poly.md) states for
`eval_mul_commring`: the gap form reassociates and commutes the
coefficient and the powers of `x`, which a noncommutative coefficient
ring does not license.

**The derivative must canonicalise.** `c · x^e` maps to
`(e : R) * c · x^(e-1)`, and the `e = 0` term is dropped. The exponent
map `e ↦ e − 1` is strictly monotone on the terms that survive, so the
order is preserved and nothing needs re-sorting or combining. What is
needed is the zero filter, because `(e : R) * c` can vanish: over
`ZMod p` every exponent divisible by `p` produces a zero coefficient,
and the derivative of `x^p + x^{2p}` is the zero polynomial. An
implementation that maps the array without filtering produces a
structurally nonzero representation of `0`, which then compares unequal
to `0`. This is the invariant hazard most likely to be missed, so it
gets a route-level conformance case rather than only an oracle case.

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
powers of `t` obtained by binary powering from the gaps. If `t` has `u`
terms then `t^e` has up to `u^e` of them before cancellation, so the
output size is governed by the output, not by the input. The
specification is the coefficient identity and the agreement with
`DensePoly.compose`. The complexity entry is stated in terms of the
output.

```lean
theorem coeff_derivative, derivative_toDense, derivative_add, derivative_mul
theorem substPow_eq_compose (s) (k) : s.substPow k = s.compose (monomial k 1)
theorem eval_substPow (s) (k) (x) : (s.substPow k).eval x = s.eval (x ^ k)
theorem eval_compose (s t) (x) : (s.compose t).eval x = s.eval (t.eval x)
theorem compose_toDense (s t) : (s.compose t).toDense = s.toDense.compose t.toDense
```

`substPow_eq_compose` is the statement that the fast path and the
general path agree, and it is what lets the cyclotomic adapter use
`substPow` and reason with `compose`.

## Conversion to and from the dense representation

```lean
/-- The array-level workers, stated separately so the round trips can
name their hypotheses. -/
def coeffsOfTerms (ts : Array (Nat × R)) : Array R
def termsOfCoeffs (cs : Array R) : Array (Nat × R)

def toDense (s : SparsePoly R) : DensePoly R
def ofDense (p : DensePoly R) : SparsePoly R
```

`toDense` allocates `degree + 1` coefficients and writes each stored
term into its slot. `ofDense` walks the coefficient array and keeps the
nonzero entries with their indices.

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
theorem eval_toDense, derivative_toDense, compose_toDense
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
theorem termsOfCoeffs_coeffsOfTerms {ts : Array (Nat × R)}
    (h : SparsePolyCanonical ts) : termsOfCoeffs (coeffsOfTerms ts) = ts

theorem coeffsOfTerms_termsOfCoeffs {cs : Array R}
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
def divModMonic [One R] [Add R] [Sub R] [Mul R]
    (s t : SparsePoly R) : SparsePoly R × SparsePoly R
def divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (s t : SparsePoly R) : SparsePoly R × SparsePoly R
def gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (s t : SparsePoly R) : SparsePoly R
def divExactMonic? [One R] [Add R] [Sub R] [Mul R]
    (s t : SparsePoly R) : Option (SparsePoly R)
```

Each is defined by `ofDense` of the corresponding `DensePoly` operation
applied to `toDense` of the inputs, and inherits that operation's
hypotheses unchanged: `divModMonic` wants a monic divisor and `divMod`
and `gcd` want a coefficient type with division, exactly as
[hex-poly](../../HexPoly/SPEC/hex-poly.md) states them.
`divExactMonic?` is `divModMonic` with a zero-remainder test. The correctness
theorems are transports through `toDense_mul` and `toDense_add`:

```lean
theorem divMod_spec [Lean.Grind.CommRing R] [Div R] [DensePoly.DivModLaws R]
    (s t : SparsePoly R) :
    (divMod s t).1 * t + (divMod s t).2 = s
theorem gcd_dvd_left, gcd_dvd_right, dvd_gcd
```

**No claim is made that any of this stays sparse.** The remainder
sequence of two sparse polynomials is generically dense: `x^n − 1` and
`x^m − 1` are two terms each and the intermediate remainders of their
Euclidean sequence are not. So the cost of `gcd` on inputs of degree `n`
is the dense cost at degree `n` plus two conversions, whatever the term
count, and the conversion is the part that is linear in `n` in space as
well as time. A caller with a two-term input of degree `10^6` should
expect a gcd to cost what a dense gcd at degree `10^6` costs.

This is a deliberate placement rather than a gap to be filled later.
[future-work](../future-work.md) records that a sparse division
algorithm should be measured before it is committed to, and the
"convert-gcd" bench family below is that measurement: it records the
conversion share of the total, which is the number that says whether a
sparse remainder sequence could pay for itself. Until that measurement
exists, this SPEC authorises the conversion route and nothing more.

Exact division over `Int` is not specified here. It is hex-poly-z's
`divExact?`, which [hex-poly-z-gcd](hex-poly-z-gcd.md) schedules, and a
consumer that wants it already depends on hex-poly-z and can apply it to
`toDense`. Adding a second one here for a coefficient type with no
division would be inventing an operation this library has no consumer
for.

The one case that does stay sparse is exact division by a monomial,
which is `mulMonomial` with a negative shift. It belongs with the
monomial operations rather than here, and `divExactMonic?` does not
special-case it in the first version.

## Complexity

`s` and `t` terms in the two inputs, `n` the larger degree (the largest
exponent, not the term count), and costs in coefficient operations.

| operation | this library | `DensePoly` |
|---|---|---|
| `coeff` | `O(log s)` | `O(1)` |
| `degree?`, `leadingCoeff`, `numTerms` | `O(1)` | `O(1)` |
| `addTerm` | `O(log s)` search, `O(s)` shift | `O(n)` |
| `ofTerms` (specification) | `O(m²)` on `m` input terms: `m` inserts, each `O(log m)` search and `O(m)` shift | |
| `ofTerms` (`@[csimp]` twin) | `O(m log m)` | |
| `add`, `sub` | `O(s + t)` | `O(n)` |
| `scale`, `mulMonomial`, `neg` | `O(s)` | `O(n)` |
| `mul` (sort and combine) | `O(s·t·log(s·t))` | `O(n²)` |
| `mul` (heap) | `O(s·t·log min(s, t))` | `O(n²)` |
| `eval` | `O(s·log(n/s + 1))` mults | `O(n)` |
| `derivative` | `O(s)` | `O(n)` |
| `substPow k`, `k ≥ 1` | `O(s)` | `O(k·n)` |
| `substScale` | `O(s·log(n/s + 1))` | `O(n)` |
| `compose s t` | `O(s)` powerings, output-governed | output-governed |
| `toDense` | `O(n)` time and space | |
| `ofDense` | `O(n)` time, `O(s)` space | |
| `gcd`, `divMod` | dense cost at `n`, plus two `O(n)` conversions | dense cost at `n` |

The crossover is at `s ≈ n`, and the constant in front of it is what the
bench families measure. Everything in the left column that is `O(s)`
against an `O(n)` right column is the reason the library exists.
Everything that is worse (`coeff`, and multiplication's `log` factor) is
the price.

## Kernel exposure

This library has no tactic consumer today, so the kernel requirement is
the always-on cross-check discipline of design principle 11 rather than
certificate replay. What must reduce under `decide`: `SparsePolyCanonical`,
`addTerm`, `ofTerms`, `coeff`, `add`, `mul` as specified, the
`DecidableEq` instance, and `ofDense`. Each is `@[expose]` and a
downstream module carries a `decide`-based test that fails if any of
them stops reducing.

What stays out of the reduction closure: the sort-and-combine `ofTerms`
twin, whichever multiplication implementation wins, and `toDense`.
`toDense` is excluded for the size reason above rather than for a
reduction reason.

The `DecidableEq` routing through `List` equality is part of this and
not an optimisation. See the representation section.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexSparsePoly/EmitFixtures.lean` exposed as
`lean_exe hexsparsepoly_emit_fixtures`, a committed snapshot at
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
- `mul` over `ZMod n` for composite `n`, where a single coefficient
  product is zero with both factors nonzero.
- `scale` by zero and by a zero divisor, checking that interior terms
  are deleted and their neighbours are not.
- `derivative` over `ZMod p` of `x^p` (zero), of `x^p + x^(2p)` (zero),
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
- `Φ_p(x^(p^(k-1)))` shapes for small `p` and `k`, which is the
  cyclotomic consumer's access pattern;
- inputs over `Int`, over `Rat`, and over `ZMod p`;
- evaluation of a high-exponent polynomial in `ZMod p`, where the oracle
  can compute the answer and a dense evaluation could not run.

**Cross-library case**: `gcd` and `divMod` on inputs of moderate degree
compared against the same computation done entirely in `DensePoly`,
which is a differential test of the conversions rather than of the
Euclidean algorithm.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexSparsePoly/Bench.lean`. Native only, plus a small kernel
family for the `decide` closure listed under kernel exposure.

Families:

- **sparse-arithmetic**: `add` and `mul` of `t`-term inputs for
  `t` in 2 to 64 at degrees `10^3` to `10^6`. The required property is
  that the time depends on `t` and not on the degree.
- **sparse-multiplication**: the three multiplication shapes on
  low-collision inputs (disjoint exponent sums) and high-collision
  inputs (arithmetic-progression exponents, where every sum collides).
  This family picks the `@[csimp]` implementation, so it is measured
  before the implementation is chosen rather than after.
- **crossover**: the same operations against `DensePoly` at matched
  degree with the term count swept from `2` to `n`, locating the density
  ratio at which dense wins. This number is the library's main output to
  the rest of the project, and it belongs in the SPEC once measured.
- **evaluation**: gap Horner against dense Horner across the same sweep.
- **substitution-power**: `substPow` on `Φ_p` shapes against the dense
  route, which is the cyclotomic adapter's cost.
- **convert-gcd**: `gcd` and `divMod` through the conversions, recording
  the conversion time and the dense time separately. The measurement
  that decides whether a sparse division algorithm is worth specifying.

**Comparators.** SymPy's sparse ring elements, `informational`: SymPy is
the oracle and is Python, so the ratio orients rather than qualifies.
FLINT's `fmpz_poly` via python-flint, `informational` and restricted to
the crossover family: it is a dense representation, so above the
crossover the comparison measures the choice of representation rather
than the quality of either implementation, and a threshold there would
be meaningless. No `gating` external comparator is registered, and that
is the justification.

Two required internal checks, which matter more than the external ones:

- `mul` and `add` on the sparse families must be faster than the same
  operation on `toDense` of the same inputs by a factor that grows with
  `n/t`, and the crossover family must locate the ratio where that stops
  being true.
- `substPow s k` must be independent of `k` up to the cost of
  multiplying the exponents, since it does not touch the coefficients. A regression here means an implementation started
  materialising the intermediate degrees.

## The Mathlib layer

`hex-sparse-poly-mathlib` identifies the type with `Polynomial R`:

```lean
def equiv [CommRing R] [DecidableEq R] : SparsePoly R ≃+* Polynomial R

theorem coeff_equiv (s : SparsePoly R) (e : Nat) : (equiv s).coeff e = s.coeff e
theorem equiv_toDense (s : SparsePoly R) : HexPolyMathlib.equiv s.toDense = equiv s
theorem equiv_support (s : SparsePoly R) : (equiv s).support = s.support.toList.toFinset
theorem equiv_eval (s : SparsePoly R) (x : R) : (equiv s).eval x = s.eval x
theorem equiv_derivative (s : SparsePoly R) :
    Polynomial.derivative (equiv s) = equiv s.derivative
theorem equiv_compose (s t : SparsePoly R) : (equiv s).comp (equiv t) = equiv (s.compose t)
theorem equiv_substPow (s : SparsePoly R) (k : Nat) :
    (equiv s).comp (Polynomial.X ^ k) = equiv (s.substPow k)
```

`equiv` is **defined** as
[hex-poly-mathlib](../../HexPolyMathlib/SPEC/hex-poly-mathlib.md)'s
`DensePoly R ≃+* Polynomial R` composed with `toDense`. The ring
homomorphism fields are then transported rather than reproved, which is
the reason the Mathlib-free layer carries `toDense_add`, `toDense_mul`,
`toDense_zero`, and `toDense_one` as theorems in the first place. The
inverse direction is `ofDense`, and the two round-trip theorems are what
make the pair an equivalence.

`equiv_support` is the one statement that is genuinely about this
representation rather than transported through the dense one: it says
the stored term array is Mathlib's `support`, which is the sense in
which the representation is the sparse one. It needs both halves of
`SparsePolyCanonical` (duplicates would make the multiset a proper
multiset, and a stored zero would put an element in the array that
`Polynomial.support` omits), and it is the cleanest place to see why the
invariant is stated the way it is.

Following the project split, no theorem about `SparsePoly` belongs in
the companion beyond these and one correspondence lemma per public
operation.

## Prerequisite changes in other libraries

None. `DensePoly`, `DensePolyNormalized`, `DensePoly.coeff`,
`DensePoly.monomial`, `DensePoly.compose`, `DensePoly.derivative`, and
the `divMod`/`gcd` family already exist with the hypotheses this SPEC
uses, and `HexBasic/Fold.lean` already supplies the `List.foldl` algebra
the sort-and-combine proof needs.

One candidate for promotion, not a prerequisite: if the stable
sort-by-key with a combining fold that the `@[csimp]` twin uses proves
reusable, it belongs in hex-basic rather than here, in the same way that
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) puts its reusable map
algorithms in `HexBasic/ExtTreeMap.lean`. The sparse matrix work
described in [future-work](../future-work.md) canonicalises coordinate
form the same way and would be the second consumer. Write it here
first and promote it when that happens.

## Milestones

1. **The representation.** `SparsePolyCanonical`, `SparsePoly`,
   `addTerm` with its invariant proof, `ofTerms`, `coeff`, `ext_coeff`,
   `DecidableEq` through `List` equality, and the accessors. The
   invariant proofs in this milestone are what the whole library rests
   on, and the cancellation and duplicate cases have their conformance
   checks written first.

2. **Arithmetic.** `add`, `neg`, `sub`, `scale`, `mulMonomial`, `mul` as
   specified, `pow`, and the ring laws. The `@[csimp]` multiplication
   twin comes after the bench family that picks it.

3. **The conversions.** `coeffsOfTerms`, `termsOfCoeffs`, `toDense`,
   `ofDense`, the homomorphism laws, and both round trips at the array
   level and the bundled level. At the end of this milestone `coeff_mul`
   is available by transport.

4. **Evaluation, derivative, substitution.** Gap Horner, the derivative
   with its zero filter, `substPow`, `substScale`, and `compose`, with
   the dense agreement theorems.

5. **Gcd and division through the conversions**, and the bench families,
   including the crossover measurement and the conversion share in
   "convert-gcd". The crossover number is written back into this SPEC
   when it exists.

6. **The companion.**

## File organisation

```
HexSparsePoly/
  Basic.lean      -- SparsePolyCanonical, SparsePoly, addTerm, ofTerms,
                  --   coeff, ext_coeff, DecidableEq, accessors
  Arith.lean      -- add, neg, sub, scale, mulMonomial, mul, pow, ring laws
  Dense.lean      -- coeffsOfTerms, termsOfCoeffs, toDense, ofDense,
                  --   homomorphism laws, round trips
  Eval.lean       -- eval, derivative, substPow, substScale, compose
  Euclid.lean     -- divModMonic, divMod, gcd, divExactMonic? through DensePoly
HexSparsePoly.lean
HexSparsePolyMathlib/
  Equiv.lean      -- equiv and the correspondence lemmas
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
          rationale: "SymPy is the conformance oracle and is Python, so the ratio orients rather than qualifies."
        - tool: FLINT fmpz_poly via python-flint
          class: informational
          rationale: "fmpz_poly is dense, so above the crossover the comparison measures the choice of representation rather than the quality of either implementation. Recorded on the crossover family only."
      input_families:
        - name: sparse-arithmetic
          description: addition and multiplication of 2 to 64 term inputs at degrees 10^3 to 10^6
        - name: sparse-multiplication
          description: low-collision and high-collision products across the three candidate implementations
        - name: crossover
          description: the same operations against DensePoly with the term count swept from 2 to the degree
        - name: evaluation
          description: gap Horner against dense Horner across the same sweep
        - name: substitution-power
          description: substPow on the cyclotomic shapes against the dense route
        - name: convert-gcd
          description: gcd and divMod through the conversions, recording the conversion share separately
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
  [future-work](../future-work.md), and design principle 10 is what
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
