# hex-summation (certified hypergeometric summation: Gosper, Zeilberger, Hyper; depends on hex-poly + hex-mv-poly + hex-resultant + hex-matrix + hex-row-reduce + hex-berlekamp-zassenhaus)

Certificate-checked hypergeometric summation: Gosper's algorithm for
indefinite sums, Zeilberger's creative telescoping for definite sums,
and Petkovšek's Hyper for hypergeometric solutions of recurrences. The
searches run untrusted and emit certificates; the verified surface is a
family of polynomial-identity checkers over `MvPoly` and the
`ℚ`-sequence theorems that turn an accepted certificate into a summation
statement. Mathlib-free. The companion `hex-summation-mathlib` carries
the semantics over `Finset.sum`, `Nat.choose`, and `Nat.factorial`, the
term-class recognizer, and the `gosper`, `zeilberger`, and `hyper`
tactics.

This SPEC expands the "Symbolic summation" entry in
[future-work](../future-work.md). That entry's central claim survives
contact with the mathematics: the identity a certificate asserts is an
identity of rational functions, clearing denominators turns it into a
polynomial identity, and the verified surface is therefore small. Two of
its subsidiary claims do not survive, and are corrected under
"Corrections to the future-work entry" below.

## What the tree has today

`DensePoly R` (hex-poly) has ring arithmetic, `compose`
(`HexPoly/Operations.lean:1153`), `eval` (`:1010`), and field-based
`divMod`, `gcd`, and `xgcd` (`HexPoly/Euclid/DivGcd.lean`). It is
already exercised at `DensePoly Rat`
(`HexPoly/Euclid/MulRing.lean:937`), so the `Lean.Grind` instances for
`Rat` that every generic operation needs are in place.

`MvPoly n R cmp` (hex-mv-poly) has ring arithmetic, `subst`
(`HexMvPoly/Structural.lean:187`), and `eval` / `eval₂`
(`HexMvPoly/Eval.lean`). `subst` at `Xᵢ + 1` is the shift operator this
library applies constantly. `HexMvPoly/KernelTests.lean` maintains
kernel-reducibility of the arithmetic, which is the property the
checkers replay under `decide +kernel`.

hex-resultant computes resultants by the subresultant pseudo-remainder
sequence over any coefficient ring with `ExactDivLaws`. The dispersion
computation in the untrusted search is a resultant with coefficient
ring `DensePoly Rat`. `HexResultant/Fraction.lean` also holds a
proof-side fraction-field construction; it is proof infrastructure for
the Brown-Traub identities, not an executable rational-function type,
and this SPEC does not change that.

hex-row-reduce solves linear systems over any `Lean.Grind.Field`
(`HexRowReduce/Api.lean`), with `spanCoeffs` soundness and `nullspace`
soundness and completeness. Instantiated at `Rat` it is the
undetermined-coefficients solver for Gosper's polynomial equation.

hex-berlekamp-zassenhaus factors `ℤ[x]` completely. Hyper's candidate
enumeration runs over monic factors of two coefficient polynomials, and
that factorization is the one place this library consumes it.

What the tree does not have: an executable rational-function type, any
`Int → ℚ` summation helper, and any statement about `Nat.choose` or
`Nat.factorial` ratios. The first is deliberately not introduced here
either (see "Corrections" below); the second lives in this library; the
third lives in the companion.

## Prior art

Surveyed against the complete AFP entry list and the wider ecosystem
(checked 2026-08-21; the usual caveat that later entries may appear).
The headline is a negative: **no system has a formalization of
Gosper's algorithm, Zeilberger's algorithm, Petkovšek's Hyper,
Gosper-Petkovšek normal form, or dispersion**. There is no AFP entry
for any of them, Manuel Eberl's AFP output on hypergeometric topics is
the analytic `pFq` function and not summation, and searches over
Coq/Rocq, ACL2, Mizar, PVS, and Lean find nothing on the algorithm
side. What exists, in every case, is a certificate checker with the
search run in a computer algebra system. Two are substantial and both
shaped this SPEC.

**The Coq/Rocq `apery` project** (Chyzak, Mahboubi, Sibut-Pinote,
Tassi; ITP 2014, LMCS journal version) is the only substantial
certificate-based creative-telescoping formalization in existence:
Maple produces recurrence operators and telescoping certificates for
the Apéry numbers, and roughly 7400 lines of Coq replay them. Three of
its decisions are adopted here.

- A hypergeometric term is not a syntactic class but a sequence
  together with *proved shift-quotient propositions*, guarded by
  explicit precondition regions that exclude the hyperplanes where
  the quotient's denominator vanishes (`annotated_recs_c.v`). That is
  this SPEC's multiplied-form ratio hypothesis, arrived at
  independently and confirmed by their experience.
- Its master lemma `sound_telescoping` (`punk.v`) assumes the
  certificate identity only away from a declared bad set and returns
  a conclusion with explicit boundary terms, an exceptional-point
  correction sum, and staircase terms, which the caller then
  evaluates and cancels concretely. The exceptional-set variant under
  "The summed recurrence" below is this lemma's shape.
- Its performance history is the replay-cost warning: the ITP 2022
  follow-up ("Reflexive tactics for algebra, revisited") exists
  because closing the per-certificate algebra with `field` plus
  reflection over `ℚ` was the bottleneck. This SPEC's checkers replay
  as polynomial identities in `MvPoly`, decided by the library's own
  verified arithmetic, precisely to keep the replay out of
  elaboration-time field normalisation.

**Harrison's HOL Light WZ checker** ("Formal Proofs of Hypergeometric
Sums", JAR 2015) verifies Maxima-produced WZ certificates by an
entirely different route: interpret binomials over `ℝ` through the
total Γ function so the vanishing conventions hold by continuity,
prove the certificate identity at generic real points off the
algebraic bad set by a Baire-category argument, and reach the integer
points by limits. The route is not taken here: it couples a
combinatorial identity to a real-analytic prerequisite chain and delivers
statements about `ℝ`-valued interpretations, where the apery route is
exact rational arithmetic in the house style. Two of Harrison's
findings are kept anyway: his report that certificate denominators
vanish at *mid-range* points and not only at the support boundary
(the reason the exceptional-set variant exists and is not hard-coded
to the boundary), and his observation that the factorial-quotient
reading of a summand is meaningless outside its support, which is the
same fact that forces the multiplied ratio form.

**Eberl's AFP `Linear_Recurrences`** solves a different problem
(constant-coefficient recurrences by generating functions) but
contributes two patterns: a computational rational-function type that
carries its nonvanishing invariant through arithmetic, which is the
shape an executable `RatFunc` would take if the open question on it is
ever answered; and factorizations as *data with a checking predicate*,
decoupled from the untrusted producer, which is how this library's
searches hand every result to a checker before returning it.

Two further data points locate the gap. Both existing ζ(3)
formalizations (Eberl's Isabelle one and the Lean 4 one,
arXiv:2503.07625) deliberately follow Beukers' integral method to
avoid creative telescoping, machinery neither had. And the WZ-guided
proof-sketching pipeline of arXiv:2605.04472 generates Lean 4 WZ proof
plans with no verified checker to discharge them against; this
library's checkers are the missing trusted replay for exactly that
pipeline.

## Scope

In scope: certificate types and checkers for Gosper, Zeilberger, and
Hyper certificates over `ℚ` with symbolic parameters; the `ℚ`-sequence
semantics (telescoping soundness, the summed recurrence, equality of
sequences from a shared recurrence and initial values, eventual
nonvanishing bounds); the untrusted searches (Gosper-Petkovšek normal
form, dispersion, degree bounds, undetermined coefficients, the
Zeilberger order loop, the Hyper factor-pair enumeration); and, in the
companion, the `Finset.sum` semantics over characteristic-zero fields,
the ratio-lemma kit for `Nat.choose` / `Nat.factorial` /
`ascPochhammer`, the term-class recognizer, and the three tactics.

Not in scope:

- **Zeilberger's theorem** (every proper hypergeometric term satisfies
  a `k`-free recurrence). This is the one substantial piece of
  hypergeometric theory in the area, resting on the Ore-Sato
  characterization of proper terms, and it buys only a completeness
  statement about the search: that the order loop terminates before
  `maxOrder` on proper input. No consumer-facing theorem needs it. The
  search is capped and reports exhaustion, exactly as hex-rcf states no
  completeness theorem for its `decide`. Formalising it later would
  change no API in this SPEC.
- **Completeness of Gosper and Hyper** as nonexistence proofs. Gosper's
  theorem (no rational certificate implies no hypergeometric
  antidifference) and Petkovšek's completeness (the enumeration finds
  every hypergeometric solution) justify trusting a *failed* search,
  and a failed search here proves nothing. See "What an accepted
  certificate proves".
- **Holonomic closure properties.** The future-work entry already
  defers these until the certificate checker has proved itself; this
  SPEC keeps that deferral.
- **q-analogues** (q-Gosper, q-Zeilberger), **multiple sums** (Sister
  Celine, Wegschaider), and **the continuous analogue**
  (Almkvist-Zeilberger for integrals). Each is a separate certificate
  language over a different ratio field.
- **Infinite bilateral sums.** Sequences are `ℤ`-indexed and sums run
  over finite integer intervals, so two-sided finite ranges are
  native; a sum with infinite support is a limit statement and out of
  scope.

## Corrections to the future-work entry

Two claims in the entry are refined by this SPEC, recorded because both
are easy to reintroduce.

**Neither gcd nor rational-function normalisation is a prerequisite of
the verified layer.** The entry lists "multivariate polynomial
arithmetic, gcd, and rational function normalisation" as prerequisites.
The checker verifies an equality of rational expressions by
cross-multiplying: both sides are formed as fraction pairs with no
cancellation, and the identity checked is `lhsNum * rhsDen = rhsNum *
lhsDen` in `MvPoly`. No gcd is computed and no fraction is reduced
anywhere a proof depends on it. Gcd (univariate, from hex-poly's
Euclid) and fraction reduction appear only inside the untrusted search,
where the Gosper-Petkovšek normal form needs them. In particular
hex-mv-gcd is not a dependency at all.

**The quotient-form identity in the entry does not survive the support
boundary; the multiplied form does.** The entry states the Gosper
identity as `y(k+1) t(k+1) − y(k) t(k) = t(k)`, which presumes the term
ratio `t(k+1)/t(k)` exists. At the edge of the support of a binomial
summand the ratio is `0/0` and the quotient form is unusable exactly
where the telescoping boundary terms live. Every ratio hypothesis in
this library is therefore stated multiplied out, as
`q(k) · t(k+1) = p(k) · t(k)`, and the load-bearing fact is that the
multiplied form holds at *every* natural argument. The worked example
is in "Term ratios in multiplied form" below.

## Term ratios in multiplied form

A hypergeometric term is not represented syntactically. The library
never defines "hypergeometric"; it takes an arbitrary sequence together
with a *ratio hypothesis*, a pair of polynomials `p, q` and the fact

```
q(k) · t(k+1) = p(k) · t(k)    for every k in the relevant range.
```

This form is chosen over the quotient form for one reason: it holds
across zeros of `t`. The example that decides the design is the
`Nat.choose` column ratio. Over `ℚ`, with true subtraction,

```
(k + 1) · C(n, k+1) = (n − k) · C(n, k)
```

holds for **all** naturals `n, k`: for `k < n` it is the usual ratio,
at `k = n` both sides are `n − k = 0` times a value, and for `k > n`
both binomials vanish. The quotient form fails at `k = n` (division by
`C(n, n+1) = 0`) which is precisely the boundary the definite-sum
telescoping must cross. With the ℤ-extended binomial of the
companion's kit the same multiplied identity holds at *every pair of
integers*, including negative upper argument, so the kit's ratio
lemmas carry no case split at all; the one case analysis (relating the
ℤ-extension to `Nat.choose` on `0 ≤ k`) is done once, inside the shim
pack, and consumers of this library never see it.

**Variables and parameters.** All certificate polynomials live in
`MvPoly (s + 2) Rat cmp` at a fixed monomial order, with a fixed variable
convention: variable `0` is `n` (the recurrence variable; unused by
Gosper certificates), variable `1` is `k` (the summation variable), and
variables `2, …, s + 1` are the `s` free parameters. The arity is
`s + 2` *by type*, not by convention: every certificate is
parameterized by its parameter count `s`, so a certificate cannot fail
to have the two shifted variables. Parameters are what let
one certificate prove Vandermonde `∑ₖ C(m,k) C(n,r−k) = C(m+n,r)` with
`m` and `r` symbolic: the checker's polynomial identity is an identity
in all of `n, k, m, r`, and the semantics theorems quantify over a
rational value for each parameter. Shifts touch only variables `0` and
`1`; parameters are inert.

```lean
namespace Hex.Summation

/-- A term ratio in multiplied form: the claim
`den · t(shifted) = num · t`, with the shift direction supplied by
context. Both entries are `(s + 2)`-variate; which variable is shifted is a
property of the consuming certificate, not of the pair. -/
structure Ratio (s : Nat) where
  num : MvPoly (s + 2) Rat cmp
  den : MvPoly (s + 2) Rat cmp

/-- Shift in the summation variable: substitute `X₁ + 1` for `X₁`. -/
def shiftK (f : MvPoly (s + 2) Rat cmp) : MvPoly (s + 2) Rat cmp

/-- Shift in the recurrence variable: substitute `X₀ + 1` for `X₀`. -/
def shiftN (f : MvPoly (s + 2) Rat cmp) : MvPoly (s + 2) Rat cmp
```

Both shifts are `MvPoly.subst` at a substitution that is the identity
off the named variable. Ratios compose by multiplying numerators and
denominators, which is how the recognizer assembles the ratio of a
product of factors; no reduction is performed, and none is needed for
soundness.

## Certificates and the checkers

Three certificate types, three Boolean checkers, three soundness
theorems. Each checker verifies a cross-multiplied polynomial identity
plus nonvanishing *as polynomials* of the denominators it multiplied
by. Pointwise nonvanishing at the integer arguments a particular sum
visits is not the checker's job; it appears as hypotheses of the
semantics theorems and is discharged by the devices under "Eventual
nonvanishing" below.

There is no analogue of hex-primality's `CheckedPrimeCert` subject
index, and the reason is worth recording: a primality certificate is
*about* a syntactic subject stored inside it, so a mismatch between
certificate and claim is a real hazard. A summation certificate is
about a semantic object, the sequence, which cannot be stored. The
linkage is instead by hypothesis: every semantics theorem takes the
ratio hypothesis stated in terms of the certificate's own `p` and `q`
fields, so a certificate for one term cannot discharge a goal about
another without the ratio hypothesis failing.

### Gosper

```lean
/-- A Gosper certificate for a term with `k`-ratio `r`: the rational
function `y = u/v` with `y(k+1) r(k) − y(k) = 1`, stored cleared. -/
structure GosperCert (s : Nat) where
  r    : Ratio s            -- the term ratio the certificate is for
  u v  : MvPoly (s + 2) Rat cmp   -- the antidifference multiplier y = u/v

def checkGosper (c : GosperCert s) : Bool
```

`checkGosper` verifies, writing `p = c.r.num`, `q = c.r.den`, and `f⁺`
for `shiftK f`:

1. `q ≠ 0` and `c.v ≠ 0` (as polynomials), and every field free of
   variable `0`: a Gosper certificate is about the summation variable
   and the parameters only, and freeness is what lets the semantics
   theorem evaluate variable `0` at an arbitrary junk value.
2. `u⁺ · p · v − u · q · v⁺ = q · v · v⁺` in `MvPoly (s + 2) Rat cmp`.

Condition 2 is the identity `y(k+1) r(k) − y(k) = 1` after multiplying
through by `q · v · v⁺`. Nothing else is checked; in particular no
normal form, no degree condition, and no claim that `u/v` is reduced.
A denominator-inflated certificate is a valid certificate.

### Zeilberger

```lean
/-- A Zeilberger certificate: a `k`-free recurrence of order `d` with
coefficients `a₀ … a_d` in the recurrence variable and parameters, and
the telescoping multiplier `R = u/v` with
`∑ⱼ aⱼ(n) F(n+j, k) = G(n, k+1) − G(n, k)` for `G = R · F`. -/
structure ZeilbergerCert (s : Nat) where
  rk rn : Ratio s                     -- k-shift and n-shift ratios of F
  d     : Nat
  a     : Vector (MvPoly (s + 2) Rat cmp) (d + 1)   -- free of variable 1
  u v   : MvPoly (s + 2) Rat cmp

def checkZeilberger (c : ZeilbergerCert s) : Bool
```

The coefficient count is `d + 1` *by type* (`Vector`, not `Array`
plus a size check), so a mismatched order is unrepresentable.

The checker builds, from the `n`-ratio alone, the shifted products

```
Nⱼ = ∏_{i<j} shiftNⁱ (rn.num)      Qⱼ = ∏_{j≤i<d} shiftNⁱ (rn.den)
```

so that `F(n+j, k) / F(n, k) = Nⱼ / (N-denominator)` and all `d + 1`
quotients acquire the common denominator `D = ∏_{i<d} shiftNⁱ (rn.den)`.
It verifies:

1. `rk.den ≠ 0`, `rn.den ≠ 0`, `v ≠ 0`, each `aⱼ` free of variable
   `1`, and the top coefficient `a_d ≠ 0` (as a polynomial), so a
   certificate cannot pad its order with zero coefficients. A
   parameter specialization can still annihilate `a_d` at particular
   values; that is the semantic leading-coefficient side condition of
   `eq_of_recurrence`, not the checker's concern.
2. The cross-multiplied identity in `MvPoly (s + 2) Rat cmp`:

   ```
   (∑ⱼ aⱼ · Nⱼ · Qⱼ) · rk.den · v · v⁺  =  (u⁺ · rk.num · v − u · rk.den · v⁺) · D
   ```

   where `f⁺` is `shiftK f`. The left side is
   `(∑ⱼ aⱼ F(n+j,k)/F(n,k))` and the right side is
   `(G(n,k+1) − G(n,k))/F(n,k)`, both multiplied by
   `D · rk.den · v · v⁺`.

The certificate does not carry `Nⱼ` or `Qⱼ`; the checker recomputes
them from `rn`, for the same reason hex-primality reads the factor
prime off the child certificate rather than storing it twice: a stored
copy would need an agreement check, and removing the redundancy removes
the check.

A WZ pair is the special case `d = 1`, `a₀ = 1`, `a₁ = −1` after
normalising by the closed form; no separate certificate type is needed
and the companion notes the connection where it proves identities of
the form `S(n) = C(n)`.

### Hyper

```lean
/-- A Hyper certificate for the recurrence `∑ⱼ cⱼ(n) y(n+j) = 0`: a
ratio `p/q` such that any sequence with `q(n) y(n+1) = p(n) y(n)`
satisfies the recurrence wherever the denominators clear. -/
structure HyperCert (s : Nat) where
  d   : Nat
  c   : Vector (MvPoly (s + 2) Rat cmp) (d + 1)   -- free of variable 1
  p q : MvPoly (s + 2) Rat cmp                    -- free of variable 1

def checkHyper (h : HyperCert s) : Bool
```

The checker verifies `p ≠ 0`, `q ≠ 0`, `c₀ ≠ 0` and `c_d ≠ 0` (as
polynomials, so the recurrence's order is genuine at both ends), and

```
∑ⱼ cⱼ · (∏_{i<j} shiftNⁱ p) · (∏_{j≤i<d} shiftNⁱ q) = 0
```

which is the recurrence applied to a sequence with ratio `p/q`, with
`y(n+j)/y(n) = ∏_{i<j} (p/q)(n+i)` cleared through the common
denominator. Everything is univariate in spirit (variable `0` plus
parameters); variable `1` is unused and the checker rejects
certificates that mention it.

## Semantics over ℚ

The Mathlib-free semantics is stated for `ℚ`-valued sequences
**indexed by `ℤ`**, summed over half-open integer intervals. The
prior art is unanimous on the index type: apery built a ℤ-extended
binomial and a bespoke ℤ-indexed bigop library because the shift
reindexing under `n ↦ n + j`, `k ↦ k + 1` is where a ℕ-indexed
development bleeds truncated-subtraction case splits, and Harrison
paid in limit arguments for staying on ℕ. The checkers are indifferent
(a polynomial identity has no index type); only this layer and the
companion see the choice.

```lean
/-- `∑_{a ≤ i < b} f i`; zero when `b ≤ a`. -/
def sumIco (f : Int → Rat) (a b : Int) : Rat

/-- Evaluate a certificate polynomial at recurrence variable `n`,
summation variable `k`, and parameter vector `w`. -/
def evalAt (f : MvPoly (s + 2) Rat cmp) (n k : Int) (w : Vector Rat s) : Rat
```

`evalAt` is `MvPoly.eval` at the assignment fixed by the variable
convention; its ring-homomorphism lemmas come from hex-mv-poly's
evaluation theory and are what carry a polynomial identity to a
pointwise rational identity.

### Telescoping soundness (Gosper)

```lean
theorem sumIco_eq_of_checkGosper {c : GosperCert s}
    (hc : checkGosper c = true) (w : Vector Rat s)
    (t : Int → Rat) (a b : Int) (hab : a ≤ b)
    (hratio : ∀ k, a ≤ k → k < b → evalAt c.r.den 0 k w * t (k+1)
                                 = evalAt c.r.num 0 k w * t k)
    (hq : ∀ k, a ≤ k → k < b → evalAt c.r.den 0 k w ≠ 0)
    (hv : ∀ k, a ≤ k → k ≤ b → evalAt c.v 0 k w ≠ 0) :
    sumIco t a b
      = evalAt c.u 0 b w / evalAt c.v 0 b w * t b
      − evalAt c.u 0 a w / evalAt c.v 0 a w * t a
```

The proof shape: evaluate the checker identity at each `k ∈ [a, b)`
(the evaluation homomorphism), divide by the three nonvanishing values
to recover `G(k+1) − G(k) = t k` for `G(k) = (u/v)(k) · t k`, and
telescope by induction on `(b − a).toNat`. The `hab` hypothesis is
load-bearing, not decorative: on a reversed interval every pointwise
hypothesis is vacuous and `sumIco` is zero, while the boundary
difference need not be (`u = X₁`, `v = q = p = 1`, `t = 1` is an
accepted certificate whose boundary difference at `a = 1, b = 0` is
`−1`). Division here is `ℚ` field division;
the junk value at zero never arises because the hypotheses exclude it
pointwise. All of this is `Rat` arithmetic and `grind`-level algebra,
with no Mathlib tactic in reach and none needed.

The Gosper theorem also gets an exceptional-edge variant of the same
shape as the Zeilberger one below, and it is not optional: a term that
vanishes at an interior point with a nonzero successor *forces*
`q(k₀) = 0` in any polynomial multiplied-form ratio (from
`q(k₀) · t(k₀+1) = p(k₀) · 0` with `t(k₀+1) ≠ 0`), so `hq` is
unsatisfiable on any range containing `k₀`. The first worked example
is already like this: `t k = k · k!` has `t 0 = 0`, `t 1 = 1`, so
every ratio for it has `q(0) = 0` and the tactic sums `[1, b)` with
the `k = 0` term split off. The recognizer performs that split; the
variant carries the general case.

### The summed recurrence (Zeilberger)

Two layers, pointwise then summed:

```lean
theorem telescoped_of_checkZeilberger {c : ZeilbergerCert s}
    (hc : checkZeilberger c = true) (w) (F : Int → Int → Rat) (n a b : Int)
    (hab : a ≤ b)
    (hk : ∀ k, a ≤ k → k < b → ∀ j ≤ c.d,   -- k-ratio at row n+j, n-ratio between rows
        ⟨multiplied ratio facts for F at the visited points⟩)
    (hnz : ⟨pointwise nonvanishing of rk.den, shiftNⁱ rn.den (i < d), v,
           at the visited points⟩) :
    ∑ⱼ evalAt (c.a[j]) n 0 w * sumIco (F (n + j)) a b
      = G n b − G n a
```

with `G n k = evalAt c.u n k w / evalAt c.v n k w * F n k`. The
hypothesis lists are abbreviated here; the SPEC commits to the exact
visited-point sets being the minimal ones the pointwise derivation
uses, and to the theorem being stated with explicit boundary terms.
**No vanishing of `G` at the boundary is assumed.** `G n a` is rarely
zero and `G n b` is zero only when the summand vanishes past its
support; both facts belong to the consumer.

On top of it, the natural-boundary corollary for
`S n = sumIco (F n) 0 (n + 1)` takes `a = 0`, `b = n + c.d + 1`, the
hypothesis `0 ≤ n` (which orders every interval in the splitting), a
vanishing hypothesis
`∀ j ≤ d, ∀ k, n + j < k → k ≤ n + d → F (n+j) k = 0`, and concludes
the pure recurrence

```lean
∑ⱼ evalAt (c.a[j]) n 0 w * S (n + j) = G n (n + d + 1) − G n 0
```

A variant without the vanishing hypothesis keeps the correction sums
`∑_{k=n+j+1}^{n+d} F (n+j) k` explicit; summands with no binomial
cutoff use it.

A third variant is the apery `sound_telescoping` shape, and it is the
one the pipeline uses when a certificate denominator vanishes at
interior points of the range, which Harrison's HOL Light development
documents as the common case rather than the pathological one. Its
exceptional set is **not a fixed finite set of points**: a denominator
root such as `k = n + 1` moves with `n`. The representation is a
declared finite list of affine lines `α·n + β·k + γ = 0` (coefficients
over all `s + 2` variables, from the factored-denominator witness
below), each with `β ≠ 0`, so that at each `n` a line contributes at
most one exceptional `k` and `|E n|` is bounded by the number of
lines; a factor with `β = 0` does not vanish at isolated `k` and is
handled by the `n₀` threshold instead, never by the exceptional set.
Writing `H n k = ∑ⱼ aⱼ(n) F (n+j) k` and defining `G` by total `ℚ`
division (junk values at poles are harmless because nothing is
assumed there), the variant assumes `H n k = G n (k+1) − G n k` only
for `k ∉ E n` with **shifted edges included** (`k` is exceptional
when either `k` or `k + 1` lies on a declared line, since `v(k+1)`
occurs), and concludes

```
∑_{k ∈ [a,b)} H n k = G n b − G n a + ∑_{k ∈ E n ∩ [a,b)} (H n k − (G n (k+1) − G n k))
```

The correction terms are symbolic functions of `n`, one per line, and
the companion's obligation is explicit: prove each vanishes or carry
it into the forcing term of the recurrence. Nothing about them is
assumed. The all-points statement above is the corollary at an empty
line list.

### Equality from a shared recurrence

The lemma both the definite-sum pipeline and the `hyper` tactic finish
with:

```lean
theorem eq_of_recurrence (S C : Int → Rat) (d : Nat) (n₀ : Int)
    (a : Vector (Int → Rat) (d + 1)) (f : Int → Rat)
    (hlead : ∀ n ≥ n₀, a[d] n ≠ 0)
    (hS : ∀ n ≥ n₀, ∑ⱼ a[j] n * S (n + j) = f n)
    (hC : ∀ n ≥ n₀, ∑ⱼ a[j] n * C (n + j) = f n)
    (hinit : ∀ n, n₀ ≤ n → n < n₀ + d → S n = C n) :
    ∀ n ≥ n₀, S n = C n
```

The recurrence is stated with a shared **forcing term** `f`, not as
homogeneous, because the two sides arrive differently: the telescoped
recurrence for a sum carries boundary and exceptional-correction terms
on its right side, while `checkHyper` certifies a homogeneous
recurrence for a closed form. The pipeline either proves the sum's
forcing term is zero (the usual case, when the boundary values vanish
and the corrections cancel) and uses `f = 0` on both sides, or keeps
`f` and proves the closed form's side matches it. Matching the two
right sides is a named obligation of the pipeline, never an implicit
step.

Strong induction on `(n − n₀).toNat`: for `n ≥ n₀ + d` the recurrence
at `n − d` determines `S n` and `C n` from the previous `d` values
because the leading coefficient is nonzero. Indices below `n₀` are not
concluded (over `ℤ` there is no floor to induct from); the pipeline
evaluates the finitely many indices below `n₀` a goal actually needs.
The coefficients are abstract `Int → Rat` functions here so the same
lemma serves certificates (coefficients are polynomial evaluations)
and hand-stated recurrences.

### Hyper semantics

```lean
/-- The sequence with ratio `p/q` from `y n₀ = 1`, extended upward by
the recursion `y (n+1) = eval p n / eval q n * y n`, and `0` below
`n₀`. -/
def ofRatio (h : HyperCert s) (w) (n₀ : Int) : Int → Rat

theorem ofRatio_recurrence {h : HyperCert s} (hc : checkHyper h = true)
    (w) (n₀ : Int)
    (hnz : ∀ n ≥ n₀, evalAt h.p n 0 w ≠ 0 ∧ evalAt h.q n 0 w ≠ 0) :
    ∀ n ≥ n₀, ∑ⱼ evalAt (h.c[j]) n 0 w * ofRatio h w n₀ (n + j) = 0

theorem ofRatio_ne_zero ... : ∀ n ≥ n₀, ofRatio h w n₀ n ≠ 0
```

`ofRatio` is executable and its values are exact rationals, which is
what the initial-value comparisons in the `hyper` tactic evaluate.

### Eventual nonvanishing

Two devices discharge the "for all `n ≥ n₀`" side conditions above
without per-point work.

```lean
/-- `1 + max |aᵢ| / |lead|` for a nonzero univariate restriction. -/
def cauchyBound (f : DensePoly Rat) : Rat

theorem eval_ne_zero_of_cauchyBound {f : DensePoly Rat} (hf : f ≠ 0)
    {x : Rat} (hx : cauchyBound f < |x|) : f.eval x ≠ 0
```

The Cauchy bound is the general device: any nonzero univariate
polynomial in `n` is nonvanishing past its bound, the bound is a
computable rational, and the comparison `n₀ > cauchyBound f` is decided
by `decide`. The proof is the leading-term-dominates argument in `Rat`
absolute values, Mathlib-free.

For the denominators the front-end actually produces, there is a
sharper decidable criterion. A proper hypergeometric summand's shift
ratios factor into affine pieces, and the piece is where every
pointwise side condition above ultimately lands:

```lean
/-- An affine form `cn·n + ck·k + ⟨cw, w⟩ + c` over all `s + 2`
variables. -/
structure AffineFactor (s : Nat) where
  cn ck : Int
  cw    : Vector Int s
  c     : Int

/-- An optional side-condition witness for one certificate
denominator: a rational constant and a multiset of affine factors
whose product is claimed to be the stored polynomial. -/
structure DenWitness (s : Nat) where
  const   : Rat
  factors : List (AffineFactor s)

def checkDenWitness (den : MvPoly (s + 2) Rat cmp) (dw : DenWitness s) : Bool
```

`checkDenWitness` multiplies the factored form out and compares it to
the stored denominator, so a witness cannot disagree with the
polynomial the identity checker used. Witnesses are **optional and
separate from the identity checkers**: each certificate type carries
an optional `DenWitness` per denominator field (`r.den` and `v` for
Gosper; `rk.den`, `rn.den`, and `v` for Zeilberger; `q` for Hyper),
the identity checkers ignore them, and the semantics side conditions
are discharged factor by factor from a validated witness. The
exceptional-set lines of the summed recurrence are read off the same
witness.

For a parameter-free factor (`cw = 0`), nonvanishing over the
trapezoid `{(n, k) : n ≥ n₀, 0 ≤ k ≤ n + e}` is decided by sign
conditions on the two boundary lines `k = 0` and `k = n + e`, each
univariate linear in `n`:

```lean
/-- Sufficient (not necessary) for: the factor is nonzero at every
integer point with `n ≥ n₀`, `0 ≤ k ≤ n + e`. -/
def AffineFactor.nonvanishingOn (ℓ : AffineFactor 0) (n₀ : Int) (e : Nat) : Bool

theorem AffineFactor.nonvanishingOn_sound ...
```

The criterion is deliberately conservative: it certifies a factor that
never changes sign on the region, and rejects factors such as
`2k − 1` that cross zero over `ℝ` while missing every integer point.
The exact divisibility refinement (a factor with `gcd(cn, ck) ∤ c`
vanishes at no integer point at all) is a compatible strengthening an
implementation may add; soundness is one-directional either way. A
factor with parameter coefficients has no closed criterion, because
nonvanishing then depends on the parameter values: the recognizer
emits its condition as a goal, discharged from the goal's own
hypotheses (`r ≤ m + n`, a variable known to be a natural, and so on)
or left to the user. A denominator outside the affine class is legal
in a certificate; it simply has no witness, and its pointwise
conditions surface as goals (see the fall-through list under "The
front-end recognizer").

## The search

Everything in this section is untrusted compiled code with no
correctness theorems, following the pattern of hex-rcf's
`SturmBuilder`: the search instruments a classical algorithm, and
**only checker-approved certificates are returned**. Every public
search function re-runs the relevant checker before returning, so its
postcondition is by construction, one line each:

```lean
def gosper? (r : Ratio s) : Option (GosperCert s)
def zeilberger? (rk rn : Ratio s) (maxOrder : Nat := 6) :
    Except ZeilbergerFailure (ZeilbergerCert s)
def hyperSolve (d : Nat) (c : Vector (MvPoly 2 Rat cmp) (d + 1)) :
    List (HyperCert 0)

theorem gosper?_check {r c} (h : gosper? r = some c) :
    checkGosper c = true ∧ c.r = r
theorem zeilberger?_check {rk rn mo c} (h : zeilberger? rk rn mo = .ok c) :
    checkZeilberger c = true ∧ c.rk = rk ∧ c.rn = rn ∧ c.d ≤ mo
theorem hyperSolve_mem_check {d c h} (hmem : h ∈ hyperSolve d c) :
    checkHyper h = true ∧ h.d = d ∧ h.c = c

inductive ZeilbergerStop | orderExhausted
structure ZeilbergerFailure where
  stop     : ZeilbergerStop
  maxOrder : Nat
```

The searches are deterministic; there is no `Rand` and no resumable
state, unlike the randomized searches in hex-primality. Failure means
exhaustion of an explicit bound, and the bound is in the failure value.

**Gosper-Petkovšek normal form.** Given the reduced ratio `p/q` (this
is where hex-poly's field gcd runs), write `p/q = Z · (a/b) · (c⁺/c)`
with `b` and `c` monic, `Z` a constant, and the three coprimality
invariants of the full normal form: `gcd(a(k), b(k+j)) = 1` for every
natural `j`, `gcd(a(k), c(k)) = 1`, and `gcd(b(k), c(k+1)) = 1`. The
shift-coprimality invariant is what the degree bound needs; the other
two are what Hyper's divisor argument needs, and computing them is two
more gcds. The candidate `j`s form the dispersion set: the nonnegative
integer roots of `Res_k(a(k), b(k+j))`, a resultant taken over the
coefficient ring `DensePoly Rat` through hex-resultant, or by
evaluation and interpolation if that is faster; the choice is
unobservable. Integer roots are extracted by the rational root theorem
with bounded trial division of the trailing coefficient, with a scan up
to the Cauchy bound as fallback. An integer root missed here costs
search completeness, never soundness, so no factorization dependency is
taken for it. The peeling loop is the standard one, A=B §5.3.

**Degree bound and linear solve.** Solve `a(k) x(k+1) − b(k−1) x(k) =
c(k)` for polynomial `x` by the classical case analysis (A=B §5.4).
Writing `b⁻(k) = b(k−1)`: if `deg a ≠ deg b⁻` or `lc a ≠ lc b⁻`, then
`deg x = deg c − max(deg a, deg b⁻)`. Otherwise, with
`ℓ = deg a = deg b⁻`, `λ = lc a`, and `A`, `B` the coefficients of
`k^(ℓ−1)` in `a` and `b⁻`, the candidates are `deg c − ℓ + 1` and
`(B − A)/λ`, the second admitted only when it is a nonnegative
integer, and `deg x` is the maximum of the admitted candidates. Then
undetermined coefficients: a linear system over `ℚ` solved by
hex-row-reduce at `Matrix Rat`. The output is assembled into
`y = u/v = (b⁻/c) · x` and checked.

**Parameters in the search.** The two paragraphs above are stated
over `DensePoly Rat`, and with symbolic parameters they do not apply
as written: gcd, dispersion, and degree bounds would live over
`ℚ(w)[k]`, a coefficient field none of the listed dependencies
provides. The search does not build that field. Instead it
**specializes and lifts**: substitute random integers for the
parameters, run the parameter-free normal form and degree analysis at
one or more specializations to obtain the certificate's *shape* (the
dispersion set, `deg x`, and for Zeilberger the order `d`), then
solve for the certificate's coefficients symbolically, as the
already-specified fraction-free elimination over `MvPoly` in which
the parameters are just variables. An unlucky specialization (one on
the parameter subvariety where a degree drops) produces a candidate
the checker rejects, and the search retries with fresh points; as
everywhere in this section, that costs retries, never soundness. This
is the reason the searches can serve the symbolic Vandermonde example
with no rational-function-field dependency.

**The Zeilberger loop.** For `d = 0, 1, …, maxOrder`: run parametrized
Gosper on `t_d(k) = ∑ⱼ aⱼ F(n+j, k)` with the `aⱼ` coefficients
unknown. The unknowns (the `x` coefficients and the `aⱼ`) enter the
Gosper equation linearly over the field `ℚ(n, parameters)`. Rather
than build a lawful rational-function field to feed hex-row-reduce,
the solver clears to `MvPoly` and runs a small fraction-free Gaussian
elimination written in this library, untrusted and theorem-free. A
nontrivial solution with the `aⱼ` not all zero yields a candidate
certificate; the loop returns the first `d` whose candidate passes
`checkZeilberger`. The degree-bound case analysis over a parametrized
coefficient field is generically valid and can be wrong on a
parameter subvariety; the checker catches any resulting bad candidate,
so genericity failures cost retries, not soundness.

**Hyper.** `hyperSolve` accepts parameter-free input only (`s = 0`,
enforced by its signature): its enumeration factors the boundary
coefficients into irreducibles, and factorization over `ℚ(w)[n]` is
machinery no dependency provides and the specialize-and-lift device
cannot substitute for (the *set* of factor pairs, not just their
coefficients, changes with the parameters). The checker still accepts
parametrized Hyper certificates, so a hand-supplied symbolic
certificate replays; only the search is restricted, and a symbolic
Hyper search is recorded under open questions. Petkovšek's enumeration
for `∑ⱼ cⱼ(n) y(n+j) = 0`: normalise the coefficients to `ℤ[n]`; for each
monic factor `A` of `c₀(n)` and monic factor `B` of `c_d(n − d + 1)`,
obtained from hex-berlekamp-zassenhaus on the two integer-cleared
polynomials, and for each rational root `z` of the leading-coefficient
equation the pair induces, solve for a polynomial `C` with the same
degree-bounded undetermined-coefficients machinery; each success yields
the candidate ratio `r(n) = z · A(n)/B(n) · C(n+1)/C(n)`, cleared into
a `HyperCert` and checked. The enumeration is exponential in the number
of irreducible factors, which is intrinsic to the algorithm; the
factor-pair count is reported in diagnostics. Petkovšek's completeness
theorem is what justifies enumerating only this candidate shape, and
it is trusted informally, in exactly the way Sorenson-Webster's base
bound is trusted by hex-primality's search: it decides what to try and
never appears in a proof term.

hex-berlekamp-zassenhaus is a dependency only of this milestone, but
it is recorded in `libraries.yml` from the start, as the
hex-berlekamp-zassenhaus / hex-lll precedent requires: it is part of
the production graph, not an optional optimisation.

## From certificate to definite sum

The companion owns the pipeline that turns an accepted Zeilberger
certificate into `S(n) = C(n)`. Its steps, each a lemma with an
explicit hypothesis for anything unproved:

1. **Ratio facts.** The recognizer produces the multiplied-form ratio
   hypotheses for the concrete summand, from the ratio kit.
2. **Recurrence for `S`.** The natural-boundary corollary of
   `telescoped_of_checkZeilberger`, with the vanishing-past-support
   facts (from a `Nat.choose` cutoff) or the explicit correction sums,
   and the boundary terms `G n 0`, `G n (n+d+1)` evaluated by the same
   ratio kit; each is a single hypergeometric value, usually `0`.
3. **Recurrence for `C`.** If `C` is hypergeometric, its `n`-ratio is
   rational and "C satisfies the same recurrence" is one more
   cross-multiplied polynomial identity, checked by `checkHyper` with
   the certificate's own coefficients. A closed form that is a sum of
   several hypergeometric terms splits into one such check per term.
4. **The forcing term.** Prove the right side of the sum's telescoped
   recurrence (boundary values plus exceptional corrections) is zero
   for `n ≥ n₀`, or match it against the closed form's side; the
   shared-`f` form of `eq_of_recurrence` is what makes this a stated
   obligation rather than a silent assumption.
5. **Leading coefficient and thresholds.** `a_d(n) ≠ 0` for `n ≥ n₀`.
   Parameter-free, this is the Cauchy bound with `n₀` computed past
   it. With symbolic parameters the Cauchy bound is unavailable as an
   automatic device (a polynomial nonzero in `ℚ[n, w]` can specialize
   to zero, and its root bound can grow without bound in `w`), so the
   discharge is the affine-factor criterion when `a_d` factors that
   way, and otherwise the condition surfaces as a goal. The tactic
   never promises a parameter-uniform threshold it cannot compute.
6. **Initial values.** `S n = C n` for `n₀ ≤ n < n₀ + d`, and directly
   for the indices `0 ≤ n < n₀` the goal covers below the threshold.
   Parameter-free, each is an exact `ℚ` computation closed by `decide`
   or `norm_num`. With symbolic parameters each initial value is
   itself an identity in the parameters, typically one whose sum has
   collapsed (a `zchoose (x) 0` or empty-support instance); the
   tactic recurses on these smaller goals through the same machinery
   and surfaces any that do not collapse.
7. **Conclusion.** `eq_of_recurrence`.

A false identity submitted to this pipeline fails at step 6 with a
concrete counterexample index, which is the error message the tactic
reports.

## The front-end recognizer

Companion-side, `Qq`/`Lean.Meta`, in the reifier tradition of hex-rcf:
it produces certificate-shaped data *plus the proofs linking it to the
goal*, here the ratio hypotheses rather than a reflected sentence. Its
interpretation step builds the ℤ-indexed sequence
`F : Int → Int → ℚ` from the kit's atoms (`zchoose` in place of
`Nat.choose`, and so on) and proves it agrees pointwise with the
goal's summand on the summation range through the shim pack; the ratio
hypotheses and the semantics theorems are then about `F`, where every
identity is caseless.

**The closed class.** A summand is accepted when it is a product of
integer powers (positive or negative) of: rational constants and
numerals; `z ^ k` and `z ^ n` for rational `z`; polynomial factors
with integer-linear arguments; `Nat.factorial` of an integer-linear
argument with nonnegative `k`-slope; `Nat.choose` applied to
integer-linear arguments; and `ascPochhammer` at rational base with
integer-linear index. The grammar is deliberately syntactic and
extensible; each atom contributes its multiplied-form shift ratios in
`n` and `k` through one kit lemma per atom per direction.

**The ratio kit** is the heart of the companion and independent of
every algorithm. Its base object is the ℤ-extended binomial

```lean
/-- `zchoose x k = x (x−1) ⋯ (x−k+1) / k!` for `0 ≤ k`, and `0` for
`k < 0`. -/
def zchoose (x : ℚ) (k : ℤ) : ℚ
```

with the shim pack relating it to `Nat.choose` on the lattice,
`zchoose_natCast : 0 ≤ k → zchoose (n : ℚ) (k : ℤ) = n.choose k` for
naturals (valid including `k > n`, where both sides vanish), the one
place the case analysis happens. On top of it, ratio lemmas valid at
**every** integer pair with no side condition:

```lean
theorem zchoose_shiftK (x : ℚ) (k : ℤ) :
    ((k : ℚ) + 1) * zchoose x (k+1) = (x − k) * zchoose x k
theorem zchoose_shiftN (x : ℚ) (k : ℤ) :
    (x + 1 − k) * zchoose (x+1) k = (x + 1) * zchoose x k
```

Factorial atoms are rewritten by the kit into `zchoose` and Pochhammer
form; a reciprocal factorial extends by zero across negative
arguments, while a factorial in the numerator carries a nonnegativity
domain condition the recognizer discharges from the range bounds.
Inverted factors flip a ratio and add a pointwise nonvanishing
obligation for the inverted atom (`zchoose n k ≠ 0` needs
`0 ≤ k ≤ n`); the recognizer emits these as domain conditions and
discharges the standard ones (`choose` positive on `0 ≤ k ≤ n`,
factorial positive) from Mathlib.

**Support facts.** A `Nat.choose (n) (k)` factor with positive `k`-slope
supplies vanishing past `k = n` via `Nat.choose_eq_zero_of_lt`, which is
what feeds the natural-boundary corollary.

**What falls through**, as a `MetaM` failure naming the reason, so
downstream tactics can take over:

- A summand outside the class: `Nat.sub` inside a non-argument
  position, harmonic numbers, `2 ^ (k^2)`, anything analytic.
- Non-integer-linear arguments (`Nat.choose (k^2) k`): the ratio in
  `k` is not rational.
- A denominator atom whose nonvanishing the kit cannot discharge:
  the condition is surfaced as a leftover goal rather than refused,
  since the user may know it.
- Sums over ranges other than `Finset.range e`: `Finset.Icc` and
  shifted ranges are normalised by existing Mathlib lemmas where a
  simp set suffices, refused otherwise with the rewrite suggested.
- Goals in `ℕ`: handled, by casting through `Nat.cast_injective` into
  `ℚ` first; subtraction in the ℕ statement must be genuine (the cast
  produces a side goal when it cannot prove the subtrahend bounded).
- Goals in a field that is not characteristic zero: refused; the
  certificate identity is a `ℚ` fact and transports only along an
  injective cast.

## Tactic surface

```lean
example (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), (k * k.factorial : ℚ)
      = ((n+1).factorial : ℚ) − 1 := by gosper

example (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), (n.choose k : ℚ) = 2 ^ n := by zeilberger

example (m n r : ℕ) :
    ∑ k ∈ Finset.range (r+1), (m.choose k * n.choose (r−k) : ℚ)
      = ((m+n).choose r : ℚ) := by zeilberger

example (y : ℕ → ℚ) (h0 : y 0 = 1)
    (hrec : ∀ n, y (n+1) = (n+1 : ℚ) * y n) (n : ℕ) :
    y n = n.factorial := by hyper
```

`gosper` closes goals equating a `Finset.range` sum of a
hypergeometric term with a closed form whose difference telescopes;
`zeilberger` closes definite-sum identities through the full pipeline;
`hyper` closes goals of the form "a sequence constrained by a
recurrence and initial values equals a closed form". Configuration:
`zeilberger (maxOrder := 10)` raises the order cap;
`zeilberger (certificate := c)` replays a stored certificate and skips
the search, which is the hook the future-work "certificate
serialization and caching" item would use. Suggestion forms `gosper?`
and `zeilberger?` print the certificate and the closed form or
recurrence found, in the `exact?` tradition, and are how a user
discovers what a sum *is* rather than verifying a guess.

The three names name the algorithms. hex-rcf chose a theory-fragment
name on the ground that the isolation method could change beneath it;
here the algorithm *is* the user-recognisable name (every computer
algebra system documents these operations as Gosper and Zeilberger),
and the certificate language is specific to each. The open questions
record the alternative of one umbrella name.

The emitted proof term applies the semantics theorem to a reified
certificate literal with the checker discharged by `decide +kernel`,
so the kernel replays the polynomial identity and never the search,
exactly as `primality` and `factor_poly` behave.

## What an accepted certificate proves, and what it does not

An accepted `GosperCert` proves the telescoping identity for every
sequence satisfying its ratio hypothesis, on every range where the
pointwise side conditions hold. Distinct statements, none claimed:

- *Search completeness for Gosper.* `gosper? r = none` does not prove
  the term has no hypergeometric antidifference, although Gosper's
  theorem says a correct implementation would justify it. The tactic
  never uses a failed search as evidence.
- *Termination of the Zeilberger loop below the cap on proper input.*
  This is Zeilberger's theorem and is deliberately out of scope; the
  failure value names the exhausted bound instead.
- *Completeness of Hyper's enumeration.* `hyperSolve` returning `[]`
  proves no nonexistence; Petkovšek's theorem is trusted only as a
  search strategy.
- *Checker completeness* (every mathematically valid certificate is
  accepted): a regression-test property, not a theorem.
- *Minimality of the recurrence order.* The certificate proves its
  recurrence holds, not that no shorter one exists. A minimality
  claim would need a second witness, per the future-work preamble on
  what certificates establish.

## Kernel exposure

The replay closure is the three checkers and what they call: `MvPoly`
multiplication, addition, `subst` at the shift substitutions, the
equality test, and `Rat` arithmetic beneath them.
`HexMvPoly/KernelTests.lean` maintains kernel-reducibility of the
arithmetic; milestone 0 audits `subst` and the equality path
specifically and adds any missing `@[expose]` along them, with a
`decide +kernel` regression test in this library as the confirmation,
in the spirit of hex-primality's kernel-exposure amendment but expected
to be an audit rather than a development.

The searches, `ofRatio` excepted, appear in no proof term and are not
exposed. `ofRatio` is exposed because the `hyper` tactic evaluates
initial values inside `decide`.

The one measured risk is the size of the checker identity at higher
order: `Nⱼ` and `Qⱼ` are products of up to `d` shifted polynomials, so
the identity's degree grows linearly in `d` in each variable and the
kernel multiplies polynomials of that size. The "kernel replay" bench
family tracks it; if order-6 certificates for classical identities
replay in seconds, the design holds.

## Complexity

Operation counts; `M(δ, s)` is the cost of multiplying `(s + 2)`-variate
polynomials of degree `δ`, `d` the recurrence order, `δ` the largest
certificate degree.

| operation | cost | note |
|---|---|---|
| `checkGosper` | `O(1)` products at `M(δ, s)` | five multiplications and one equality |
| `checkZeilberger` | `O(d)` products at `M(δ + d, s)` | building `Nⱼ`, `Qⱼ` dominates |
| `checkHyper` | `O(d)` products at `M(δ + d, s)` | |
| `sumIco` replay | `O(b − a)` evaluations | per-point `evalAt` |
| GP normal form | one resultant + `O(|J|)` gcds | untrusted |
| `gosper?` | linear solve, `O(δ³)` field ops | hex-row-reduce at `Rat` |
| `zeilberger?` | `∑_{d' ≤ d}` parametrized solves | coefficient growth in `n` is the practical bottleneck |
| `hyperSolve` | `O(2^{f₀} · 2^{f_d})` inner solves | `fᵢ` = irreducible factor counts; intrinsic |

The honest caveat from hex-primality applies: these are operation
counts over exact rationals whose numerators and denominators grow, and
coefficient growth, not operation count, is what the benchmarks must
watch, particularly in the fraction-free elimination inside
`zeilberger?`.

## Conformance

Per [SPEC/testing.md](../testing.md). A driver at
`conformance/HexSummation/EmitFixtures.lean` exposed as
`lean_exe hexsummation_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexSummation/summation.jsonl`, oracles under
`scripts/oracle/`, and tuples appended to `ORACLES` in
`scripts/ci/run_oracles.sh`.

Fixture kinds: `gosper_cert`, `zeilberger_cert`, `hyper_cert` (a
certificate and whether the checker accepts), and `identity` (a term
description, a range, and exact `ℚ` values of the sum at concrete
arguments).

Cases that must be present:

- The A=B corpus classics as accepted certificates: the binomial
  theorem row sum, Vandermonde (with symbolic parameters),
  Saalschütz, Dixon, `∑ k·k!`, `∑ 1/(k(k+1))` (a rational, not just
  hypergeometric, case), and the Apéry-number recurrence as a
  `zeilberger_cert` of order 2.
- Gosper failures that must stay failures: `t(k) = 1/k` summed as the
  harmonic numbers (no rational certificate exists; the fixture
  records `gosper? = none` as the expected outcome, a regression
  test on the search, not a nonexistence proof).
- **Rejected certificates of each kind, hand-built**: a tampered `u`;
  a `v` with a dropped factor; a Zeilberger certificate whose `aⱼ`
  mention the summation variable; a zero top coefficient `a_d` (a
  padded order); a Gosper certificate mentioning variable `0`; a Hyper
  certificate mentioning variable `1` or with a zero boundary
  coefficient; a `DenWitness` whose factored product disagrees with
  the stored denominator. No oracle
  produces negative cases, so these are constructed by hand, as
  hex-primality's rejected-certificate fixtures are.
- Boundary-behaviour identities: a summand vanishing at interior
  points of the range (binomial with an upper cutoff inside the
  range), the empty range `b ≤ a`, a two-sided range crossing zero,
  and a sum whose closed form has a removable exceptional index at
  small `n`, pinning the `n₀` / initial-values machinery.
- `identity` fixtures evaluating each accepted certificate's sum
  exactly at `n ≤ 30` including every exceptional index.

**Oracle choice.** Two oracles. `scripts/oracle/summation_sympy.py`
uses sympy's `sympy.concrete.gosper` (`gosper_normal`,
`gosper_term`) to cross-check the Gosper families: sympy is **not
currently installed** in CI (`.github/workflows/ci.yml` installs
`python-flint`, `cypari2`, and `conway-polynomials`), so this oracle
carries an amendment to the existing install step and to the
`HEX_REQUIRE_ORACLES` preflight, per
[SPEC/testing.md § Adding a new oracle](../testing.md); it extends the
script of the existing single job and adds no workflow or matrix
entry. `scripts/oracle/summation_replay.py` replays every `identity`
fixture numerically through cypari2 (already installed), evaluating
the summand and closed form in exact arithmetic at every fixture
argument; for the certificate fixtures it independently re-derives the
cross-multiplied identity at random rational points. sympy has no
Zeilberger implementation, and Maxima's `zeilberger` package is the
nearest independent one; it is a manual cross-check during
development, not a CI oracle, and the benchmarking section lists it as
an informational comparator only.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), drivers at
`bench/HexSummation/Bench.lean`, Mathlib-free, native and kernel
suites both, because the kernel-side replay cost is a design risk
this SPEC explicitly carries.

Families:

- **Checker replay, native**: the three checkers across the fixture
  corpus, reported by certificate order and degree.
- **Kernel replay**: `decide +kernel` on the same checker calls, at
  orders 1 through 6. This family answers the kernel-exposure risk;
  its budget is the "few minutes" rule every committed-artifact
  family in this repository uses.
- **Gosper search**: `gosper?` across the A=B §5 examples, plus the
  dispersion-heavy family `t(k+N)/t(k)` at growing `N`, which is the
  input that stresses the integer-root scan.
- **Zeilberger search**: Vandermonde, Saalschütz, Dixon, Apéry, at
  their natural orders, plus one family with growing parameter count,
  which is what stresses the fraction-free elimination.
- **Hyper**: recurrences with reducible leading and trailing
  coefficients at growing factor counts, plus the no-solution
  Fibonacci case (constant coefficients, irrational ratio), which
  must fail fast.

**Comparators.** sympy's `gosper_term` and Maxima's `Zeilberger` are
both **informational**: they are interpreted implementations answering
in a different runtime with different startup costs, and neither
checks anything, so a required ratio would compare a prover-plus-
checker against a search alone. The comparison a reader wants, and
the one recorded, is wall-clock on the shared corpus.

## The Mathlib layer

The companion depends on hex-summation and Mathlib alone; the
certificates' polynomial identities are checked on the Hex side and
never transported to `Polynomial` or `MvPolynomial`, so no
`*-poly-mathlib` equivalence is needed. Its content:

- `sumIco_cast`: `((sumIco f a b : ℚ) : K) = ∑ k ∈ Finset.Ico a b, (f k : K)`
  for `[DivisionRing K] [CharZero K]`, the `Finset.range` transfer
  (`∑ k ∈ Finset.range m, g k = sumIco F 0 m` given pointwise
  agreement of `g` and `F` on `[0, m)`), and the statements of the
  main theorems over such `K`, obtained by casting the `ℚ` identity.
  Goals over `ℝ` and `ℂ` cost one cast lemma, not a second proof.
- The ratio kit and the recognizer, as above.
- The definite-sum pipeline lemmas, as above.
- The three tactics and the two suggestion forms.

Two Mathlib-facing notes, both to verify at implementation time
against the Mathlib revision then current: `Ring.choose`
(`Mathlib.RingTheory.Binomial`) overlaps `zchoose` where its lower
index (a natural) is defined, and whether `zchoose` is defined on top
of it or standalone with a compatibility lemma is an implementation
choice, not an interface one; and no `norm_num` extension is
registered, because a summation identity is not a numeral fact, so
there is no analogue of hex-primality's `norm_num` interoperation
here.

## Milestones

0. **Audit.** Kernel-reducibility of the checker closure (`MvPoly`
   `mul`, `add`, `subst`, equality at `Rat`), with a
   `decide +kernel` regression test on a small hand certificate; the
   `ExactDivLaws` instance for `DensePoly Rat` coefficients that the
   dispersion resultant instantiates, added to hex-poly or
   hex-resultant if absent. Expected to be small; everything below
   assumes it.

1. **Gosper certificates.** `Ratio`, `shiftK`/`shiftN`, `GosperCert`,
   `checkGosper`, `sumIco`, `evalAt`, `sumIco_eq_of_checkGosper` and
   its exceptional-edge variant, the Cauchy bound, `AffineFactor`,
   and `DenWitness` with `checkDenWitness`, and hand-written
   certificate fixtures for `∑ k·k!` and `∑ 1/(k(k+1))`. The
   checker-first deliverable the future-work entry asks for.

2. **Zeilberger certificates.** `ZeilbergerCert`, `checkZeilberger`,
   the pointwise and summed telescoping theorems, the
   natural-boundary and explicit-correction corollaries,
   `eq_of_recurrence`, and a hand-written Vandermonde certificate
   with symbolic parameters as the fixture that pins the parameter
   design.

3. **The searches.** GP normal form with its three invariants,
   dispersion, degree bounds, the `Rat` linear solve, `gosper?`; the
   fraction-free parametrized elimination, the specialize-and-lift
   parameter handling, and the `zeilberger?` order loop;
   checker-approved output with the by-construction postcondition
   theorems; the
   conformance drivers and both oracles, including the CI install
   amendment for sympy.

4. **The companion pipeline and tactics.** `sumIco_cast`, the
   `Finset.range` transfer, and the `K`-statements; `zchoose` with
   its shim pack; the ratio kit; the recognizer with its
   fall-through list, the definite-sum pipeline, `gosper`,
   `zeilberger`, and the suggestion forms. The library's user-visible
   payoff lands here.

5. **Hyper.** `HyperCert`, `checkHyper`, `ofRatio` and its theorems,
   the parameter-free `hyperSolve` over hex-berlekamp-zassenhaus
   factor pairs, the `hyper` tactic, and the Hyper conformance and
   bench families.

## File organisation

```
HexSummation/
  Ratio.lean        -- Ratio, shiftK/shiftN, composition
  GosperCert.lean   -- GosperCert, checkGosper
  ZeilbergerCert.lean -- ZeilbergerCert, checkZeilberger, Nⱼ/Qⱼ assembly
  HyperCert.lean    -- HyperCert, checkHyper
  Telescope.lean    -- sumIco, evalAt, Gosper soundness
  Recurrence.lean   -- summed telescoping, corollaries, eq_of_recurrence
  Bound.lean        -- cauchyBound, AffineFactor, DenWitness
  OfRatio.lean      -- ofRatio and its theorems
  Normal.lean       -- GP normal form, dispersion (search)
  Solve.lean        -- degree bounds, undetermined coefficients,
                    -- fraction-free parametrized elimination (search)
  Search.lean       -- gosper?, zeilberger?, postcondition theorems
  HyperSearch.lean  -- hyperSolve (search)
HexSummation.lean
HexSummationMathlib/
  Semantics.lean    -- sumIco_cast, range transfer, K-statements
  RatioKit.lean     -- zchoose and its shim pack, ratio lemmas
  Recognize.lean    -- the term-class recognizer
  DefiniteSum.lean  -- the certificate-to-identity pipeline
  Gosper.lean       -- the gosper tactic and gosper?
  Zeilberger.lean   -- the zeilberger tactic and zeilberger?
  Hyper.lean        -- the hyper tactic
HexSummationMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexSummation:
    deps: [HexPoly, HexMvPoly, HexResultant, HexMatrix, HexRowReduce,
           HexBerlekampZassenhaus, HexBasic]
    mathlib: false
    done_through: 0
    status: draft
  HexSummationMathlib:
    deps: [HexSummation]
    mathlib: true
    done_through: 0
    status: draft
```

## Open questions

- **An executable rational-function field.** The fraction-free
  elimination inside `zeilberger?` exists because no lawful
  `RatFunc`-style field over `DensePoly` exists to hand to
  hex-row-reduce. Such a type (reduced fraction, monic denominator,
  `Lean.Grind.Field` instance) is the "rational function
  normalisation" of the future-work entry, and its natural home would
  be a small library over hex-poly. It is not built here because no
  verified statement needs it; the question is whether a second
  consumer appears before this library's search would be simplified
  by it.
- **`maxOrder` default.** Set to 6 provisionally; the Zeilberger
  bench family measures where real identities live (the classical
  corpus needs at most 3) and the default follows the measurement.
- **One umbrella tactic.** Whether `gosper` / `zeilberger` / `hyper`
  should be fronted by a single name that dispatches on goal shape,
  in the way `rcf` names the fragment rather than the method. The
  three-name surface ships first because the failure diagnostics are
  method-specific.
- **Certificate caching.** `zeilberger (certificate := c)` is the
  replay hook; whether stored certificates adopt the shared envelope
  of the future-work "certificate serialization and caching" item is
  decided by that item, and this library is a natural second case
  study after hex-conway.
- **Where the ℤ-interval sum kit lives.** `sumIco` and its splitting
  and reindexing lemmas are the Mathlib-free counterpart of apery's
  bespoke `bigopz` library. They start here because this library is
  their only consumer; a second Mathlib-free consumer of ℤ-interval
  sums would argue for moving them down to hex-basic.
- **A symbolic Hyper search.** `hyperSolve` is parameter-free because
  its enumeration needs factorization over `ℚ(w)[n]`. If parametrized
  recurrence solving turns out to have consumers, the options are a
  factorization over rational-function coefficient fields (a
  substantial library) or a partial search over parameter-free factor
  candidates; the checker already accepts symbolic certificates
  either way.
- **The holonomic extension.** Closure properties for
  P-recursive sequences would subsume `eq_of_recurrence` and give
  Zeilberger a home as one closure instance; the future-work entry's
  deferral stands until the certificate checkers have carried real
  identities for a while.

## References

- M. Petkovšek, H. Wilf, D. Zeilberger, *A=B*, A K Peters, 1996.
  Chapters 5 and 6 are the algorithm sources for the search; the
  degree-bound case analysis is §5.4 and the GP normal form §5.3.
- R. W. Gosper, Jr., "Decision procedure for indefinite hypergeometric
  summation", PNAS 75 (1978).
- D. Zeilberger, "A fast algorithm for proving terminating
  hypergeometric identities", Discrete Math. 80 (1990); "The method of
  creative telescoping", J. Symbolic Comput. 11 (1991).
- M. Petkovšek, "Hypergeometric solutions of linear recurrences with
  polynomial coefficients", J. Symbolic Comput. 14 (1992).
- W. Koepf, *Hypergeometric Summation*, 2nd ed., Springer, 2014. The
  parametrized-Gosper formulation of Zeilberger's loop used above.
- F. Chyzak, A. Mahboubi, T. Sibut-Pinote, E. Tassi, "A
  Computer-Algebra-Based Formal Proof of the Irrationality of ζ(3)",
  ITP 2014; journal version at https://arxiv.org/abs/1912.06611;
  sources at https://github.com/rocq-community/apery. The
  `sound_telescoping` master lemma and the annotated-recurrence
  representation adopted above.
- J. Harrison, "Formal Proofs of Hypergeometric Sums", J. Automated
  Reasoning 55 (2015), https://www.cl.cam.ac.uk/~jrh13/papers/wz.html.
  The Γ-and-limits alternative not taken, and the mid-range
  singularity warning that is.
- M. Eberl, "Linear Recurrences", Archive of Formal Proofs,
  https://www.isa-afp.org/entries/Linear_Recurrences.html.
- Liu, Zhang, Zhi, a Lean 4 proof of the irrationality of ζ(3) by
  Beukers integrals, https://arxiv.org/abs/2503.07625; and the
  WZ-guided proof-sketching pipeline of
  https://arxiv.org/abs/2605.04472. The demand-side evidence cited
  under "Prior art".
