# hex-rational-fn

Canonical univariate rational functions over an effective field, implemented
as coprime dense polynomials with a monic denominator. The computational
library is Mathlib-free. Its
[Mathlib companion](../../HexRationalFnMathlib/SPEC/hex-rational-fn-mathlib.md) identifies this representation
with `RatFunc K`.

## Scope and dependencies

The first version provides normalization, exact equality, field arithmetic,
natural powers, checked inversion and division, evaluation at a field element,
formal differentiation, polynomial-part decomposition, and certificate replay.
It works over any `K` with `[Lean.Grind.Field K] [DecidableEq K]`. Rational
coefficients and prime-field coefficients are the initial conformance domains.
There is no characteristic-zero hypothesis on the representation or arithmetic.

The immediate dependencies are `HexPoly` and `HexPolyFast`:

- `Hex.DensePoly` supplies canonical coefficient arrays, arithmetic,
  evaluation and differentiation. `HexPoly.Field` supplies lawful division,
  gcd and extended gcd over the lightweight field interface.
- `HexPolyFast` supplies `MulPlan`, fast multiplication, division and half-gcd.
  Algorithms with significant polynomial products accept an explicit plan.
  The plan is an argument to an operation, not part of a rational function's
  identity. There is no second polynomial-operations typeclass.

`HexRationalFnMathlib` additionally depends on `HexPolyMathlib`. Neither
library depends on multivariate gcd, polynomial factorization, number fields,
or the planned generic finite-field interface. Instances for a concrete field
are supplied by the library that defines that field. A downstream function
field library may use `RationalFn K` as its coefficient field without importing
expression tactics.

Partial fractions, expression reification, `Together` and `cancel` tactics,
multivariate fractions, composition, coefficient-field maps, series expansions,
pole orders and algebraic extensions of `K(x)` are outside this first version.
They can use the representation and theorems here. In particular, a later
expression tactic must track the denominators of its original expression.

## Representation and equality

The namespace is `Hex.RationalFn`, and the type is `Hex.RationalFn K`.
The following is the required data and invariant shape. Names in subsequent
API tables are required declarations, with implicit field parameters omitted.

```lean
namespace Hex

universe u

structure RationalFn (K : Type u) [Lean.Grind.Field K] [DecidableEq K] where
  num : DensePoly K
  den : DensePoly K
  monic_den : den.Monic
  coprime : DensePoly.monicize (DensePoly.gcd num den) = 1

end Hex
```

The invariant uses the monic associate of the gcd explicitly. It does not
assume that the existing gcd's chosen unit normalization is monic. Monicity
implies `den ≠ 0`. Coprimality and monicity imply that `num = 0` forces
`den = 1`. The unique zero is therefore `(0, 1)` without a second zero tag.
Proof fields are propositions and have no runtime payload. Bézout coefficients,
cached gcds, execution plans and expression domains are not stored in this type.

Prove `ext` from equality of numerators and denominators, and `eq_iff`:

```text
f = g  ↔  f.num * g.den = g.num * f.den.
```

The reverse implication is the substantive uniqueness theorem: coprimality
gives mutual denominator divisibility, monicity makes the denominators equal,
and cancellation identifies the numerators. Establish this in the
computational library, rather than requiring a Mathlib quotient to prove its
field laws. `DecidableEq` compares the two canonical coefficient arrays. A
lawful `BEq` uses the same comparison and does not multiply polynomials.
`num_eq_zero` states `f.num = 0 ↔ f = 0`.

Equality is equality in `K(x)`. In a finite field, different polynomials can
agree at every field element: `X^p - X` and zero do so over `F_p`. Evaluation
samples, including exhaustive samples over a finite field, are not an equality
decision for this type.

## Construction and normalization

| Declaration | Contract |
| --- | --- |
| `normalizeWith plan p q hq` | Canonical representative of `p/q`, requiring `hq : q ≠ 0`. |
| `normalize p q hq` | The same operation with the default multiplication plan. |
| `ofFraction? p q` | `none` exactly when `q = 0`, otherwise the normalized fraction. |
| `ofPoly p` | Numerator `p`, denominator `1`. |
| `C a`, `X` | Constants and the polynomial indeterminate through `ofPoly`. |

For `p = 0`, normalization returns zero. Otherwise compute
`d = monicize (gcdWith plan p q)`, divide both inputs exactly by `d`,
and call the quotients `a` and `b`. Set `c = b.leadingCoeff` and return
`(scale c⁻¹ a, scale c⁻¹ b)`. Prove that `d` and `c` are nonzero, both
divisions have zero remainder, and the resulting pair satisfies the invariant.
Use `divModWith` for division and its proved agreement with polynomial division.
Internal exact divisions carry divisibility proofs. A failed arithmetic check
must not silently substitute zero or the original input.

`normalize_spec` proves the invariant and the fraction equation
`result.num * q = p * result.den`. `normalize_unique` says that any canonical
pair satisfying this equation is the result. Consequences include idempotence
on stored pairs, independence of the nonzero-denominator proof, equality of
the results for all lawful plans, and invariance under multiplying both inputs
by the same nonzero polynomial. Constructor rejection includes `0/0`.

The default plan is `DensePoly.karatsubaPlan` with a named positive cutoff,
selected from the crossover experiment below. Small products use that plan's
schoolbook base case. No fixed field, roots of unity or machine-word modulus
is required. Explicit `With` operations let consumers supply more specialized
lawful plans without installing competing field instances.

There is no unchecked pair constructor accepting a zero denominator. Field
division by zero, defined below, is a different operation with a deliberate
totalized-field meaning.

## Arithmetic algorithms

Write `f = a/b`, `g = c/d` for canonical inputs. Every operation returns
canonical data and proves the indicated fraction identity. Use fast gcd,
division and multiplication with the supplied plan. Do not multiply full
numerators and denominators and then run a full normalization when the
following cancellation algorithm avoids those intermediate products.

### Addition and subtraction

Compute the monic gcd `h` of `b` and `d`, then exact quotients `b₁ = b/h`
and `d₁ = d/h`. Form `t = a*d₁ + c*b₁`. If `t = 0`, return zero.
Otherwise compute the monic gcd `e` of `t` and `h`, and return

```text
num = t/e
den = b₁ * (d/e).
```

The proof shows that `t` is coprime to both `b₁` and `d₁`. Thus every
remaining common factor divides `h`, and cancelling `e` suffices. Products
and exact quotients of the monic denominators remain monic. Subtraction uses
the same algorithm with `t = a*d₁ - c*b₁`. Negation only negates `num`.
Zero operands, denominator one and equal denominators have direct branches
whose results agree with these formulas.

### Multiplication and division

Return zero immediately if either multiplicand is zero. Otherwise compute
the monic gcds `u = gcd(a,d)` and `v = gcd(c,b)`, and form

```text
num = (a/u) * (c/v)
den = (b/v) * (d/u).
```

Here and below a displayed gcd in an algorithm means its monic associate.
The proof establishes coprimality of the resulting pair before constructing
the value. Since `b` and `d` are monic, the output denominator is monic.

For nonzero `f`, inversion swaps the two polynomials and scales both by
`a.leadingCoeff⁻¹`. Their existing coprimality proof transfers, so inversion
does not recompute a gcd. Define `inv 0 = 0`, and division by multiplication
with this inverse. Natural powers use binary powering of the numerator and
denominator separately and transport coprimality under powers. They do not
run a gcd at every multiplication. Set `f^0 = 1`, including `0^0`.

Expose `addWith`, `subWith`, `mulWith`, `divWith`, and `powWith` and prove
their plan independence. The usual arithmetic instances use the default plan.
Provide `inv? f : Option (RationalFn K)` and `div? f g` as checked wrappers:
the former rejects exactly zero, the latter rejects exactly a zero divisor.
On success they agree with total inversion and division. `div? 0 0` is `none`.

### Field laws

Provide a lawful `Lean.Grind.Field (RationalFn K)` and `DecidableEq`, including
compatible natural and integer casts. Derive the field laws from the fraction
equations and `eq_iff`. Prove that `ofPoly` is injective and preserves zero,
one, addition and multiplication. Constants preserve the coefficient field's
arithmetic, including total inversion.

In this field, `f / 0 = 0` and `0⁻¹ = 0`. This supports generic polynomial
Euclidean arithmetic over `K(x)` and agrees with Lean's field convention.
It is not a statement that a rational function has a value at a pole. The
partial evaluation API below never returns a field value for a pole.

## Evaluation and its domain

`eval? f a : Option K` evaluates the canonical denominator by Horner's rule.
It returns `none` if this is zero and otherwise returns the numerator value
divided by the denominator value. Define `Regular f a` to mean
`f.den.eval a ≠ 0`, and prove:

```text
eval? f a = some v  ↔  Regular f a ∧ v = f.num.eval a / f.den.eval a
eval? f a = none    ↔  ¬ Regular f a.
```

If a raw denominator `q` is nonzero at `a`, `normalize p q hq` is regular
there and evaluates to `p.eval a / q.eval a`. The converse is false because
normalization removes removable singularities. For example, over `Rat`,
normalizing `(X²-1)/(X-1)` gives `X+1`, which evaluates to `2` at `1`.
The original expression still has a zero denominator there. This library
does not preserve that expression's domain of definition.

For two regular operands, prove regularity and the expected values for
addition, subtraction and multiplication. For inversion and division also
require the value of the inverted operand to be nonzero. These implications
are one-way: `1/X + (-1/X)` becomes zero and is regular at zero, even though
neither summand is. There is no unconditional homomorphism obtained by
evaluating all of `K(x)` at a field element.

## Differentiation and polynomial part

`derivativeWith plan f` normalizes
`(a' * b - a * b') / b²`, with `derivative` as the default-plan wrapper.
The prime denotes the polynomial derivative. Prove the quotient formula,
constant and indeterminate rules, additivity and the Leibniz rule in the
rational-function field. Cancellation may reduce the denominator degree.
These are formal derivatives in every characteristic. Do not infer that a
zero derivative means a constant in positive characteristic.

`splitWith plan f : DensePoly K × RationalFn K` divides `a` by `b`, obtaining
`a = q*b + r`, and returns `(q, r/b)`. If `r = 0`, the second component is
zero. Otherwise `gcd(r,b)` is a unit by coprimality of `a,b`, so the stored
pair `(r,b)` is already canonical. `split` uses the default plan.

Define `Proper f` by `f.num = 0 ∨ f.num.size < f.den.size`. `split_spec`
proves `f = ofPoly q + s` and `Proper s`. `split_unique` proves uniqueness
among all such polynomial/proper-fraction decompositions. This is polynomial
division, not partial fractions. `toPoly? f` returns `some f.num` exactly
when `f.den = 1`, and otherwise returns `none`. Prove that it succeeds
exactly on the image of `ofPoly`.

## Certificates and kernel replay

Ordinary executable arithmetic uses its proved algorithms and does not carry
certificates in every value. A separate certificate permits replay of a
proposed normalization without reducing a Euclidean search in the kernel.

`Cert K` contains four raw dense polynomials `num`, `den`, `s`, `t`.
`check p q cert : Bool` checks precisely:

```text
q ≠ 0
cert.den.leadingCoeff = 1
cert.num * q = p * cert.den
cert.s * cert.num + cert.t * cert.den = 1.
```

The last equality proves coprimality. Checking only the cross-product
equation would not prove that the answer is canonical. `check_sound`
constructs the canonical value from accepted data and proves that it equals
`normalize p q hq`. `ofCert? p q cert` returns this value exactly when the
check succeeds. No proof field from a supplied certificate is trusted.

`certifyWith plan p q hq` normalizes and computes Bézout coefficients for
the canonical pair using polynomial extended gcd, rescaling a nonzero
constant gcd to one. Prove `certify_checks` for every `q ≠ 0`. Certificate
fields need not be canonical beyond `num` and `den`, and distinct Bézout
witnesses do not change the resulting rational function. In the zero case
`num = 0`, `den = 1`, `s = 0`, `t = 1` is a valid certificate.

Expose the checker and its polynomial equality operations for kernel replay.
Proof-producing consumers run certificate generation as untrusted compiled
search, then apply `check_sound` to a kernel-checked Boolean equality on
literals. They must budget certificate generation, payload size and replay
separately. `native_decide`, new axioms and new trusted extern boundaries are
not allowed. This SPEC introduces no external candidate provider or shared
certificate cache. An external oracle is a testing tool, not part of execution.

## Complexity and benchmarking

Use coefficient-array lengths to measure zero and constant polynomials
uniformly. Let `N ≥ 1` bound the lengths of the operands' numerators and
denominators. Let `M(N)`, `D(N)` and `G(N)` denote the multiplication,
division and gcd costs of the selected polynomial algorithms. Constants in
arguments, such as `2N`, account for intermediate products.

| Operation | Polynomial work, excluding coefficient bit costs |
| --- | --- |
| Normalization | One gcd, two exact divisions, linear scaling. |
| Addition/subtraction | At most two gcds, a constant number of exact divisions and products. |
| Multiplication/division | At most two gcds, four exact divisions and two products, plus linear inversion scaling for division. |
| Inversion/negation | Linear coefficient work, no gcd. |
| Equality | At most linear coefficient comparisons, no gcd or multiplication. |
| Evaluation | Linear field operations by two Horner evaluations. |
| Derivative | Polynomial differentiation and a constant number of products, followed by normalization. |
| Polynomial part | One polynomial division and canonical construction without another gcd. |
| Natural power | `O(log(e+1))` polynomial products at growing lengths, output length up to `e*(N-1)+1` for `e > 0`. |
| Certificate check | A constant number of products and coefficient comparisons, in the certificate/input lengths. |

With suitable regularity bounds on `M`, fast division costs `O(M(N))` and
half-gcd costs `O(M(N) log(N+1))` field operations. These are dependency
algorithm bounds, not unconditional runtime claims for arbitrary `MulPlan`
values. Benchmark both balanced and unbalanced degrees. Over `Rat`, report
coefficient bit lengths and growth independently from degree. Unit-cost field
operation counts do not establish a wallclock model for growing rationals.

Required input families in `bench/HexRationalFn/Bench.lean` are:

1. **normalization**: prescribed common-factor degree, nonmonic denominators,
   and coprime residual factors. Vary input degree and cancellation separately.
2. **addition**: coprime, equal and partially shared denominators. Include
   cancellation against their gcd and total cancellation to zero.
3. **multiplication**: coprime pairs and substantial cross-cancellation. Compare
   with multiply-then-normalize on exactly the same canonical operands.
4. **coefficient-height**: fixed dense rational shapes with increasing numerator
   and denominator bit lengths, recording intermediate as well as final sizes.
5. **queries**: equal inputs and inputs differing in the last compared
   coefficient, evaluation at regular points and poles, and inversion.
6. **calculus**: derivatives with and without cancellation, polynomial-part
   division with nonzero remainder, and natural powers measured by output size.
7. **certificate-replay**: generation and replay timed separately, including
   rejected certificates. Vary witness size rather than only input degree.

Measure the schoolbook/Karatsuba crossover for the default plan. The competing
normalization route in multiplication must include the same canonical output
requirement. Publish its crossover and intermediate-degree savings, not a
promise that cancellation is faster on every small coprime input.

The required external throughput comparator is
[FLINT `fmpz_poly_q`](https://flintlib.org/doc/fmpz_poly_q.html), specifically
`fmpz_poly_q_canonicalise`, `add`, `sub`, `mul`, `div`, `inv`, `pow`,
`derivative`, `equal`, and `evaluate_fmpq` (see the
[public header](https://github.com/flintlib/flint/blob/main/src/fmpz_poly_q.h)).
Use a persistent driver linked to
FLINT, with the `fmpz_poly_q_` prefix on each function name. It is
**informational**: FLINT stores integer numerator/denominator pairs with its
own scalar normalization, whereas this library stores monic-denominator
polynomials over `Rat`. Convert inputs and outputs outside the timed operation
and compare the resulting canonical `Rat` coefficient arrays. Record both
representation sizes. FLINT's zero-input rejection conventions must be
adapted explicitly rather than equated with total field division.

The comparator covers the rational-coefficient arithmetic, equality and
evaluation surfaces. Polynomial-part splitting is a **structural-layer**
comparison delegated to `HexPolyFast` division evidence. Certificate production
and replay have **no-comparable-surface-in-named-comparator**: FLINT does not
expose this Bézout normalization certificate protocol. Measure those native
operations and kernel replay independently. Prime-field plan comparisons use
the same generic implementation and internal plan-agreement checks.

Follow the ordered complexity modes in [benchmarking](../../SPEC/benchmarking.md).
Derive any model independently of timings. Preserve complete output checks,
record hardware and tool versions, keep Mathlib out of executable benches,
and extend the existing CI job and scheduled timing workflow.

### Performance evidence tracks

The compiled operations and the certificate-proof consumer are separate
measurement surfaces. Ordinary mathematical correspondence theorems are not
advertised proof-search operations.

| Surface | Track and targets |
| --- | --- |
| `normalizeWith`, `normalize`, `ofFraction?` | Compiled: `RationalFnFamilies.normalizeDegree`, `normalizeCancel`, `checkedFraction`; `RationalFnWorkloads.normalizeChain`, `heightNormalize`. |
| `ofPoly`, `C`, `X`, natural/integer casts, `toPoly?`, stored-pair projections | Compiled: `RationalFnWorkloads.constructors`, a bounded-degree, bounded-word constant-work family. |
| `addWith`, `subWith`, addition/subtraction instances | Compiled: `RationalFnFamilies.addCoprime`, `addShared`, `addCancel`, `addTotal`, `addEqual`, `subtract`; `RationalFnWorkloads.heightAdd`. |
| `mulWith`, `divWith`, multiplication/division instances, `div?` | Compiled: `RationalFnFamilies.multiply`, `cancelMultiply`, `divide`, `checkedDivide`; `RationalFnWorkloads.multiply`, `unbalanced`, `unbalancedSchoolbook`, `heightMultiply`. |
| Negation, inversion, `inv?` | Compiled: `RationalFnScaling.negate`; `RationalFnFamilies.inverse`, `checkedInverse` include nonmonic scaling. The monic `RationalFnScaling.inverse` is supplemental sharing/hash evidence. |
| `DecidableEq`, `BEq`, `eval?` | Compiled: `RationalFnScaling.equal`, `different`, `evaluate`, `evaluatePole`. |
| `derivativeWith`, `derivative` | Compiled: `RationalFnWorkloads.derivative`, `derivativeCancel`, `derivativePolynomial`, `heightDerivative`. |
| `splitWith`, `split` | Compiled: `RationalFnWorkloads.polynomialPart`, with a nonzero remainder and bounded short divisor. |
| `powWith`, natural powers | Compiled: `RationalFnWorkloads.square` varies base degree at exponent two; `power` varies exponent and output degree over the prime field. |
| `certifyWith`, executable `check`, executable `ofCert?` | Compiled: `RationalFnFamilies.generate`, `accept`; `RationalFnScaling.replay`, `reject`. |
| Kernel replay of literal certificate-check equalities | Proof: `bench/HexRationalFn/ProofProbe`, externally measured by `scripts/bench/rationalfn_kernel_replay.py`; no LeanBench timing is used. |

Default wrappers and their `With` variants execute the same algorithm with the
selected lawful plan. Fixed schoolbook/Karatsuba and cancelled/naive comparison
groups provide plan/route agreement; they are not the operation-coverage
models. The controlled degree families do not claim generic rational bit
complexity. The height families keep degrees fixed and use the published
quadratic coefficient-arithmetic upper bound; their named intermediate
cofactor and quotient-rule sizes are emitted with the matched FLINT fixtures.
The long Euclidean chain over `ZMod64 7` separately covers the generic half-gcd
phase without coupling degree to rational coefficient growth.

Each kernel probe has a five-second absolute fresh-module build budget, six
rotated reference/candidate samples, an import-only baseline, and cheap and
replay same-module noise controls. The accepted witnesses have degrees 5, 17,
and 65; the rejection probe changes the last checked Bezout identity. Literal
payloads are in a warm imported support module, so the reported build time is
certificate theorem elaboration and kernel replay, not certificate search or
payload generation. Standard logical axioms are recorded from `#print axioms`;
no additional axiom, native decision procedure, or trusted external checker is
introduced.

## Conformance

Create `conformance/HexRationalFn/{Conformance,EmitFixtures}.lean`,
`conformance-fixtures/HexRationalFn/rationalfn.jsonl`, and
`scripts/oracle/rationalfn_sympy.py`. The required independent oracle in the
existing `oracles` profile uses SymPy's polynomial rings and fraction fields
over `QQ` and `GF(p)`, through explicit domains, not expression simplification.
See [SymPy's domain reference](https://docs.sympy.org/latest/modules/polys/domainsref.html).
Normalize oracle outputs to coprime polynomials with a monic denominator
before comparing canonical coefficient arrays. Zero-denominator inputs are
classified before constructing an oracle fraction.

Fixtures identify a schema version, coefficient domain, characteristic for
prime fields, operation and all operands. Coefficients are in ascending order.
Rationals use reduced integer numerator/positive-denominator pairs, and
prime-field elements use canonical residues. Include the full expected pair
or an explicit `none`, rather than only an evaluation hash. The computational
conformance module has deterministic examples for every public operation and
property. Domain adapters live with tests and do not add concrete-field
dependencies to the library.

Required cases include zero, units, constant denominators other than one,
`0/0` rejection, negative leading coefficients over `Rat`, large common
factors, asymmetric degrees, a nonzero remainder in `split`, and poles versus
removable singularities. Use small prime fields including characteristic two.
Check that `derivative (X^p) = 0` there and that `X^p-X ≠ 0` despite vanishing
on every field element. Test cancellation after addition and multiplication
and the failure of unconditional evaluation-through-division at zero.

For certificates, change each of `num`, `den`, `s`, and `t` in examples where
the changed identity must fail, reject a nonmonic but fraction-equivalent
pair, reject a non-coprime pair satisfying the fraction equation, and accept
different valid Bézout witnesses for the same pair. A mutation of an irrelevant
zero multiplier need not invalidate a certificate.

## Manual and implementation milestones

The manual chapter in `HexManual/Chapters/HexRationalFn.lean` should derive
the transfer function of a new two-stage linear recurrence model using formal
rational arithmetic. Compare a cascade with a cancelled common factor and
explain what cancellation says about the rational function. A second example
uses `(X²-1)/(X-1)` at `X=1` to explain why an expression's excluded input
does not survive normalization. Neither example claims dynamical stability
from cancellation alone. A finite-field example distinguishes rational-function
equality from equality on sampled field values.

Implement in this order:

1. Representation, normalization, uniqueness and polynomial embedding in
   `HexRationalFn/{Basic,Normalize}.lean`.
2. Cancellation algorithms and field laws in `Arithmetic.lean`, then exercise
   polynomial division and extended gcd over `DensePoly (RationalFn Rat)`.
3. Evaluation, differentiation and polynomial part in `Eval.lean` and
   `Derivative.lean`, with splitting beside the arithmetic operations.
4. `Cert.lean`, kernel replay tests, conformance and the performance families.
5. The companion's equivalence and headline theorem, followed by manual
   examples. No correctness contract may retain `sorry` at completion.

The computational library and its companion are active through Phase 3.
The performance report distinguishes measured latency anchors from the remaining
Phase-4 scaling evidence. Publication is through the monorepo release manifest
once both libraries meet release readiness. No released-repository dependency
is introduced here.
