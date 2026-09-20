# Real-closure execution and interpretation

This is the shared computational boundary for the
[real-closure family](future-work.md#real-closures-of-ordered-fields).
Computational contexts, polynomial kernels, exploration, conformance and
benchmarks import no Mathlib. Companions establish their mathematical meaning;
constructing an algebraic context does not require a companion law theorem.
This does not put field instances on noncanonical representations.

## Polynomial coefficients and equality

There are two distinct coefficient interfaces:

- A canonical field `K` has the existing lawful field/order instances.
  Existing `DensePoly K`, `RationalFn K` and their theorems remain available.
- An executable representation type `E` has ordinary total arithmetic,
  structural `DecidableEq`, a unique stored zero, and an executable sign.
  `DensePoly E` uses the same polynomial operations. `E` need not satisfy
  ring identities as Lean equalities and has no asserted field instance.

An extension owns raw representatives and its semantic zero test. One
implementation of its coefficient storage is

```lean
abbrev Coeff (Raw : Type) (isZero : Raw → Bool) :=
  Option {r : Raw // isZero r = false}
```

`none` is zero. Packing a raw value tests `isZero`, returning zero or a
nonzero representative with the computed Boolean invariant. This construction
and structural equality require no theorem about a selected real root.
Arithmetic normalizes its output through this constructor. Consequently,
`e = 0` in storage agrees with the executable zero test. `DensePoly` removes
precisely these zero coefficients, without a second polynomial representation
or a fabricated `DecidableEq` for mathematical equality.

Nonzero values need not have canonical representatives. Never use structural
inequality to conclude mathematical inequality. Semantic equality tests the
zero sign of a difference; polynomial identities test coefficient differences
for zero. Structural equality is a sufficient fast path only. Replay,
monicity, gcd normalization, selected-root comparison and context transport
must use the appropriate relation. Squarefreeness can test whether a computed
gcd is a nonzero constant; it need not compare its representation with `1`.
Hash identity alone establishes neither structural nor semantic equality.

The polynomial operation instances are ordinary `Zero`, `One`, `Add`, `Sub`,
`Mul`, `Div` and so on, with the existing structural `DecidableEq`. There is
no fallible operation record, arithmetic budget or per-operation certificate.
The existing `DensePoly.divMod`, `gcd` and `xgcd` require operations
rather than a `Field` instance. `natPow` and `monicize` also accept ordinary
operations; their existing ring/field laws retain their hypotheses. The global
power-notation instance retains its ring assumption to preserve instance
selection in existing Mathlib bridges; representations call `natPow` directly.
On representatives, `monicize` need only be monic under
interpretation: its leading coefficient need not be structurally `1`. New pseudo-division uses the same separation:
operation-only computation, with domain hypotheses on correctness theorems.
Do not duplicate the Tarski kernel for representation coefficients.

Canonical-zero storage may introduce more zero tests than an implementation
which tests only leading coefficients. It does not authorize eager reduction
by defining polynomials or eager denominator normalization. Count actual
zero/sign tests, retain their cost in tower8 and clean/eager measurements,
and use proved structural fast paths and context-bound caches. No performance
claim follows from the representation alone. A later optimization must retain
the same zero/interpretation contract and shared polynomial algorithms.

## Interpretation and semantic fields

Correctness fixes a semantic ordered field `K`, an interpretation `eval : E → K`,
and proofs of preservation of zero, one and the actual arithmetic and sign.
Crucially, `eval` need not be injective. Require zero reflection:

```text
eval e = 0 ↔ e = 0
sign e = sign (eval e)
eval (a+b) = eval a + eval b, and likewise for negation, product and inverse.
```

Lift interpretation coefficientwise to `DensePoly E → Polynomial K`.
Zero reflection preserves degree despite noninjectivity. Prove preservation
of polynomial operations, division, gcd/xgcd, derivative and Horner evaluation
for this actual executable map. Existing injective polynomial equivalences
for lawful carriers are not sufficient for this bridge. For example, the
existing division degree theorem only needs leading-coefficient cancellation;
preservation plus zero reflection proves that cancellation in storage.
Companions then compose with `K →+* R` for an abstract real closed `R` and
the shared Sturm–Tarski/BKR theorems.

At a selected-root extension, interpret a representative by evaluation at
the selected root in the ambient model. Equality of denotations defines the
semantic quotient `Value ctx`. The companion proves equivalence, operation
descent, order and field laws for this quotient. It may retain a `Root.Laws`
lemma as a proof intermediate, but neither `Context.adjoin` nor executable
`Element ctx`, roots, readers or benchmarks takes that law package.
`K[X]/(p)` for reducible `p` is not the selected-root field.

The proof proceeds by tower induction: current sign determination and local
inversion use only predecessor arithmetic. The companion proves preservation
of every constructor and operation, then the quotient laws. Its semantic maps
may be noncomputable; the executable never uses classical representative
selection. Abstract real-closure existence and univariate correctness remain
real proof obligations, not prerequisites for running the algebraic code.

## Termination and validation

Computational representations carry finite storage/stage invariants, not the
entire semantic validity theorem. Distinguish syntactic construction, executable
domain checks, and mathematical correctness of those checks. Serialization
readers reject malformed or incompatible input. Correctness theorems quantify
over interpreted valid contexts and establish that generated descriptors,
root lists and transports remain valid.

Polynomial division/gcd/xgcd use their existing size-derived recursion bounds.
Pseudo-division uses at most `max(0, deg A - deg B + 1)` cancellation steps
in the nonzero, ordered-degree case; pseudo-gcd uses the input degrees.
Yun uses the original degree bound, justified in characteristic zero by
remaining multiplicity, not strict degree decrease at every iteration.
These bounds are computed internally. Companions prove that they suffice on
valid interpreted inputs; exhausting one must not be specified as a legitimate
partial result. No user accuracy or resource threshold controls completion.

Isolation bounds bisection work by the declared finite input-derived policy,
then uses finite derivative/BKR sign determination for all unresolved roots.
Query lists, derivative lists and support combinations give structural bounds
for BKR. Coefficient arithmetic recurses on tower depth; polynomial loops use
their finite size bounds. Inversion at a new algebraic level uses predecessor
gcd/xgcd and predecessor sign determination, never its own inverse. Persistent
splitting decreases defining degree. Each library must make these recursion
arguments explicit in its implementation and prove adequacy separately.

## Transcendental search is a separate obligation

The caller supplies a total computational function `approx : Rat → Bounds`
and separate proof functions. For every positive rational request `δ`, the
returned interval must contain the specific constant being approximated and
have width at most `δ`. Both guarantees are required for a verified oracle.
The evaluator calls only `approx`; containment and width proofs are used where
needed by correctness and termination arguments. Width is rational arithmetic;
containment is stated against the caller's semantic constant in the companion.
The coefficient approximation functions have the same split.

Under these guarantees and relative transcendence, the paper's refinement
loop terminates: every nonzero polynomial has nonzero evaluation, so the
bounds eventually exclude zero. The total Lean implementation takes the
resulting core-expressible accessibility/progress proof as an erased argument.
The companion derives it from the verified oracle contract. This is a Lean
proof interface, not an additional mathematical obstacle or user threshold.
Arbitrary procedures without the guarantees do not satisfy this interface.

The shared `firstSome` implementation uses accessibility and erases the
termination proof. Besides the universal progress theorem, provide
`acc_of_success`: a finite checked success `trial N = some s` proves
accessibility from any `n ≤ N`. It requires neither monotonicity of the trial
nor a proof of a universal real-field model. The witness `N` is used only in
the proof; execution still refines from the requested starting precision and
stops at its first success. It is not an input fuel or a precomputed answer.

Keep per-input total sign/approximation functions separate from the wrapper
that supplies progress for every query from an oracle registration. Compiled
benchmarks can instantiate those same functions on concrete rational-bound
inputs using finite kernel-checked successes, entirely without Mathlib.
Measure all search work, including earlier failed attempts. A checked successful trial proves termination only. Soundness of its sign
for the named real subject still requires the containment theorem; it remains
companion evidence. Such measurements exercise
total sign/approximation, not a universally registered transcendental field.
An arbitrary mixed transcendental tower still needs its caller's universal
progress proof; a finite benchmark witness cannot manufacture that interface.
Keep the companion Liouville integration fixture and do not replace it with
a synthetic trial or claim unresolved relative transcendence is proved.

## Validation boundary

[The executable prototype](../experiments/RealClosureRepresentation/README.md)
checks two levels of zero-normalized representations against the existing
polynomial kernels, proves a generic remainder-degree statement for its
selected-root example, and compiles a real-constant refinement example with
a finite termination witness. It establishes the interface mechanism, not
the full tower implementation, BKR correctness or Phase-4 performance.
All existing Mathlib-free benchmark import rules remain unchanged.
