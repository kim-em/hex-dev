# hex-rational-fn-mathlib

The correspondence between `Hex.RationalFn K` and Mathlib's `RatFunc K`,
including canonical numerator/denominator agreement and the semantics of
partial evaluation. Its immediate dependencies are `HexRationalFn` and
`HexPolyMathlib`, plus Mathlib. The computational contract is in
[hex-rational-fn](../../HexRationalFn/SPEC/hex-rational-fn.md).

## Coefficient instances and representation

Work over `[Field K] [DecidableEq K]`, using the lightweight field instance
induced by that same Mathlib field. Do not ask callers for two unrelated
field structures on one carrier. As in `HexPolyMathlib`, the executable
coefficient operations and the Mathlib operations must agree.

The required `RationalFn` structure is indexed by the entire lightweight field
instance, not just by its carrier. Choose `Field.toGrindField` before defining
values for this companion (a local instance priority can make that explicit).
Changing priorities afterwards does not convert previously defined values.
In particular, values already instantiated using Lean core's separate
`Lean.Grind.Field Rat` are not directly inputs to this equivalence. No equality
of those two bundled structures or automatic transport between them is assumed.
The computational conformance suite exercises the generic implementation at the
core rational instance; companion examples separately exercise the Mathlib-induced
instance and kernel certificate replay. This instance choice is not a second
unrelated field hypothesis on the companion's theorems.

The same choice applies at each level of an iterated rational-function field:
for `RationalFn (RationalFn K)`, choose the Mathlib-induced lightweight field
on the inner `RationalFn K` before defining outer values. The computational
and Mathlib-induced bundled field instances are not automatically identified,
even though their arithmetic, scalar multiplication, powers and casts agree.

Define `HexRationalFnMathlib.toRatFunc f` by embedding
`HexPolyMathlib.toPolynomial f.num` and `f.den` into `RatFunc K` and dividing.
Prove `toRatFunc_injective` from cross multiplication and the computational
`eq_iff`. Obtain surjectivity from a numerator/denominator presentation of
each rational function with a nonzero denominator, followed by normalization.

Expose a ring equivalence named `equiv`:

```text
Hex.RationalFn K ≃+* RatFunc K.
```

Provide the compatible Mathlib `Field` and `Algebra K` instances on the
executable type and refine the same map to a `K`-algebra equivalence
`algEquiv`. The Mathlib instances must retain the executable operations,
not install arithmetic through a noncomputable conversion. The inverse of
the mathematical equivalence may be noncomputable. It is not an algorithm
used by `HexRationalFn`.

Prove agreement of the transported stored polynomials with Mathlib's
`RatFunc.num` and `RatFunc.denom`, not just their quotient. Mathlib uses the
same coprime, monic-denominator convention. The relevant existing results
are documented in
[RatFunc.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/Basic.html).
In particular, canonical uniqueness justifies equality of the two
representations without evaluating at points.

## Headline correctness theorem

`normalize_spec` is the headline theorem. Let `P` denote
`HexPolyMathlib.toPolynomial` and `ι : Polynomial K →+* RatFunc K` the
canonical embedding. For `q ≠ 0` and `f = RationalFn.normalize p q hq`, it
states all of the following:

```text
toRatFunc f = ι(P p) / ι(P q)
P f.num = (toRatFunc f).num
P f.den = (toRatFunc f).den
```

The theorem identifies the mathematical fraction and its unique normalized
representation. The same result holds for every lawful multiplication plan.
For certificate replay, `check_sound` transports accepted data to these
claims using the computational checker soundness theorem. A replaying caller
does not reduce normalization or extended gcd in the kernel.

Prove correspondence for constants, the indeterminate, polynomial embedding,
addition, subtraction, negation, multiplication, total inversion/division and
natural powers. Checked inversion/division reject exactly the cases specified
by the computational API. Polynomial membership and `split` transport to the
unique polynomial plus proper rational-function decomposition. State the
formal derivative theorem explicitly as the quotient rule for the embedded
polynomial derivatives, together with additivity and the Leibniz rule. This
does not assume an analytic topology or differentiability structure on `K`.

## Partial evaluation

Mathlib's
[RatFunc.eval](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/AsPolynomial.html#RatFunc.eval)
is total, with value zero when its canonical denominator evaluates to zero.
That convention is not the failure behavior of `RationalFn.eval?`.

Prove `eval?_eq_some` with both conditions:

```text
RationalFn.eval? f a = some v ↔
  (P f.den).eval a ≠ 0 ∧
  v = RatFunc.eval (RingHom.id K) a (toRatFunc f).
```

Prove that `none` is equivalent to the vanishing of that same canonical
denominator. Relate evaluation to a noncanonical input `p/q` only under
`(P q).eval a ≠ 0`. The companion must not erase that hypothesis when the
normalized result has a removable singularity. No field homomorphism from
all of `RatFunc K` to `K` sending `X` to an arbitrary `a` is claimed.

## Verification and placement

Place conversion and equivalence in
`HexRationalFnMathlib/Correspondence.lean`, evaluation correspondence in
`Eval.lean`, and export both from `HexRationalFnMathlib.lean`. Polynomial
identities needed independently of Mathlib belong in the computational
library or `HexPoly`, according to their subject.

Computational conformance owner: `HexRationalFn`.

Computational performance owner: `HexRationalFn`.

Runtime examples and oracle comparisons belong to
`conformance/HexRationalFn/Conformance.lean`. Build-only examples in
`HexRationalFnMathlib/Tests.lean` prove the transported operations and
canonical components on rational and prime-field inputs. Include a regular
zero, a pole where Mathlib's total evaluator returns zero, and a cancelled
denominator. Check an explicit nontrivial normalization certificate through
the headline theorem, and inspect its theorem dependencies for `sorryAx`.
The manual's Mathlib examples state their goals in Mathlib types and introduce
executable values only inside proofs.

This is a `correspondence_only: true` library. It has no executable benchmark
targets and its comparator absence class is **correspondence-only-layer**.
The owner's normalization, arithmetic, certificate and evaluation targets
supply the runtime evidence.
Build-time conformance examples do not advertise a tactic-performance API.
Expression reification and user tactics are separate future work.
