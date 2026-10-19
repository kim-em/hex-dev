# hex-pos-def-theory

The interpretation and correctness of
[hex-pos-def](../../HexPosDef/SPEC/hex-pos-def.md)'s exact certificates, together with the
`pos_def` tactic for `Matrix.PosDef` and its negation. All supporting
theorems are proved locally in Hex against the pinned Mathlib dependency.

## Scope and dependencies

`HexPosDefTheory` depends directly on `HexPosDef`, `HexMatrixTheory`, and
`HexBareissTheory`, plus Mathlib, and uses the namespace `Hex.PosDefTheory`.
The library owns mathematical interpretation, certificate
soundness, producer correctness, entry quotation, and tactic elaboration.
It does not own a second implementation of elimination or solving.

Support closed square matrices indexed by `Fin n` over `Int`, `Rat`,
`Real`, and `Complex`. Real entries must have certifiable rational values.
Both components of complex entries must have certifiable rational values.
Use the standard instances, including the scoped `ComplexOrder` order for
complex positive definiteness. Arbitrary algebraic constants, symbolic
entries, other index types, semidefiniteness, and inertia are outside the
initial tactic contract.

The general producer must cover every supported numeric matrix that is
successfully quoted, apart from resource exhaustion. This is a positive
definiteness decision, not a test limited to diagonally dominant matrices.

## Interpretation and soundness

Interpret integer rows as a Mathlib matrix of their integer casts.
Interpret a Gaussian entry `(a,b)` in `Complex` as `a + b * Complex.I`.
An input encoding additionally supplies `s > 0` and a proved matrix equation
`s • A = B`, where the natural scale is cast into the target carrier and
`B` denotes the decoded integer or Gaussian matrix. Scaling here is scalar
multiplication of entries, not multiplication by a matrix with every entry
equal to `s`.

Name the main certificate theorems `Int.checkPositive_sound`,
`Int.checkNegative_sound`, `Gaussian.checkPositive_sound`, and
`Gaussian.checkNegative_sound`. For arbitrary well-shaped input rows and
arbitrary certificates, acceptance implies respectively `B.PosDef` or
`¬ B.PosDef`. These are checker theorems, with no premise that a
certificate came from `certify`. Supply corresponding wrappers taking the
quoted input's identification and positive denominator, concluding the
same assertion about the user's `A`.

Factor the common matrix algebra into reusable congruence lemmas. Prove
the integer certificate sound over a linearly ordered commutative ring
with the compatible trivial star, covering integers, rationals, and reals.
Also interpret integer certificates over `RCLike` carriers so a complex
matrix whose entries are real uses the integer checker. Interpret Gaussian
certificates in `Complex`. No API for arbitrary star rings with a chosen
square root of `-1` is required.

The triangular checker establishes

```text
T * B * T* = diagonal d, with every d[i] real and strictly positive.
```

Use triangularity to prove `det T != 0`. Over fields, this makes `T` a
unit, so diagonal positivity and congruence reflection apply. Over integers
and ordered domains, use adjugates to descend without dividing: put
`N = T*` and `y = adjugate N * x`. Then `N*y = det(N)*x`, so `y != 0` for
`x != 0`. In the trivial-star case the congruence gives
`y^t * (T * B * T^t) * y = det(N)^2 * (x^t * B * x)`.
The left side is positive. Cancel the positive scalar `det(N)^2`.
In particular, `det T != 0` must not be used as a claim that `T` is a
unit over integers.

For `positiveVector`, prove the weighted sum-of-squares identity and
coordinate-product descent specified by the computational library. The
same certificate interpreted in a complex carrier uses squared absolute
values. Do not try to transfer positivity over rational test vectors to
all real or complex test vectors without an argument. Interpret the
certificate identities directly in the target carrier instead.

For negative certificates, a checked coordinate mismatch refutes
`IsHermitian`, which is part of `PosDef`. A checked nonzero vector with
nonpositive quadratic value contradicts `PosDef.dotProduct_mulVec_pos`.
Positive common scaling preserves both assertions.

## Producer correctness and completeness

Prove `Int.certify_spec` and `Gaussian.certify_spec`: every returned
classification has its stated mathematical meaning. Derive this from
producer self-validation and the checker soundness theorems.

Separately prove `Int.certify_complete` and `Gaussian.certify_complete`
for the unrestricted general method. On every square input it returns a
positive or negative certificate, without an unsupported-method result
or a rejected-certificate error. State the positive outcome equivalently
to `Matrix.PosDef` of the decoded matrix. For Gaussian data, this is its
interpretation in `Complex`. For integer data, it is `Matrix.PosDef` over
integers. Obtain the corresponding equivalences over other carriers
through the classification and certificate soundness: positive definiteness
over the larger carrier restricts to integer test vectors, forcing a
positive producer outcome, whose certificate is sound in that carrier.

Establish the no-swap augmented-minor invariant, exactness of division,
reality of Gaussian diagonal pivots, and validity of the first nonpositive
pivot's vector. These obligations concern the algorithm the executable
runs. They do not require a separate spectral algorithm, a general
Sylvester criterion, or symmetric pivoting for inertia.

Reuse the generic no-pivot invariant in `HexBareissTheory/Bareiss.lean`
and `HexMatrixTheory.desnanot_jacobi_borderedMinor` as the starting point.
Extend the bordered-minor argument to the augmented right block `[B | I]`
and prove the transform relation for this producer's recurrence. The
existing square-matrix loop theorem alone does not cover that block.
Reusing these theory lemmas does not call the determinant producer.

The positive-vector method needs soundness on success. It is an explicitly
selected specialization, and need not prove that every positive definite
input admits that method. Its capability declines have no mathematical
conclusion. A resource-limited run also need not return a classification.

The Theory proofs may use computational definitions and fully proved
computational lemmas. They must not depend on unfinished computational
proofs, directly or through another lemma or instance.

## Entry quotation

Reuse `HexMatrixTheory.Literal` for dimensions, literal recognition,
bounded definition unfolding, and closed-proof construction. Support
`!![...]`, `Matrix.of ![...]`, `fun i j => ...`, `Matrix.ofArray`, and
`Matrix.of` applied to a closed lambda. In particular, recognize
`CartanMatrix.E 8` directly, rather than requiring its literal equality
lemma as a user rewrite. Extend recognition narrowly if necessary.

Reuse the existing integer and rational scalar evaluation and literal
identification where applicable. For real and complex entries, supply
proof-producing quotation in this library. The existing `entriesEq`
kernel-`decide` route is not an evaluator for classical real or complex
equality.

For each real entry, produce its rational value and a proof of equality
to that value cast into `Real`. For each complex entry, normalize its real
and imaginary components and prove both rational-value equations, then
assemble the complex equality with extensionality. Reuse `norm_num`, scalar
simplification, and their proof-producing interfaces rather than adding a
new scalar normalization algorithm. No native evaluation is proof evidence.

Choose the common positive denominator in compiled code. Prove its
entrywise scaling equations and assemble them into `s • A = B` by matrix
extensionality over the finite indices. Reuse definitional identification
where it suffices. Do not enumerate real or complex equality using a
classical `DecidableEq`. Every quoted value and component must be accounted
for by an equality proof checked by the kernel.

Reject an unquotable entry with its coordinate and carrier. The numerical
checker still reduces only integer or integer-pair data. No claim that
entry quotation or certificate arithmetic dominates complete-call cost
is made without measurements.

## The pos_def tactic

Declare `pos_def` once as a non-reserved tactic atom. Accept exactly
`A.PosDef` and `¬ A.PosDef` for the supported closed matrices. The tactic
does not choose existential witnesses, prove Cartan axioms, or discover a
symmetrizer. Those remain ordinary Lean proof steps.

Use structure configuration with a `method` field of type
`Hex.PosDef.Method`, defaulting to `triangular`:

```lean
example : (CartanMatrix.E 8).PosDef := by pos_def

example : (CartanMatrix.E 8).PosDef := by
  pos_def (method := .positiveVector)
```

The default includes diagonal inputs represented by the same triangular
certificate with `T = 1`. There is no automatic positive-vector selection,
no family dispatcher, and no benchmark prerequisite for exposing either
method. The explicitly selected vector method accepts positive goals on
real symmetric matrices with nonpositive off-diagonal entries, including
such matrices represented in `Complex`. It declines negative goals,
nonreal inputs, and inputs for which it cannot produce a valid positive
vector. It does not silently run the general method afterward.

Follow [the matrix tactic outcome protocol](../../SPEC/matrix-tactics.md#outcome-protocol-and-diagnostics).
Classify goals and carriers before producing a certificate. Unsupported
goals, open matrices or metavariables, unsupported carriers, and unrecognized
literal shapes are `notApplicable`. Recognized inputs whose entries cannot
be quoted and unavailable specialized methods are `declined`, with the
missing capability named. Runtime resource exceptions propagate.

For a positive goal whose general result is negative, report the checked
coordinate mismatch or counterexample vector. For a negative goal whose
result is positive, report that the matrix has a positive certificate.
Do not close a goal of the wrong polarity or replace it by a weaker goal.
A producer self-check rejection or kernel rejection is `failure`, never
a recoverable unsupported input or a mathematical negative result.

Apply the relevant soundness wrapper to the quotation equations and
integer checker proof. Use the shared `addClosedProof` discipline to check
each supplied certificate synchronously and once. When reporting an
opposite-polarity result as certified, check its evidence as well. Do not
pre-evaluate the reflective checker in the elaborator or route the complete
proof through a second preliminary type check. Native checking is permitted
for producer self-validation, but does not replace kernel checking.
Use committed tactic errors and `throwUnsupportedSyntax` consistently
with the existing handler convention.

Accepted proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
`native_decide`, new axioms, and kernel replay of elimination or solving
are forbidden. No Mathlib tactic is an implicit fallback.

## Worked certificates and proof examples

Use the following certificate data as examples, not special cases in the
producer. In Mathlib's numbering, `A = CartanMatrix.E 8` has leading
principal minors

```text
2, 4, 6, 5, 4, 3, 2, 1.
```

Its fraction-free transform, written with implicit trailing zeros, is

```text
[1]
[0, 2]
[2, 0, 4]
[2, 3, 4, 6]
[2, 3, 4, 6, 5]
[2, 3, 4, 6, 5, 4]
[2, 3, 4, 6, 5, 4, 3]
[2, 3, 4, 6, 5, 4, 3, 2].
```

It gives `T*A*T^t = diagonal [2,8,24,30,20,12,6,2]`, with
`det T = 5760`. The positive-vector example is
`v = [46,68,91,135,110,84,57,29]`, for which `A*v = 1` entrywise.

Build-only examples must prove positivity of `E 6`, `E 7`, and `E 8`, and
refute positivity of `E 9` and `E 10`. The vector
`[2,3,4,6,5,4,3,2,1]` gives quadratic value zero for `E 9`, and its
zero-padded extension does so for `E 10`. The latter matrix is nonsingular,
so this also checks that a zero leading pivot is not confused with a
kernel vector of the full matrix.

Include this complete existential example, with `d = 1` supplied by the
caller:

```lean
example : ∃ d : Fin 8 → ℤ, (∀ i, 0 < d i) ∧
    (Matrix.diagonal d * CartanMatrix.E 8).PosDef := by
  refine ⟨fun _ => 1, by simp, ?_⟩
  simpa using (show (CartanMatrix.E 8).PosDef from by pos_def)
```

Also test the unrevised `CartanMatrix.E 8` expression as well as an explicit
literal. The matrix `!![2,1,1; 1,2,1; 1,1,2]` supplies a positive definite
input outside strict scaled diagonal dominance, and must succeed by the
default method. A vector-method decline must not be reported as
non-definiteness.

For complex literals with `I = Complex.I`, include
`!![2,I; -I,2]`, `!![1,I; -I,1]`, and `!![1,2*I; -2*I,1]`, respectively
positive definite, singular, and indefinite. Test both goal polarities,
a non-Hermitian example, empty and singleton inputs, and a rational-entry
example with distinct denominators. Include malformed-certificate checks
and the standard axiom audit. Exercise these distinct cases without a
cross-product over every carrier and literal syntax.

## Manual

Include live, typechecked `pos_def` examples in
`HexManual/Chapters/HexPosDef.lean`, with the Theory correspondence in the
same chapter. Require an E₈ recipe proving `(CartanMatrix.E 8).PosDef`
and the complete existential above, explaining why the symmetrizer is
constant `1`. Also include small complex literal examples demonstrating
a positive goal and a negative goal. Explain the explicitly selected
positive-vector method without turning the chapter into a test suite.

State the example matrices and goals using Mathlib types, with any
executable conversion confined to the proof. Follow
[the Manual writing conventions](../../SPEC/writing-style.md#manual-examples-that-cross-into-mathlib).
Include the chapter in `HexManual.lean` under the applicable released or
unreleased section. Both libraries use this chapter through the standard
Theory-companion ownership checks, rather than a separate Theory chapter.
When adding the chapter, register both libraries in the `HexPosDef` entry
of `CHAPTER_LIBRARIES` in `scripts/release/check_manual_split.py`, so its
released placement depends on both libraries.
Build the chapter through `lake build HexManual` and inspect the rendered examples
as part of the implementation's documentation work.

## Performance and integration

Keep one small table of complete tactic costs: `E 8` and the representative
Gram family from the computational SPEC at sizes `8`, `16`, and `32`.
Include entry quotation, native production, and kernel checking in the
complete-call cost. Include one complex example in the ordinary proof
examples to exercise its quotation path. Do not require a separate
complex scaling study, mandatory profiling, per-carrier timing grids,
or fixed wall-clock thresholds. The table is evidence about useful
examples, not a universal timing law or a comparison with a nonexistent
Mathlib positive-definiteness tactic.

Use the existing benchmark and shared-host measurement policy. The
computational benchmarks stay Mathlib-free. Theory proof examples and
their complete-call observations belong to this library and use existing
build and measurement support. No separate benchmarking framework,
workflow, or job is required. Routine correctness checks do not depend on
timing results.
