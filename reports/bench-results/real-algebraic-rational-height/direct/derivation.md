# Direct rational recognition: cost derivation

At `b=262144,524288,1048576,2097152`, let `A=(2^b-1)/3`, `D=2^b+1`
and `q=A/D`. Even b makes A an odd integer and D=3*A+2; Euclidean reduction
gives remainders 2,1,0 and hence gcd one. The canonical
minimal polynomial is therefore `D*X-A`: degree stays one while coefficient
height grows. Preparation constructs the existing canonical value and checks
its degree and recognized rational against the independent `q`. Preparation
and input hashing are outside the timed operation.

`toRat?` now uses the primitive polynomial's erased coprimality and positivity
proofs to construct a reduced core `Rat` directly. Its numerator is `-p[0]`.
In the pinned Lean 4.35.0-rc3 runtime, `lean_int_neg` on a borrowed boxed integer
calls `lean_int_big_neg`, whose native body copies the GMP integer before
negating its sign and returning a new integer. Copying a b-bit numerator costs
Θ(b) limb work. The positive denominator's absolute value, coefficient lookup
and two-field record construction add no higher-order work. The independently
derived family model is Θ(b), rather than a fitted timing exponent.

The harness times the structural result hash as well. `Rat` derives `Hashable`
from its numerator and denominator. The pinned `Hashable Int` performs `2*n`
(or `2*n+1`) before conversion to UInt64; this has at most linear limb work.
The hash does not have higher order than recognition. Floor and ceiling return
word-size results on this family, respectively zero and one. Their actual
rational-first APIs still perform recognition, and the additional quotient
and remainder calculations have at most linear work when numerator is smaller
than denominator. All three mode-1 models are therefore Θ(b).

This covers a growing degree-one leaf and the rational rounding branch only.
It does not characterize arbitrary gcd inputs, canonical rational construction,
nonrational rounding, polynomial roots or root exactification. Historical
normalizing-implementation measurements remain retained at their exact sources;
they do not admit this changed implementation. Their derivation omitted an
explicit structural-output-hash analysis, which is supplied above for the new
measurement. No historical declaration or failed/inconclusive result is edited.

This fixture approaches 1/3 rather than a dyadic boundary. The earlier fixture
approaches one with separation 2/(2^b+1). That historical family and all its
completed observations remain retained. Moving to 1/3 did not remove expensive
canonical preparation: the retained native backtrace places the worker in the
factorization prime planner's coefficient-norm square root. The first-rung
preparation probe was terminated after 969.496897 seconds without producing a
kernel observation. See `preparation-diagnostic/README.md`. No scientific
verdict admits this declaration; the cause is separate from the timed bodies'
coefficient-height model and cannot be waived by changing the fixture.

`runRationalQuotient` is the previous coefficient-quotient expression on the
same prepared input, as a comparison control. Its denominator D=3*A+2 yields
the bounded Euclidean remainders above. Single-limb reduction, normalization
and output hashing give its independently derived Θ(b) model. Comparing it
with the actual `toRat?` therefore joins identical inputs and complete outputs;
no cross-source fixture change is presented as an improvement.

Scientific settings are the compiled four-rung custom ladder, four fixed
trial-major outer trials and a 100 ms tuning target. A 600-second child cap
is an operational guard, not a scientific budget; the preparation diagnostic
exceeded it and therefore does not establish that this ladder is runnable. Every completed sample and result is retained. Before/after
comparisons use adjacent arms in four alternating AB/BA blocks, matching actual
output hashes at each parameter, on one automatically leased CPU. No quiet-core
preflight, host-load rejection or retry-until-pass is used.
