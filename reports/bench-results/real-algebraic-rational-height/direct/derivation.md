# Direct rational recognition: cost derivation

At `b=8192,16384,32768,65536`, let `A=2^b-1`, `D=2^b+1` and `q=A/D`.
The positive odd integers differ by two and have gcd one. The canonical
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

Scientific settings are the compiled four-rung custom ladder, four fixed
trial-major outer trials and a 100 ms tuning target. A 600-second child cap
allows expensive canonical preparation; it is an operational guard, not a
scientific budget. Every completed sample and result is retained. Before/after
comparisons use adjacent arms in four alternating AB/BA blocks, matching actual
output hashes at each parameter, on one automatically leased CPU. No quiet-core
preflight, host-load rejection or retry-until-pass is used.
