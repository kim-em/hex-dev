# HexNumberField Performance Report

`HexNumberField` is a compiled-track library: every operation it advertises is
Mathlib-free executable computation, so all of its Phase-4 evidence is ordinary
LeanBench evidence and none of it is fresh-module proof evidence
(`PLAN/Phase4.md` §Evidence tracks).

This snapshot records the complete Phase-4 evidence. `libraries.yml` records
`HexNumberField` at `done_through: 4`; every direct dependency is also at Phase
4 or later, every advertised compiled operation is registered, and every
profiled dominant cost is attributed to a registration.

## Bench targets

The compiled Mathlib-free driver is `bench/HexNumberField/Bench.lean`. It
registers 13 controlled parametric targets and 76 fixed targets (89 total).
The adjacent comments in the driver derive each parametric model or explain the
fixed-mode choice. The contracts below are copied from the registration sites.

| target | mode | operation and controlled input | model or ceiling |
|---|---|---|---|
| `runQAdjoinAddLadder` | parametric | `QAdjoin` addition in `ℚ(2^(1/n))`, both operands dense and all-nonzero | `n` |
| `runQAdjoinSubLadder` | parametric | `QAdjoin` subtraction on the same controlled field family | `n` |
| `runQAdjoinNegLadder` | parametric | coefficientwise `QAdjoin` negation | `n` |
| `runQAdjoinSmulLadder` | parametric | rational scalar action on dense representatives | `n` |
| `runQAdjoinMulLadder` | parametric | `QAdjoin` multiplication, then reduction modulo `X^n - 2` | `n * n` |
| `runQAdjoinApprox` | fixed | dyadic-ball evaluation of a dense degree-128 representative at fixed precision | 7 s whole-child ceiling, zero grace |
| `runQAdjoinInvLadder` | parametric | `QAdjoin` inversion by monic-normalized rational extended gcd against `X^n - 2` | `n * n * (n + 7)` |
| `runQAdjoinDivLadder` | parametric | inversion followed by multiplication on the controlled field family | `n * n * (n + 7)` |
| `runAddEliminantLadder` | parametric | `ZPoly.addEliminant (X^n - 2) (X^2 - 3)`, the Brown sum-eliminant resultant | `n * n * (Nat.log2 (n + 2) + 1)` |
| `runLazyAddLadder` | fixed | end-to-end `AlgebraicRoot.add?` pairing the first root of `X^6 - 2` with `√3` | 12 s ceiling |
| `runExactLadder` | fixed | `AlgebraicRoot.exact?` on the first certified root of `∏_{p ∈ [2,3,5,7,11,13]} (X² - p)` | 200 ms whole-child ceiling, zero grace |
| `runExactFactorLadder` | fixed | `AlgebraicRoot.exactFactor?` for `X^8 - 2` inside `(X^8 - 2)(X + 3)`, with a static certified enclosing root | 2 s whole-child ceiling, zero grace |
| `runCanonicalRepLadder` | fixed | `AlgebraicNumber.canonicalRep?` for a static certified root of `X^8 - 2` | 1.1 s whole-child ceiling, zero grace |
| `runCommonPresentationLadder` | parametric | `AlgebraicPoly.Common.presentation?` over `n + 1` canonical coefficients | `n` |
| `runAlgebraicPolyOfArray` | parametric | normalized construction from an array with a zero suffix | `n` |
| `runAlgebraicPolyBeq` | parametric | equality of equal dense coefficient arrays | `n` |
| `runEvalMajorantFixed` | fixed | exact majorant evaluation of 4,096 bounded rational coefficients | 200 ms whole-child ceiling, zero grace |
| `runCommonPrimitive` | parametric | common primitive construction over `n + 1` coefficients | `n` |
| `runMergeRootListLadder` | parametric | duplicate-removal fold across the two Yun components of the fixed-field roots family, with component construction outside timing | `n ^ 2 * (Nat.log2 (n + 2) + 1)` |
| `runQAdjoinRootsLadder` | fixed | `QAdjoin.roots?` on `g^2 * (X - 1)` over `ℚ(√2)` with `g` dense of degree 6 | 20 s ceiling |
| `runAlgebraicRootsLadder` | fixed | `AlgebraicPoly.roots?` on the dense degree-6 polynomial with one `√2` coefficient | 15 s ceiling |
| advertised fixed-degree API cases | fixed | lazy and canonical arithmetic, conversion, powers, casts, zero decisions, and `AlgebraicPoly.Common` primitives | 500 ms default; 750 ms for measured slower routes, zero grace |
| `runNormEliminant`, `runEvalEliminant`, `runComponentRoots` | fixed | separable phases of the profiled repeated degree-6 component over `ℚ(√2)` | 1 s, 1.1 s, and 30 s whole-child ceilings, zero grace |

The 76 fixed registrations comprise 51 internal API, phase, and fixed-problem
cases, twenty-four Lean/PARI comparator rungs (`runQAdjoinMulPair` /
`runPariPolmodMul` at
`n = 4, 6, 8, 12, 16, 20` and `runQAdjoinInvPair` / `runPariPolmodInv` at
`n = 4, 6, 8, 10, 12, 16`), and one external-driver overhead probe
(`runPariPolmodOverhead`).

### Isolation benchmark mode

The three isolation-dominated end-to-end registrations use the fixed-problem
form described in [`SPEC/benchmarking.md` §Fixed-problem benchmarks](../SPEC/benchmarking.md#fixed-problem-benchmarks).
The ordered assessments requested by [issue #9728](https://github.com/kim-em/hex-dev/issues/9728)
and [issue #9796](https://github.com/kim-em/hex-dev/issues/9796) first ask for a
two-sided expected scaling. None can be derived independently of the timings: the former
`n⁵ log² n` expression substituted fixture assumptions into
HexRoots' explicitly heuristic `O(d³ B²)` contract. It was not a complexity
result for either operation.

[Becker–Sagraloff–Sharma–Yap, Corollary 6](https://arxiv.org/abs/1509.06231v4) proves
`Õ(d³ + d² tau)` bit operations for its `CIsolate` algorithm on a
square-free integer polynomial of degree `d` whose coefficients have magnitude
below `2^tau`. The inputs here satisfy that polynomial shape after
`squareFreeCore`. The table records `ceilLog2 coeffAbsMax`, which is the
quantity HexRoots passes to `mahlerPrec`; BSSY's strict `tau` can be one larger
when `coeffAbsMax` is a power of two. The theorem does not provide a published
upper bound for this executable, however. HexRoots differs
from `CIsolate` in its bounded-precision front end with exact-dyadic fallback,
speculative Newton acceptance, dual certificate routes, and conservative
global completeness depth. No proof transfers BSSY's amortised complexity
analysis across those changes. Profiling does show that this unmatched phase
dominates: `isolate` accounts for 91.87% of the profiled algebraic-roots
process, 92% of the lazy-addition process, and 85.01% of the repaired
fixed-field-roots process; the latter spends 92.94% of the profiled process in
the enclosing `componentRoots?` phase.

The fixed-problem option therefore applies. `n = 6` belongs to all three
former schedules, gives degree-product or norm-eliminant degree 12, and stays
practical in smoke verification. For `QAdjoin.roots?`, this is also the
canonical repeated-component case used by the performance repair and its
inclusive profile: Yun sees `g² * (X - 1)`, isolates the norm eliminant of the
dense degree-6 component, and merges the separate linear component. These are
project-internal canonical inputs; there is no comparator unit surface for
any of the three certified APIs. The 12 s and 15 s sibling ceilings give
2.5–2.6x headroom over their maximum clean repeats. The 20 s
`QAdjoin.roots?` ceiling is 2.46x the clean root-merge run's 8.114 s maximum at
the same `n = 6` input. After its warmup populates the `IO.Ref`, the fixed
registration times the same checksum body as that historical rung. The loaded-
host fixed export has a 13.272 s maximum, leaving 1.51x observed headroom; it
is retained as a stress observation rather than used as the margin baseline.
Full timing runs enforce the ceilings; merge-gating `verify` enforces the
expected hashes. Asymptotic detection is explicitly given up for these three
operations.
The per-library SPEC retains the HexRoots isolation ceiling as its worst-case
contract; changing the benchmark mode does not weaken that contract.

The compiled `isolation-stats` command reproduces the input characterisation.
`isolation target` is the exact `separationDepth` passed to `isolate`, not the
adaptive working precision eventually reached by the isolator:

| family | fixture parameter | degree after `squareFreeCore` | `coeffAbsMax` | `ceilLog2 coeffAbsMax` | isolation target |
|---|---:|---:|---:|---:|---:|
| lazy add | 2 | 4 | 10 | 4 | 36 |
| lazy add | 3 | 6 | 36 | 6 | 64 |
| lazy add | 4 | 8 | 180 | 8 | 99 |
| lazy add | 6 | 12 | 1,998 | 11 | 186 |
| lazy add | 8 | 16 | 20,520 | 15 | 314 |
| lazy add | 10 | 20 | 272,565 | 19 | 480 |
| algebraic roots | 3 | 6 | 900 | 10 | 84 |
| algebraic roots | 4 | 8 | 22,920 | 15 | 148 |
| algebraic roots | 5 | 10 | 366,720 | 19 | 228 |
| algebraic roots | 6 | 12 | 366,720 | 19 | 274 |
| algebraic roots | 8 | 16 | 602,625 | 20 | 389 |
| fixed-field roots | 2 | 4 | 7,920 | 13 | 63 |
| fixed-field roots | 3 | 6 | 15,520 | 14 | 104 |
| fixed-field roots | 4 | 8 | 814,800 | 20 | 183 |
| fixed-field roots | 6 | 12 | 45,480,960 | 26 | 351 |
| fixed-field roots | 8 | 16 | 7,518,868,896 | 33 | 584 |
| fixed-field roots | 12 | 24 | 1,972,110,460,320 | 41 | 1,082 |

The fixed exactification certificates are pinned separately because their
stored precision can include refinement beyond the isolator's initial target:

| fixed input | degree | `coeffAbsMax` | coefficient bit height | certificate precision |
|---|---:|---:|---:|---:|
| six-quadratic end-to-end polynomial | 12 | 40,361 | 16 | 241 |
| `(X⁸ - 2)(X + 3)` enclosing polynomial | 9 | 6 | 3 | 77 |
| `X⁸ - 2` canonical candidate | 8 | 2 | 2 | 53 |

The same ordered assessment resolves the three exactification registrations.
Their historical controlled sweeps are useful negative evidence: no stable
two-sided model was found, and the declarations' `n⁵ log² n` terms were the
same unproved HexRoots proxy. The current registrations therefore use the top
completed sweep rungs as canonical hard fixed inputs. The harness enforces a
deadline on the whole child, not directly on the reported operation median, so
the budgets are sized against startup plus one untimed warmup plus the timed
call or batch. With `killGraceMs := 0`, the 200 ms, 2 s, and 1.1 s declarations
are the actual child deadlines. Against the measured 41.85 ms spawn floor and
the largest clean operation calls they provide approximately 2.3x, 2.8x, and
3.1x process-level headroom, respectively, and remain operation-specific
rather than reusing the generic 30 s ladder timeout. The fast end-to-end case
uses an at-least-20 ms timed batch instead of a single-shot reading. Static certified
isolating regions and lazy warmup initialization keep fixture construction
outside the timed batch without increasing every executable spawn's floor.

The current local `hexnumberfield_bench verify` invocation completes in 10.85 s
on the reference host: 36% of the per-library 30 s soft-warning threshold and
3.0% of the repo-wide 360 s hard cap. All 77 internal and protocol targets
pass; the invocation reports only the twelve
expected PARI comparator failures because `cypari2` is absent locally. Unlike
the full timing path, `verify` runs each fixed body once and does not enforce
its per-call ceiling, so its merge-gating role here is correctness and hash
stability. A same-tree one-repeat timing of the three formerly slow headline
targets is 2.241 s (`runLazyAddLadder`), 2.272 s
(`runQAdjoinRootsLadder`), and 1.775 s (`runAlgebraicRootsLadder`); thus the
verification wall time is consistent with current code. `verify` invokes all
bodies in one process, so the lazy `IO.Ref` fixtures shared across targets are
constructed once rather than paying each standalone command's parent and
fixture cost again. The larger medians in
the historical fixed exports below describe earlier source revisions and are
not current-tree wall-time predictions.

Separately, the four exactification registrations, including the pre-existing
`runExactSelection`, verify well inside CI's 360 s hard cap for the whole bench
suite. All mode-3 registrations also pass their named local `verify`
invocations with stable expected hashes.

### Fixture control

Every degree-varying fixture here — the arithmetic operands, and the
`AlgebraicPoly` coefficients behind the common-field and algebraic-root
ladders — builds coefficient `i` from one helper, `denseRatCoeff`, whose
numerator cycles modulo 11 and denominator modulo 6. Every denominator is in
`1 .. 6`, so the reduced common denominator divides
`lcm(1, ..., 6) = 60` and stays under six bits at every degree measured. The
coefficient pattern has period 66, so it repeats in the
degree-128 arithmetic rungs and the 128-coefficient `AlgebraicPoly` rungs;
repetition does not change any coefficient's height, which is what these
controlled one-parameter models depend on.

Holding height fixed is what makes these one-parameter ladders. An earlier
form built coefficient `i` as `±(i + salt + 1) / (i + 2)`. Because
`gcd (i + salt + 1) (i + 2) = gcd (salt - 1) (i + 2)`, that reduces to
denominator `(i + 2) / gcd (i + 2) (salt - 1)`, whose lcm over the vector
still has `Θ(n)` bit length — it differs from `lcm (2, …, n + 1)` only by
divisors of the constant `salt - 1`. So those ladders varied coefficient
height together with degree and could not test any fixed-height cost model.

One caveat on the multiplication model: bounded input coefficients do not make
every rational operation single-limb, since the convolution accumulators grow
by `O(log n)` bits. The declared `n^2` is a coefficient-operation count over
the measured domain, where those accumulators stay within a machine word.

The exactification inputs separate three different claims. The fixed
`runExactSelection` case retains `(X^8 - 2)(X + 3)` as evidence for inspecting
more than one candidate, representative matching, and canonicalisation. The
two certification registrations use the same degree-eight shapes; one times
the full `exactFactor?` certification and the other isolates the public
`canonicalRep?` phase. `runExactLadder` uses the BZ-adversarial top historical
rung, the first root of the product of six distinct quadratics `X² - p`. All
three roots and isolating regions are static checked certificates. Compile-time
guards identify the handwritten polynomials with the archived family builders
and pin certificate precisions 241, 77, and 53. On the first untimed warmup in
each named child, lazy initialization checks squarefreeness but performs no root
isolation or fixture search; other benchmark children pay no initialization
cost.

The fixed data reproduce the archived top rungs exactly: the degree-12
end-to-end polynomial is `∏_{p ∈ {2,3,5,7,11,13}} (X²-p)`; the
degree-nine enclosing polynomial is `(X⁸-2)(X+3)`; and the public canonical
case uses `X⁸-2`. Their original polynomial-only hashes and per-call timings
agree with the archived rows. The current exactification checks strengthen the
hash to include both the output polynomial and its canonical isolating square.

The historical next factor-count rung is not a millisecond extension of the
measured range: a cold single call at `n = 7` spends 17.19 s in child setup before the
3.038 ms timed exactification, and `n = 8` crosses the 30 s setup cliff. Thus
the historical ceiling at six factors was fixture-cost forced. The fresh
inclusive profile is used only to apportion the executable phases: it shows
that certification and candidate re-isolation, rather than BHKS-covered
factorization, control this end-to-end family.

### Scientific arithmetic ranges

The arithmetic fixtures now certify only the selected positive real root of
`X^n - 2`. Integer Newton iteration supplies an untrusted Mahler-precision
dyadic approximation, and HexRoots' local `isolateOne?` entry point checks the
single atom directly. The certificate still says that its region contains
exactly one simple root; it no longer constructs and pairwise-separates the
other `n - 1` roots.

The addition and multiplication ladders consequently cover six doublings,
`n = 4, 8, 16, 32, 64, 128`. Degree 128 is a common controlled domain whose
timed multiplication remains in the millisecond regime. The inversion ladder
covers `n = 4, 8, 16, 32, 48, 64, 96`; its ceiling is set by the timed extended
gcd, which takes about 96 ms there: a useful upper asymptotic rung that
remains practical to sample. These are scientific operation ranges, not
fixture-wallclock caps.

### Track assignment re-audit

`HexNumberField` advertises no elaboration, tactic, emitted-proof or
kernel-checking surface, so every advertised operation belongs to the
Mathlib-free compiled row of `PLAN/Phase4.md` §Evidence tracks and none of
them is eligible for the fresh-module proof row.

The audit rechecked every declaration below in the current source: each is
still public, and each nontrivial route has evidence. Closed projections and
literal constructors are explicitly identified as grouped correctness anchors
instead of ceremonial performance targets. A target shown more than once is
an intentional shared measurement when declarations use the same implementation
route or when unrelated closed constant-time operations are explicitly grouped
as correctness anchors. In particular, a total wrapper calls its checked form
and adds only a constant-time projection.

| advertised declaration | registration | assignment |
|---|---|---|
| `QAdjoin.add` | `runQAdjoinAddLadder` | parametric, `n` |
| `QAdjoin.approx` | `runQAdjoinApprox` | fixed degree 128; failed conservative-model audit |
| `QAdjoin.sub` | `runQAdjoinSubLadder` | parametric, `n` |
| `QAdjoin.neg` | `runQAdjoinNegLadder` | parametric, `n` |
| `QAdjoin.mul` | `runQAdjoinMulLadder` | parametric, `n²` |
| `QAdjoin.inv` / `Inv.inv` | `runQAdjoinInvLadder` | parametric, `n²(n+7)` aggregate finite-word proxy; the SPEC retains the conservative `O(n³ log n)` worst-case bit-cost bound |
| `QAdjoin.div` / `Div.div` | `runQAdjoinDivLadder` | parametric, `n²(n+7)` |
| rational `SMul.smul` on `QAdjoin` | `runQAdjoinSmulLadder` | parametric, `n` |
| `QAdjoin.toAlgebraicNumber?` | `runQAdjoinCanonical` | fixed quadratic conversion |
| `QAdjoin.toAlgebraicNumber` | `runQAdjoinCanonical` | same checked conversion plus projection |
| `QAdjoin.instDecidableEq` | `runQAdjoinCanonical` | grouped runtime structural decision |
| `QAdjoin.isZero` | `runQAdjoinCanonical` | grouped constant-time decision |
| `QAdjoin` natural/integer powers | multiplication/inversion targets | repeated-squaring composition of registered routes |
| `AlgebraicRoot.add?` | `runLazyAdd` | fixed quadratic pair |
| `AlgebraicRoot.add` | `runLazyAdd` | same checked route plus projection |
| `AlgebraicRoot.sub?` | `runLazySub` | fixed quadratic pair |
| `AlgebraicRoot.sub` | `runLazySub` | same checked route plus projection |
| `AlgebraicRoot.mul?` | `runLazyMul` | fixed quadratic pair |
| `AlgebraicRoot.mul` | `runLazyMul` | same checked route plus projection |
| `AlgebraicRoot.div?` | `runLazyDiv` | fixed quadratic pair |
| `AlgebraicRoot.div` | `runLazyDiv` | same checked route plus projection |
| `AlgebraicRoot.inv?` | `runLazyInv` | fixed quadratic root |
| `AlgebraicRoot.inv` | `runLazyInv` | same checked route plus projection |
| `AlgebraicRoot.neg` | `runLazyNeg` | fixed reflection route |
| `AlgebraicRoot.ofEliminant?` | lazy arithmetic targets | shared checked root-construction route |
| `AlgebraicRoot.exact?` / `AlgebraicRoot.exact` | exactification targets | checked route and total projection |
| `AlgebraicNumber.zeroRep` | `runZeroDecisions` | grouped fixed accessor/decisions |
| `AlgebraicNumber.canonicalRep?` | `runCanonicalRepLadder` | fixed hard canonicalization case |
| `AlgebraicNumber.add` | `runAlgebraicAdd` | fixed canonical pair |
| `AlgebraicNumber.sub` | `runAlgebraicSub` | fixed canonical pair |
| `AlgebraicNumber.mul` | `runAlgebraicMul` | fixed canonical pair |
| `AlgebraicNumber.div` | `runAlgebraicDiv` | fixed canonical pair |
| `AlgebraicNumber.neg` | `runAlgebraicNeg` | fixed canonical input |
| `AlgebraicNumber.inv` | `runAlgebraicInv` | fixed canonical input |
| `AlgebraicNumber.ofRat` | `runAlgebraicConstructors` | grouped linear constructor route |
| `AlgebraicNumber.toQAdjoin` | `runAlgebraicConstructors` | grouped fixed conversion |
| `AlgebraicNumber.toRoot` | canonical arithmetic and zero-decision targets | shared constant-time projection |
| `One.one` | `runAlgebraicConstructors` | grouped `ofRat` correctness anchor |
| `NatCast.natCast` | `runAlgebraicConstructors` | same linear constructor route |
| `IntCast.intCast` | `runAlgebraicConstructors` | same linear constructor route |
| `OfNat.ofNat` | `runAlgebraicConstructors` | same linear constructor route |
| `Pow.pow Nat` | `runAlgebraicNatPow` | fixed exponent 7 |
| `Pow.pow Int` | `runAlgebraicIntPow` | fixed exponent -5, including inverse |
| rational `SMul.smul` on `AlgebraicNumber` | `runAlgebraicScalars` | grouped canonical scalar route |
| natural `SMul.smul` on `AlgebraicNumber` | `runAlgebraicScalars` | grouped canonical scalar route |
| integer `SMul.smul` on `AlgebraicNumber` | `runAlgebraicScalars` | grouped canonical scalar route |
| `AlgebraicNumber.beq` / `BEq.beq` | `runAlgebraicPolyBeq` | coefficientwise canonical equality route |
| `AlgebraicRoot.isZero` | `runZeroDecisions` | grouped fixed decision |
| `AlgebraicNumber.isZero` | `runZeroDecisions` | grouped fixed decision |
| `RefinedIsolation.containsZero` | `runZeroDecisions` | grouped fixed decision |
| `AlgebraicPoly.ofArray` | `runAlgebraicPolyOfArray` | parametric, `n` |
| `AlgebraicPoly.coeff` | `runAlgebraicPolyAccessors` | grouped fixed accessor |
| `AlgebraicPoly.coeffs` | `runAlgebraicPolyAccessors` | grouped fixed accessor |
| `AlgebraicPoly.size` | `runAlgebraicPolyAccessors` | grouped fixed accessor |
| `AlgebraicPoly.degree?` | `runAlgebraicPolyAccessors` | grouped fixed accessor |
| `AlgebraicPoly.isZero` | `runAlgebraicPolyAccessors` | grouped fixed accessor |
| `AlgebraicPoly.beq` | `runAlgebraicPolyBeq` | parametric, `n` |
| `Disambiguation.evalMajorant` | `runEvalMajorantFixed` | fixed length 4,096 with rational `valueBound`; failed conservative-model audit |
| `Common.signedShift` | `runCommonSignedDegree` | grouped fixed arithmetic/accessor |
| `Common.degree` | `runCommonSignedDegree` | grouped fixed arithmetic/accessor |
| `Common.rational?` | `runCommonRational` | fixed canonical construction |
| `Common.add?` | `runCommonAdd` | fixed canonical construction |
| `Common.mul?` | `runCommonMul` | fixed canonical construction |
| `Common.scale?` | `runCommonScale` | fixed canonical construction |
| `Common.shift?` | `runCommonShift` | fixed canonical construction |
| `Common.extendShiftStep` | `runCommonExtendStep` | fixed canonical construction |
| `Common.extendShift?` | `runCommonExtendShift` | fixed canonical construction |
| `Common.extend?` | `runCommonExtend` | fixed canonical construction |
| `Common.primitive?` | `runCommonPrimitive` | parametric, `n` |
| `Common.powers?` | `runCommonPowers` | fixed powers through exponent 16 |
| `Common.trace?` | `runCommonTrace` | fixed accessor |
| `Common.coordinates?` | `runCommonCoordinates` | fixed coordinate solve |
| `QAdjoin.Roots.normEliminant` | `runNormEliminant` | fixed repeated degree-6 component |
| `QAdjoin.Roots.evalEliminant` | `runEvalEliminant` | fixed repeated degree-6 component |
| `QAdjoin.Roots.componentRoots?` | `runComponentRoots` | fixed repeated degree-6 component |
| `QAdjoin.Roots.sameValue?`, `mergeRoot`, `mergeRootList` | `runMergeRootListLadder` | parametric duplicate-removal route |
| `QAdjoin.roots?` / `QAdjoin.roots` | root targets | the total target calls the checked route and projects |
| `AlgebraicPoly.roots?` / `AlgebraicPoly.roots` | algebraic-root target | the total target calls the checked route and projects |

The Attribution-rule phases are now explicit too. The existing
`runExactFactorLadder` and `runCanonicalRepLadder` cover the 95.58% candidate
re-isolation and 47.39% nested canonical-representation shares of the original
`exact?` profile. `runMergeRootListLadder` covers the original roots profile's
83.04% duplicate-removal share. The three new root-phase registrations cover
`componentRoots?`—91.45% of the algebraic-polynomial-roots profile—and both
separable eliminants. There is no unresolved compiled-surface or attribution
gap.

## Verdicts

Thirteen ladders use **mode 1, two-sided parametric**:
`runQAdjoinAddLadder`, `runQAdjoinMulLadder`, `runAddEliminantLadder`,
`runQAdjoinInvLadder`, `runCommonPresentationLadder`, and
`runMergeRootListLadder`, plus the seven API-surface ladders for subtraction,
negation, scalar multiplication, division, `AlgebraicPoly.ofArray`,
`AlgebraicPoly.beq`, and `Common.primitive?`. Their adjacent derivations give
the intended algorithms' expected scaling on the controlled families before
measurement, and all thirteen pass.

`runLazyAddLadder`, `runExactLadder`, `runExactFactorLadder`,
`runCanonicalRepLadder`, `runQAdjoinRootsLadder`, and
`runAlgebraicRootsLadder`, `runCommonPowers`, `runQAdjoinApprox`, and
`runEvalMajorantFixed` use **mode 3, fixed
registration with an absolute budget**. The adjacent isolation-mode
assessments record why modes 1 and 2 do
not apply, identify their canonical inputs, and set 12 s, 200 ms, 2 s, 1.1 s,
20 s, 15 s, 500 ms, 7 s, and 200 ms whole-child ceilings. All fixed
measurements and hashes pass.
This deliberately gives up asymptotic detection for those operations without
changing their per-library worst-case contracts.

The other 67 fixed registrations are canonical API, separable-phase,
comparator, and protocol checks. Their adjacent derivations justify a fixed
input or grouped constant-time route; none makes an asymptotic claim.
Historical parametric failures remain diagnostic evidence and are not
reclassified as passes.

Authoritative verdict per ladder, and which committed run it comes from. The
runs below give the measurements; this table says which one counts.

| target | verdict | slope | from |
|---|---|---:|---|
| `runQAdjoinAddLadder` | **consistent** | -0.066 | current API-surface audit |
| `runQAdjoinSubLadder` | **consistent** | -0.067 | current API-surface audit |
| `runQAdjoinNegLadder` | **consistent** | -0.051 | current API-surface audit |
| `runQAdjoinSmulLadder` | **consistent** | -0.019 | current API-surface audit |
| `runQAdjoinMulLadder` | **consistent** | -0.015 | current API-surface audit |
| `runQAdjoinApprox` | **fixed: 17.244 ms, hash match** | — | API-surface fixed |
| `runQAdjoinInvLadder` | **consistent** | **-0.106** | Phase-4 completion rerun |
| `runQAdjoinDivLadder` | **consistent** | -0.102 | current API-surface audit |
| `runAddEliminantLadder` | **consistent** | +0.116 | current API-surface audit |
| `runAlgebraicPolyOfArray` | **consistent** | -0.080 | current API-surface audit |
| `runAlgebraicPolyBeq` | **consistent** | -0.008 | current API-surface audit |
| `runEvalMajorantFixed` | **fixed: 5.968 ms, hash match** | — | API-surface fixed |
| `runCommonPrimitive` | **consistent** | -0.029 | current API-surface audit |
| `runLazyAddLadder` | **fixed: 4.539 s, hash match** | — | isolation fixed |
| `runExactLadder` | **fixed: 1.878 ms, hash match** | — | exactification mode 3 |
| `runExactFactorLadder` | **fixed: 308.643 ms, hash match** | — | exactification mode 3 |
| `runCanonicalRepLadder` | **fixed: 154.045 ms, hash match** | — | exactification mode 3 |
| `runCommonPresentationLadder` | **consistent** | -0.171 | current API-surface audit |
| `runMergeRootListLadder` | **consistent** | -0.281 | current three-trial root-merge audit |
| `runQAdjoinRootsLadder` | **fixed: 11.108 s, hash match (loaded host)** | — | QAdjoin roots fixed |
| `runAlgebraicRootsLadder` | **fixed: 5.955 s, hash match** | — | isolation fixed |
| `runCommonPowers` | **fixed: 34.734 ms, hash match** | — | API-surface fixed |

All thirteen parametric registrations receiving a statistically matching
two-sided harness verdict have models derived independently of timed results. The former
`runQAdjoinRootsLadder` sweep matched a withdrawn heuristic isolation proxy;
its result remains diagnostic history and the fixed registration supersedes
it. The former `runQAdjoinInvLadder` declaration and the three archived
exactification sweeps were faster than declared; the latter remain diagnostic
evidence for why no parametric model was retained, while their current fixed
registrations pass.
The initial `Common.powers?` sweep was smooth through exponent 16, jumped from
about 35 ms at 16 to 1.3 s at 24, and exceeded its 30 s child cap at 32.
Because no independent one-parameter model explains that coefficient-shape
cliff, the current target retains the largest stable pre-cliff case as a fixed
absolute-budget registration rather than treating the failed sweep as a pass.
None of those classifications is a measurement artefact, and §Profile
identifies the controlling phases.
For the normalized inversion chain specifically, the single-root fixture now
carries the repaired implementation through degree 96. Stepwise chain
instrumentation supplies the tighter aggregate finite-word model that passes
below; the SPEC separately retains the conservative `O(n³ log n)` worst-case
bit-cost bound.

The final clean-tree API-surface audit ran the controlled ladders once per rung;
the earlier three-trial audit remains diagnostic history only.
`AlgebraicPoly.ofArray` was initially too close to fixed call overhead through
256 entries, so its unchanged linear derivation was re-run on the extended
4-through-2048 schedule where the suffix traversal is measurable. The final
verdicts are:

| target | schedule | model | verdict | slope |
|---|---|---:|---|---:|
| `runQAdjoinSubLadder` | 4..128, doubling | `n` | **consistent** | -0.067 |
| `runQAdjoinNegLadder` | 4..128, doubling | `n` | **consistent** | -0.051 |
| `runQAdjoinSmulLadder` | 4..128, doubling | `n` | **consistent** | -0.019 |
| `runQAdjoinDivLadder` | 4, 8, 16, 32, 48, 64, 96 | `n²(n+7)` | **consistent** | -0.102 |
| `runAlgebraicPolyOfArray` | 4..2048, doubling | `n` | **consistent** | -0.080 |
| `runAlgebraicPolyBeq` | 4..256, doubling | `n` | **consistent** | -0.008 |
| `runCommonPrimitive` | 2..128, doubling | `n` | **consistent** | -0.029 |

The all-target post-rebase run had one noisy `runMergeRootListLadder` top rung
(0.964 ms at `n = 12`) and therefore an inconclusive one-trial verdict. The
focused clean-tree rerun uses three outer trials: the `n = 12` median is
0.533 ms with 4.52% spread, and the ladder is consistent with slope -0.281.
That focused result is authoritative for the merge target; the one-trial row is
retained in the complete inventory rather than silently discarded.

The corresponding fixed export covers the 35 newly registered fixed targets;
every target has a declared hash, every repeat agrees, and every observed hash
matches. On the exact profiled degree-six component, the representative phase
medians are 64.456 us for `runNormEliminant`, 43.384 ms for
`runEvalEliminant`, and 2.315 s for `runComponentRoots`. The runtime-fed
quadratic `runQAdjoinCanonical` conversion is 928 us. Sub-microsecond grouped
accessors are intentionally retained as fixed registrations: their inputs pass
through `IO.Ref`, and the harness warning records that the genuine operation is
smaller than its one-microsecond diagnostic floor.

Fixed medians exclude the untimed warmup and lazy fixture construction, but the
zero-grace ceiling covers the whole child. Direct one-repeat parent invocations
of `runNormEliminant`, `runEvalEliminant`, and `runComponentRoots` took 0.235 s,
0.343 s, and 9.520 s respectively, including parent overhead. Their 1 s, 1.1 s,
and 30 s child ceilings therefore retain at least 3x even that more conservative
end-to-end observation; the degree-six component budget is not inferred from
its 2.288 s reported operation median alone.

The approximation and majorant registrations were deliberately demoted after
a stricter model review. The conservative quartic approximation proxy is
inconclusive with slope -2.262 on the 4-through-128 sweep; the former quadratic
proxy also accelerates at the upper rungs. The independently derived quadratic
linear-bit proxy for `evalMajorant` is inconclusive with slope -0.689 on the
32-through-4096 sweep after crossing the small-Nat/GMP boundary. The diagnostic
export records both failures. Their fixed cases retain the largest controlled
inputs under measured whole-child budgets without presenting either failed fit
as scientific evidence.

Eight historical parametric runs are committed: one original full-suite pass, two idle-host
re-measurements that between them cover all nine ladders, and a
fixture-corrected run plus the single-root run that supersede six of those,
the exactification audit covering its two new phase ladders and replacement
family, the aggregate inversion rerun, and the root-merge fix run. Both repaired root ladders extend to the
two-octave range needed for `fitSlope`. §Artefact traceability
records the source commit and SHA-256 of each, and says which supersedes
which. The isolation fixed exports supersede the parametric verdicts for
`runLazyAddLadder`, `runQAdjoinRootsLadder`, and `runAlgebraicRootsLadder`, and the exactification mode-3
export supersedes the three exactification audit verdicts. Their earlier
sweeps remain diagnostic evidence for withdrawing the unsupported models.

The **original full-suite run** covers the nine registrations that existed at
source commit `066f6fc29`, at three outer trials per rung:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinAddLadder \
  Hex.NumberFieldBench.runQAdjoinMulLadder \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  Hex.NumberFieldBench.runAddEliminantLadder \
  Hex.NumberFieldBench.runLazyAddLadder \
  Hex.NumberFieldBench.runExactLadder \
  Hex.NumberFieldBench.runCommonPresentationLadder \
  Hex.NumberFieldBench.runQAdjoinRootsLadder \
  Hex.NumberFieldBench.runAlgebraicRootsLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific.json
```

`chungus2` is shared, and other work on it drove the one-minute load average
from 105 to above 150 during that run. The bench child held a full core
throughout, and a uniform slowdown cancels in a log-log slope fit, but
transient spikes do not: `runQAdjoinMulLadder` recorded a 48% three-trial
spread at its top rung and `runAddEliminantLadder` 65% at `n = 128`.

The **quiet run** therefore re-measures the ladders that fit inside a short
window, at five outer trials, with the host idle (load average 1.5). Three of
its six entries — `runAddEliminantLadder`, `runCommonPresentationLadder`, and
`runQAdjoinInvLadder` — were later superseded and are omitted from the table:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinAddLadder \
  Hex.NumberFieldBench.runQAdjoinMulLadder \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  Hex.NumberFieldBench.runAddEliminantLadder \
  Hex.NumberFieldBench.runExactLadder \
  Hex.NumberFieldBench.runCommonPresentationLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific-quiet.json
```

Quiet run, worst per-rung spread now at or below 5.5%:

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runQAdjoinAddLadder` | 4, 6, 8, 12, 16, 24 | **consistent** | -0.054 | 109.4..120.6 | 4.96% |
| `runQAdjoinMulLadder` | 4, 6, 8, 12, 16, 24 | **consistent** | -0.009 | 467.5..473.6 | 3.51% |
| former `(X^n - 2)(X + 3)` exactification ladder | 2, 3, 4, 6, 8 | inconclusive | — | 2.014..174.6 | 5.49% |

`runQAdjoinMulLadder`'s full-suite verdict was `inconclusive` at `+0.222`
solely because of the load spike at `n = 24`; on the idle host its `C` is flat
to 1.3% across all six rungs.

The **single-root run** refreshes all three fixed-field arithmetic ladders
after their fixture and scientific domains changed:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinAddLadder \
  Hex.NumberFieldBench.runQAdjoinMulLadder \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-single-root.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runQAdjoinAddLadder` | 4, 8, 16, 32, 64, 128 | **consistent** | -0.064 | 94.94..110.95 | 2.56% |
| `runQAdjoinMulLadder` | 4, 8, 16, 32, 64, 128 | **consistent** | -0.018 | 449.10..470.35 | 5.86% |
| `runQAdjoinInvLadder` | 4, 8, 16, 32, 48, 64, 96 | inconclusive | **+1.784** | 549.2..46288.9 | 2.93% |

Addition remains linear through 128 and multiplication remains quadratic
through 128. The shipped inversion chain's monotone normalized cost grows even
more clearly over the repaired range: the extended ladder strengthens the
existing #9721 finding rather than attributing the former ceiling to its
fixture.

The **aggregate inversion run** measures the repaired `QAdjoin.inv` at the
same scientific schedule and five outer trials. The Phase-4 completion rerun
supersedes the normalized-chain repair's earlier timing export:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  --outer-trials 5 \
  --export-file \
    reports/bench-results/hex-number-field-phase4-final-inversion.json
```

The untimed diagnostic replays the exact `xgcdLeftMonicAux` recurrence on the
same prepared input and emits one row per nonzero divisor:

```sh
.lake/build/bin/hexnumberfield_bench qadjoin-inv-chain-stats \
  > reports/bench-results/hex-number-field-qadjoin-inv-chain.csv
```

Every nonterminal step drops the remainder degree by one. The diagnostic
records separate peak numerator and denominator widths for the normalized
divisor and cofactor, plus the next-remainder degree and an explicit zero flag.
The two work columns are linear-width proxies over normalization, division,
the one-sided Bezout product, and subtraction; `limb_work` applies the same
charge after rounding each numerator and denominator to 64-bit runtime limbs.
They do not model the gcd inside `Rat.normalize` or the superlinear cost of
large-integer arithmetic.

| n | nonzero steps | peak numerator bits | peak denominator bits | bit work / `n³` | limb work | limb work / `n²(n+7)` |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 5 | 16 | 16 | 50.750 | 345 | 1.960 |
| 8 | 9 | 57 | 56 | 71.014 | 1,372 | 1.429 |
| 16 | 17 | 118 | 121 | 78.527 | 7,693 | 1.307 |
| 32 | 33 | 282 | 281 | 90.424 | 56,086 | 1.404 |
| 48 | 49 | 426 | 429 | 91.279 | 179,136 | 1.414 |
| 64 | 65 | 622 | 625 | 96.435 | 434,458 | 1.494 |
| 96 | 97 | 926 | 922 | 89.383 | 1,319,965 | 1.391 |

The controlled fixture's recorded widths are linear in `n`, so its `Θ(n²)`
coefficient slots give a cubic linear-bit aggregate. Rounding each numerator
and denominator up to a limb adds a quadratic lower-order term, giving the
form `A*n³ + B*n²`. A least-squares decomposition of the deterministic counts
over the verdict region `n = 8 .. 96` gives `A = 1.424`, `B = 9.563`, and
`B/A = 6.72`; rounding that dimensionless transition yields the registered
proxy `n²(n+7)`. Its limb-count residual slope is `+0.014` over that region
and `-0.067` with the leading rung included. This calibration uses the untimed
operation trace, not benchmark timings. The general Hadamard peak is still
`O(n log n)` bits, so charging every one of the `O(n²)` coefficient operations
that peak retains the separate conservative `O(n³ log n)` worst-case bound in
the SPEC.

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runQAdjoinInvLadder` | 4, 8, 16, 32, 48, 64, 96 | **consistent** | **-0.106** | 101.713..137.605 | 1.85% |

All seven rungs have five-trial spread at or below 1.85%. Median time is
714.2 µs at `n = 16`, 4.720 ms at `n = 32`, 32.570 ms at `n = 64`, and
96.551 ms at `n = 96`: respectively 2.08×, 4.28×, 14.70×, and 30.92× faster
than the shipped-chain single-root medians. At `n = 4`, normalization's extra
scale passes cost 23.79 µs versus 20.24 µs, a 17.5% regression; it is
already 1.07× faster at `n = 8`. The result hashes match the superseded run at
all seven rungs, confirming identical reduced inverses. Against the complexity
declaration, the normalized chain is now consistent with the operation-trace-
calibrated aggregate finite-word proxy. The slope tolerance remains unchanged.
The paired PARI inversion registrations were rerun separately below so the
comparator ratios also describe the normalized implementation.

The **exactification audit run** measures the replacement end-to-end family
at five outer trials and both newly separated certification phases at three:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runExactLadder \
  --outer-trials 5 \
  --export-file /tmp/hex-number-field-exactification-end-to-end.json
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runExactFactorLadder \
  Hex.NumberFieldBench.runCanonicalRepLadder \
  --outer-trials 3 \
  --export-file /tmp/hex-number-field-exactification-phases.json
```

The end-to-end result in the export is a separate five-trial invocation of the
first target on the same clean implementation; the two three-trial phase
results come from the preceding clean commit, and the intervening commits
change benchmark artefacts only.

| target | ladder | verdict | cMin..cMax | worst spread |
|---|---|---|---:|---:|
| `runExactLadder` | 2, 3, 4, 5, 6 quadratic factors | inconclusive | 0.000129..0.0857 | 4.40% |
| `runExactFactorLadder` | 2, 3, 4, 6, 8 | inconclusive | 2.004..168.0 | 5.53% |
| `runCanonicalRepLadder` | 2, 3, 4, 6, 8 | inconclusive | 515.8..2551 | 1.28% |

The historical end-to-end per-call times are small, but the spawn-floor
comparison is against each amplified child-side batch, not one call: its
32/64-repeat rows run for 53.36–95.37 ms against a 41.85 ms measured spawn
floor. The former parametric registration used
`signalFloorMultiplier := 1.0` to disable the conservative default 10×
exclusion without timing parent-side startup as algorithm work; the current
registration is fixed and does not carry that setting.

All three historical sweeps remain in the faster-than-declared direction. `canonicalRep?` uses
the declared heuristic isolation envelope; `exactFactor?` uses that envelope
plus the BHKS factorization it invokes for its irreducibility guard; and the
end-to-end model is BHKS evaluated at the fixture's actual degree and height.
These are large monotone shape mismatches, quantified below, not
constant-factor slack.
Under the harness's two-sided verdict none is a parametric pass. The ordered
rule therefore proceeds to mode 3: the current fixed registrations retain the
hard top rungs without claiming that those withdrawn envelopes model scaling.

The **exactification mode-3 run** is a clean five-trial measurement of those
three fixed registrations at source `2df51cf4b`:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runExactLadder \
  Hex.NumberFieldBench.runExactFactorLadder \
  Hex.NumberFieldBench.runCanonicalRepLadder \
  --outer-trials 5 \
  --export-file \
    reports/bench-results/hex-number-field-exactification-mode3-2df51cf4b.json
```

| target | median | min..max | whole-child ceiling | observed hash |
|---|---:|---:|---:|---|
| `runExactLadder` | 1.878 ms | 1.871..1.885 ms | 200 ms | `0x5bfd5b96f72b6002` |
| `runExactFactorLadder` | 308.643 ms | 306.667..310.988 ms | 2 s | `0xe5c33ee70736a0fb` |
| `runCanonicalRepLadder` | 154.045 ms | 153.773..156.491 ms | 1.1 s | `0x1d7ae08962f9292c` |

Every repeat completed, all repeat hashes agreed, and every expected hash
matched. These budgets are enforced by the full timing path; `verify` checks
the same inputs and hashes in smoke mode.

The later HexRoots bounded-finisher repair leaves this operation and its
budget unchanged but selects a tighter dyadic representative in the
end-to-end `runExactLadder` result. Current-tree verification therefore uses
`0xd0642a7d4df3da02`; the two phase-isolated hashes above remain unchanged.

A second quiet run historically covered the three ladders too expensive to fit
in the same window, at three outer trials, on the idle host. The two
isolation-dominated sweeps are retained as diagnostic evidence but are no
longer registered parametrically:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runLazyAddLadder \
  Hex.NumberFieldBench.runQAdjoinRootsLadder \
  Hex.NumberFieldBench.runAlgebraicRootsLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific-quiet-heavy.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runLazyAddLadder` | 2, 3, 4, 6, 8, 10 | **consistent** | -0.123 | 64088..107864 | 0.92% |
| `runQAdjoinRootsLadder` | 2, 3, 4, 6, 8 | inconclusive | — | 1.134e6..2.016e6 | 3.57% |
| `runAlgebraicRootsLadder` | 3, 4, 5, 6, 8 | inconclusive | — | 80829..184738 | 1.48% |

The two root ladders reproduce the full-suite run almost exactly
(`runQAdjoinRootsLadder` 1.134e6..2.016e6 against 1.176e6..2.013e6;
`runAlgebraicRootsLadder` 80829..184738 against 80419..185225), so the
historical verdicts do not depend on host conditions. `runLazyAddLadder` improved from
`-0.300` to `-0.123` once the load-induced spike at its 113 s top rung is
gone. Its apparent pass was against the same unsupported composed model, so
it did not justify retaining a parametric registration.

Between the two quiet runs, every one of the nine ladders has an idle-host
measurement, and the full-suite export is retained as the first pass.

A **fixture-corrected run** closes out the three ladders whose inputs or
schedules changed in review. `prepAlgPolyInput` still built coefficient `i` as
`(i + 1) / (i + 2)` after `denseRatCoeff` was fixed, so the two ladders it
feeds were still varying coefficient height with degree; it now shares the
bounded-height helper. `runAddEliminantLadder` and
`runCommonPresentationLadder` also had their low rungs restored, so each
covers the range its downstream caller actually uses rather than starting
above the start-up-dominated regime:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runAddEliminantLadder \
  Hex.NumberFieldBench.runCommonPresentationLadder \
  Hex.NumberFieldBench.runAlgebraicRootsLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific-fixture-corrected.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runAddEliminantLadder` | 4, 8, 16, 32, 64, 128, 256 | **consistent** | +0.115 | 91.8..168.1 | 1.46% |
| `runCommonPresentationLadder` | 2, 4, 8, 16, 32, 64, 128 | **consistent** | -0.245 | 7.771e6..1.823e7 | 5.18% |
| `runAlgebraicRootsLadder` | 3, 4, 5, 6, 8 | inconclusive | — | 64309..234783 | 3.11% |

Restoring the low rungs costs margin and buys coverage, which is the right
trade: `runAddEliminantLadder` moves from `+0.015` over `16 .. 256` to
`+0.115` over `8 .. 256` against a 0.15 tolerance, and
`runCommonPresentationLadder` from `+0.027` over `16 .. 128` to `-0.245` over
`4 .. 128` against its declared 0.35 tolerance. Both still fit their unchanged
declared models, now over ranges that include the degrees their callers use.

The former `runAlgebraicRootsLadder` sweep moved the other way. On the
uncontrolled fixture its
continuous-proxy slope was `-0.490`; with bounded coefficient height it is
`-1.406`, because the old fixture's growing coefficients were inflating the
large-`n` end. This finding motivated the fixed-mode analysis above.

The **root-merge fix run** historically superseded `runQAdjoinRootsLadder`
from the heavy run and added the phase target required by the Attribution
rule:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runMergeRootListLadder \
  Hex.NumberFieldBench.runQAdjoinRootsLadder \
  --outer-trials 3 \
  --export-file \
    reports/bench-results/hex-number-field-phase4-scientific-root-merge-fix.json
```

| target | ladder | verdict | cMin..cMax | worst spread |
|---|---|---|---|---:|
| `runMergeRootListLadder` | 2, 3, 4, 6, 8, 12 | **consistent** | 506.8..855.8 | 2.85% |
| `runQAdjoinRootsLadder` | 2, 3, 4, 6, 8, 12 | **consistent** | 114733..224068 | 2.29% |

The end-to-end medians are 29.772 ms, 174.503 ms, 917.784 ms, 8.029 s,
37.577 s and 349.552 s. Against the superseded run's values through `n = 8`,
the speedup grows from 4.2x at `n = 2` to 15.8x at `n = 8`. The isolated
merge takes 8.904 µs through 492.960 µs. Its `n = 12` fixture takes about six
minutes because norm-root construction is outside the timed kernel; the 900 s
per-call cap permits that prelude without charging it to `mergeRootList`.

At that source commit the end-to-end registration retained its original
`n⁵ log² n` derivation. After the optimization, `n = 12` became reachable and
the harness could fit that declaration over two octaves. Issue #9796 found
that this was still a composed heuristic rather than an independently derived
family model. The sweep remains repair evidence, but its matching verdict is
superseded by the fixed mode-3 registration.

The **QAdjoin roots fixed run** measures the canonical `n = 6` repeated-
component input from that repaired family on a clean source commit:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinRootsLadder \
  --export-file \
    reports/bench-results/hex-number-field-qadjoin-roots-fixed.json
```

The three loaded-host repeats are 13.272 s, 11.108 s, and 10.305 s
(median 11.108 s),
all below the enforced 20 s ceiling and all returning
`0x1b2a158c4b746671`. The host's one-minute load average was 61.25 across 96
logical CPUs immediately after the run; the result is therefore not used to
tighten the budget derived from the earlier idle-host baseline. It is
fixed-mode evidence from a clean source commit that the canonical operation
completes within that budget under this loaded-host observation and preserves
its expected result.

### Sensitivity to integer-log steps

`fitSlope` rejects a log-log fit whose x-range is too narrow. The historical `runExactLadder`
and the former parametric `runAlgebraicRootsLadder` sweep span under two octaves
because their top rungs already cost 0.3 s and 25 s per call. The harness then falls back to a
multiplicative range check,
`cMax / cMin ≤ max(narrowRangeNoiseFloor,
exp(slopeTolerance · xRange))`. That check is
sensitive to a discontinuity anywhere in the ladder, and
`(Nat.log2 (n + 2)) ^ 2` supplies one: it is an integer step function, so the
declared model jumps by 2.25x in a single rung — between `n = 5` and `n = 6`
for `runAlgebraicRootsLadder`.

Recomputing `C` against a continuous asymptotic proxy — the same expression
with real `log₂` in place of `Nat.log2` — separates that artefact from the
residual. `Nat.log2` and real `log₂` are different functions at these rungs,
so this is a sensitivity check and not a restatement of the declared model:
the registrations were unchanged during that diagnostic run, and every
historical verdict quoted here is the harness's result for the then-registered
integer model. The
harness bound is reproduced in the table only to show the scale of the
artefact, not as a verdict on the proxy.

| target | integer-log cMax/cMin | smooth-log cMax/cMin | fallback bound | smooth-log slope |
|---|---:|---:|---:|---:|
| `runLazyAddLadder` | 1.683 | 1.199 | 1.524 | -0.028 |
| former `(X^n - 2)(X + 3)` exactification ladder | 86.697 | 80.498 | 1.500 | **-4.145** |
| `runQAdjoinRootsLadder`, before repair | 1.777 | 1.953 | 1.500 | **+0.675** |
| `runQAdjoinRootsLadder`, repaired | 1.953 | 1.384 | — | -0.258 |
| `runAlgebraicRootsLadder` | 2.680 | 2.680 | 1.500 | **-1.406** |

The three historical exactification sweeps also have no fitted slope. Their
integer-model ratios, including the harness bound they failed, are:

| target | cMax/cMin | bound | direction |
|---|---:|---:|---|
| `runExactLadder` | **664.357** | 1.500 | faster than declared |
| `runExactFactorLadder` | **83.846** | 1.500 | faster than declared |
| `runCanonicalRepLadder` | **4.945** | 1.500 | faster than declared |

The end-to-end replacement therefore exercises the missing phase but does not
repair the model fit: its decline in `C` is larger than the former family's.
That result is retained as the evidence that modes 1 and 2 are unavailable.
The current mode-3 registrations make no parametric fit claim.

(The historical exactification and lazy-addition figures are from the quiet
runs, the repaired fixed-field-root figure is from the root-merge fix run,
and `runAlgebraicRootsLadder` is from the fixture-corrected run.)

Read as a sensitivity check. On the uncontrolled fixture most of
`runAlgebraicRootsLadder`'s spread was the step; with bounded coefficient
height the residual is large under either evaluation and the step no longer
explains it. `runExactLadder`'s declared envelope over-predicts by roughly
four powers of `n` under either evaluation and remains `inconclusive` in the
archived parametric verdict.
`runAlgebraicRootsLadder` was also inconclusive and is now a fixed registration
for the independent selection reasons above.
The repaired `runQAdjoinRootsLadder` smooth proxy remains within tolerance
independently of the integer-log steps. That confirms the historical
measurement was stable; it does not establish the proxy's provenance. The
fixed registration now supersedes that fitted verdict.

### Fixed registrations

All 76 fixed registrations use deterministic inputs; repeats agree whenever
the optional comparator dependency is present, and all 52 cases with a
declared `expectedHash` match it. Historical medians come from the committed
[comparator export](bench-results/hex-number-field-phase4-comparators.json),
with `runExactSelection` in the
[exactification fixed export](bench-results/hex-number-field-exactification-fixed.json),
the three mode-3 exactification cases in the
[mode-3 export](bench-results/hex-number-field-exactification-mode3-2df51cf4b.json),
and the three isolation cases in the isolation fixed exports:

| fixed target | median | observed hash | expected |
|---|---:|---|---|
| `runFixedMul` | 39.844 us | `0xc319ee2337214e59` | match |
| `runFixedInv` | 137.423 us | `0x1525969728101d06` | match |
| `runFixedMinpoly` | 4.039 ms | `0xb1ed00ebc8d039e9` | match |
| `runAddEliminant` | 5.754 us | `0xeb2eecad44116a79` | match |
| `runIsolateAdd` | 9.649 ms | `0x4367ab34a73ea4ed` | match |
| `runSelectAdd` | 11.193 ms | `0xb2956b93cac0235f` | match |
| `runLazyAdd` | 9.899 ms | `0xb2956b93cac0235f` | match |
| `runLazyAddLadder` | 4.539 s | `0xc544c942d8336f51` | match |
| `runExact` | 1.421 ms | `0xafd3fbfd3a66fc82` | match |
| `runExactSelection` | 308.418 ms | `0xd5512fda51bc6ff6` | match |
| `runExactLadder` | 1.878 ms | `0xd0642a7d4df3da02` | match |
| `runExactFactorLadder` | 308.643 ms | `0xe5c33ee70736a0fb` | match |
| `runCanonicalRepLadder` | 154.045 ms | `0x1d7ae08962f9292c` | match |
| `runRoots` | 1.069 ms | `0x235b18400d87a46c` | match |
| `runQAdjoinRootsLadder` | 11.108 s (loaded host) | `0x63e9dd11895b2211` | match |
| `runAlgebraicRootsLadder` | 5.955 s | `0xb6a44b3ff493da5e` | match |
| `runPariPolmodOverhead` | 7.126 us | `0x0` | match |

The five root-representation hashes above were refreshed after HexRoots
restored its bounded local finisher. Current-tree verification observes the
new values consistently (`runExactLadder`, `runLazyAddLadder`, `runRoots`,
`runQAdjoinRootsLadder`, and `runAlgebraicRootsLadder`). The recorded table
medians remain those of the cited controlled exports for traceability; the
current one-repeat timings above supersede them when estimating present
verification wall time.
The conformance emitter also reproduces the refreshed 51-record fixture:
six box/result records carry the tighter dyadic representatives selected by
the repaired HexRoots finisher. The HexNumberFieldTower emitter reproduces its
existing 30-record fixture without changes.

The SPEC's §Complexity and Phase 4 budgets caps a compiled degree-10 field
operation at 100 ms on the reference host. `runFixedMul` is 39.844 us and
`runFixedInv` is 137.423 us, both about three orders inside that budget.

`runSelectAdd` and `runLazyAdd` produce the same hash and the same median to
within 0.1%, which is the intended reading: the SPEC asks Phase 4 to separate
eliminant construction, isolation and disambiguation, and the trio
`runAddEliminant` (5.754 us), `runIsolateAdd` (9.649 ms) and `runSelectAdd`
(11.193 ms) does that. Construction is three orders below isolation, and
operation-ball disambiguation adds 1.5 ms on top of isolation — about 16%.
Isolation dominates the lazy-addition cost.

## Comparator ratios

The library SPEC declares one external comparator, **PARI/GP via cypari2**,
class `informational`, scoped to the fixed-field arithmetic bench targets.
PARI's `t_POLMOD` arithmetic (`Mod(a, m) * Mod(b, m)` and `Mod(a, m)^(-1)`) is
the callable PARI surface computing exactly `QAdjoin` multiplication and
extended-gcd inversion in `ℚ[x]/(m)`. It is wired as a persistent-subprocess
process call through `scripts/oracle/pari_bench_driver.py` and
`Hex/BenchOracle/Pari.lean`, with per-rung fixed Lean/PARI registration pairs
on identical deterministic inputs.

`libraries.yml` declares no second comparator, so
`SPEC/benchmarking.md` §Headline reports requires no comparator-runtime plot.

**Differential correctness.** Both sides hash the identical reduced rational
coefficient vector, so `compare` joins them on result hashes. Every shared
rung agrees, which makes this comparator a cross-implementation conformance
check as well as a timing one.

**Per-call overhead.** `runPariPolmodOverhead` issues one `polmod`-family
request whose PARI-side work is a constant `0`, so it measures the JSON
request/reply round trip alone. The multiplication export records **7.126 us**;
the clean-tree inversion rerun records **7.063 us** (min 6.775 us, max 7.173
us across five repeats). Overhead is at most 22% of the PARI wall
time on the smallest rung of either family and under 4% on the largest, so
every rung clears the 50% floor `SPEC/benchmarking.md` sets for the eligible
range, and every rung is far inside the 10 s hard ceiling and the 1 s soft
target. Both raw and overhead-adjusted ratios are recorded below; the adjusted
figure subtracts only that request/reply floor, leaving serialization and
PARI-side polynomial construction charged to PARI.

**Eligible range and rung density.** `SPEC/benchmarking.md` warns that a
doubling-only schedule usually does not give enough eligible rungs to read a
trend, and both families here cross the ratio 1 inside the measured range —
a claim three points cannot support. The registered schedules are therefore
densified with in-fill rungs: multiplication at `n = 4, 6, 8, 12, 16, 20`
and inversion at `n = 4, 6, 8, 10, 12, 16`, each bracketing its crossover.

The local single-root fixture removes the former smoke-cost constraint. The
registered comparison domains now restore multiplication at `n = 20` and
inversion at `n = 16`, giving six rungs in each family. The original five-rung
comparator export and the committed
[endpoint supplement](bench-results/hex-number-field-single-root-comparators.json)
supply the multiplication rows. The clean-tree
[Phase-4 completion rerun](bench-results/hex-number-field-phase4-final-inversion-comparators.json)
supplies all six normalized-inversion rows and the current overhead probe.
Before the three exactification registrations
were added, a full `verify` of those 43 registrations, including PARI,
completed locally in 0.379 s; the four exactification targets verify together
well inside the suite's 360 s hard cap, and the three current mode-3 targets
pass their named smoke verification.

Ratios are quoted as PARI wall time divided by Hex wall time, so a value above
1 means Hex is faster.

### QAdjoin multiplication against PARI `Mod(a, m) * Mod(b, m)`

| n | Hex | PARI | driver overhead as share of PARI | canonical hash | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---|---:|---:|
| 4 | 7.399 us | 39.058 us | 18.2% | `0xdbf17509eb46ddc0` | 5.279x | 4.316x |
| 6 | 17.332 us | 40.824 us | 17.5% | `0x2cf024c7e6988530` | 2.355x | 1.944x |
| 8 | 30.356 us | 57.391 us | 12.4% | `0x195da6835711d63` | 1.891x | 1.656x |
| 12 | 67.972 us | 70.731 us | 10.1% | `0xffbc782c4aba338b` | 1.041x | 0.936x |
| 16 | 120.729 us | 89.841 us | 7.9% | `0x5e40c901cf3a60b9` | 0.744x | 0.685x |
| 20 | 189.299 us | 72.142 us | 9.9% | `0xa6b61e5f0a5bbec9` | 0.381x | 0.343x |

### QAdjoin inversion against PARI `Mod(a, m)^(-1)`

| n | Hex | PARI | driver overhead as share of PARI | canonical hash | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---|---:|---:|
| 4 | 23.852 us | 33.126 us | 21.3% | `0xb8302e29a4df3f41` | 1.389x | 1.093x |
| 6 | 65.904 us | 52.177 us | 13.5% | `0xc80c3d019e0b9e4c` | 0.792x | 0.685x |
| 8 | 131.609 us | 214.185 us | 3.3% | `0xd16df20a45d683c7` | 1.627x | 1.574x |
| 10 | 222.623 us | 212.071 us | 3.3% | `0x7d0941f1c8c5f9e8` | 0.953x | 0.921x |
| 12 | 336.255 us | 236.367 us | 3.0% | `0x7776688d262fc467` | 0.703x | 0.682x |
| 16 | 709.281 us | 479.138 us | 1.5% | `0x5820b68b7d69021d` | 0.676x | 0.666x |

### Trend

Both ratios decline over their full measured ranges: multiplication from
5.279x at `n = 4` to 0.381x at `n = 20`, crossing 1 just past `n = 12`
(1.041x raw, 0.936x adjusted); normalized inversion from 1.389x at `n = 4`
to 0.676x at `n = 16`, with the final raw crossover between `n = 8` and
`n = 10`. The inversion curve remains non-monotone because PARI has a sharp
cost step between `n = 6` and `n = 8`.

For **multiplication** the decline is PARI's fixed per-call marshalling being
amortised, not an algorithmic-class difference. Fitting each side's growth
across the six rungs, with the 7.126 us driver floor subtracted from PARI:

- Hex grows as `n^2.01` — its declared `n^2` model, measured on the same
  inputs as the ladder.
- PARI's net cost grows as `n^0.58`, and its net times are 31.9, 33.7, 50.3,
  63.6, 82.7 and 65.0 us.

A sub-linear exponent means PARI's `t_POLMOD` multiplication is not what is
being timed: at these degrees the cost is building and reading back the
`O(n)`-coefficient objects, which cypari2 charges per coefficient. The
comparison does not yet reach degrees where PARI's arithmetic dominates its
own marshalling, so the multiplication ratio is orientation only. That is
consistent with the SPEC's declared expectation for this comparator — "the
constant-factor gap is structural rather than algorithmic" — and it is why
this comparator is `informational` rather than `gating`.

For **inversion**, the current numbers describe the same monic-normalized chain
as the scientific ladder. Both sides do substantial work at every rung. A
descriptive fit over this short crossover range gives:

- Hex grows as `n^2.43`.
- PARI's net cost grows as `n^2.13`, with net times 26.1, 45.1, 207.1, 205.0,
  229.3 and 472.1 us.

The Hex exponent is not a replacement complexity claim: these six small
comparator rungs span the lower-order transition that the scientific
`n²(n+7)` registration models explicitly, whereas that ladder continues to
`n = 96`. The comparator fit is orientation only. At `n = 16`, normalized Hex
inversion now takes 709.281 us instead of the former export's 1.478 ms while
preserving the same canonical hash. This removes the obsolete pre-repair trend
from the Phase-4 verdict without changing the SPEC's conservative
`O(n³ log n)` worst-case statement.

The `n = 6` and `n = 8` inversion rungs are non-monotone (0.792x then 1.627x)
because PARI's own net cost jumps from 45.1 us to 207.1 us between them while
Hex's rises smoothly; that is a PARI-side discontinuity and no claim here
rests on those two points.

### Absence declarations retained

The per-library SPEC declares three surfaces with no comparable PARI unit
surface, all with the reason
`no-comparable-surface-in-named-comparator`, and this report changes none of
them: factorization-lazy and canonical arithmetic (PARI has no certified lazy
algebraic-number type), exactification (PARI exposes rational polynomial
factorization but no unit function certifying the minimal polynomial of a root
given an isolating region), and the root APIs (`nfroots`/`nffactor` return
only roots inside the number field, `polroots` returns uncertified floating
approximations). The measurements above cover exactly the two surfaces PARI
does expose.
## Profile

samply 0.13.1 sampled at 999 Hz on the same `chungus2` hardware (Linux x86-64,
AMD EPYC 9455 48-Core Processor, 96 logical CPUs), Lean 4.34.0-rc2, LeanBench
0.1.0. The normalized-inversion profile uses clean source commit `c94811435`.
The five original profiles use source commit `066f6fc29` (with the
fixture-corrected algebraic-roots profile noted below); the replacement
exactification profile uses `a20d30552`, and the repaired fixed-field-roots
profile uses implementation commit `4a827ea546`. Fresh fixed exactification,
certification, and canonical-representation profiles use `1e5cb8472`. Every fixture is
deterministic and no fixture is randomised: the arithmetic operands come from
`denseRatCoeffs` at salts 3 and 7 (and 5 for inversion), and the remaining
families are the fixed polynomials named in the bench source. No runtime
oracle participates in any profiled route.

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runQAdjoinMulLadder     16 5000000000
# Current monic-normalized inversion implementation:
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runQAdjoinInvLadder     64 5000000000
# Historical parametric invocations, before the corresponding fixed-mode
# replacements (and, for exactification, the family replacement):
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runLazyAddLadder         8 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runExactLadder           8 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runQAdjoinRootsLadder    6 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runAlgebraicRootsLadder  6 5000000000
# After replacing the exactification family:
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runExactLadder           6 5000000000
# Re-run after the cross-component gcd guard:
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runQAdjoinRootsLadder    6 5000000000
# Current fixed mode-3 registrations (fixed child dispatch, parameter label 0):
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runExactLadder            0 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runExactFactorLadder      0 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runCanonicalRepLadder     0 5000000000
```

The profiling helper currently emits parametric child arguments. For these
three local fixed runs only, its child argv used the harness's equivalent
`--fixed --repeat-index 0 --min-total-nanos 5000000000` form, and the pinned
`lean-bench` fixed child was instrumented with the same opt-in
`withSidecarIfEnabled` wrapper already used by its parametric child. That
instrumentation records boundaries only; it does not alter the benchmark body
or the timed fixture. Both temporary tooling changes were removed after the
profiles.

Each summary used
`python3 scripts/profile/summarize_profile.py --thread hexnumberfield_bench`.
Raw filtered `*.json.gz` artefacts stay developer-local under `/tmp` as
`SPEC/profiling.md` requires; their local paths are
`/tmp/hex-profile-<target>-<param>.json.gz`.

The original five family profiles, replacement exactification profile,
repaired fixed-field-roots profile, and three current fixed exactification
profiles all pass calibration, confidence and the ±5 ms sensitivity check:

| family | case | retained / rejected | calibration residual | leaf cost | classified |
|---|---|---:|---:|---|---:|
| `qadjoin-arithmetic` | `runQAdjoinMulLadder` n=16 | 3,938 / 4,750 | 0.755 ms | allocation 37.79%, GMP 37.51%, Lean runtime 23.72%, own code 0.74% | 99.75% |
| `qadjoin-arithmetic`, normalized inversion | `runQAdjoinInvLadder` n=64 | 4,241 / 23 | 0.411 ms | allocation 19.52%, GMP 59.96%, Lean runtime 20.16%, own code 0.21% | 99.86% |
| `lazy-arithmetic` | `runLazyAddLadder` n=8 | 25,651 / 153 | 0.293 ms | allocation 50.31%, GMP 32.79%, Lean runtime 13.61%, own code 0.58% | 97.28% |
| `exactification-selection` | former `runExactLadder` n=8 | 5,334 / 488 | 0.574 ms | allocation 43.74%, GMP 29.04%, Lean runtime 18.77%, own code 1.78% | 93.33% |
| `exactification-factorization` | `runExactLadder` n=6 | 4,426 / 11,330 | 0.807 ms | allocation 34.86%, GMP 10.85%, Lean runtime 43.20%, own code 9.60% | 98.51% |
| `exactification-mode3` | fixed `runExactLadder` | 15,342 / 10 | 1.324 ms | allocation 37.28%, GMP 11.04%, Lean runtime 41.19%, own code 9.54% | 99.05% |
| `exactification-certification-mode3` | fixed `runExactFactorLadder` | 9,975 / 339 | 0.858 ms | allocation 45.03%, GMP 28.81%, Lean runtime 24.41%, own code 1.61% | 99.87% |
| `canonical-representation-mode3` | fixed `runCanonicalRepLadder` | 10,983 / 169 | 0.994 ms | allocation 43.29%, GMP 29.04%, Lean runtime 25.99%, own code 1.59% | 99.91% |
| `fixed-field-roots` | `runQAdjoinRootsLadder` n=6 | 97,109 / 7 | 0.325 ms | allocation 52.60%, GMP 33.21%, Lean runtime 11.54%, own code 0.42% | 97.77% |
| `fixed-field-roots`, repaired | `runQAdjoinRootsLadder` n=6 | 9,353 / 10 | 0.616 ms | allocation 48.57%, GMP 33.55%, Lean runtime 14.06%, own code 0.71% | 96.89% |
| `algebraic-poly-roots` | `runAlgebraicRootsLadder` n=6 | 5,965 / 9 | 0.633 ms | allocation 53.80%, GMP 30.76%, Lean runtime 12.04%, own code 0.54% | 97.14% |

The rejected counts are the untimed fixture preludes, which the filtering
postprocessor excludes by construction. The arithmetic profile predates the
single-root repair, so its rejected samples include the former 4.9 s
all-roots fixture; that prelude is outside the retained timed region. The hard
historical exactification fixture also
does substantial enclosing-polynomial isolation before its five timed
regions; despite that large rejected prelude, its 4,426 retained samples,
0.807 ms residual, and sensitivity comparison all pass the postprocessor's
confidence checks. The categorizer counts the top-level compiled `Dyadic`
helpers as Lean standard-library code, consistently with its existing
`Int`, `Rat`, and collection handling; this accounts for the corrected 98.51%
classification.

The current fixed inputs require no isolator prelude. Their rejected samples
are profiler startup and autotune gaps outside recorded timed regions; all
three retain roughly ten thousand or more samples with sub-1.4 ms calibration
residuals and pass the sensitivity check.

"Own code" is under 2% in the original five profiles and 9.60% in the hard
exactification family; most leaves are still GMP entry points,
`malloc`/`free`, or Lean runtime primitives reached from `Hex.*` frames. The
inclusive ranking below identifies the hot paths.

### `qadjoin-arithmetic` — both registered phases attribute cleanly

| share | function |
|---:|---|
| 99.85% | `Hex.QAdjoin.mul` |
| 54.34% | `Hex.DensePoly.mulImpl` |
| 45.35% | `Hex.DensePoly.divMod` → `divModArray` 45.07% → `subtractScaledShiftStep` 42.38% |

This is exactly what the `runQAdjoinMulLadder` derivation describes: dense
schoolbook multiplication of two degree-`(n-1)` operands, then reduction of the
degree-`(2n-2)` product modulo `X^n - 2`. The two phases are 54% and 45% of the
call and both are inside the registered target. Nothing here is unattributed.

The fresh normalized-inversion profile records the other changed arithmetic
route:

| share | function |
|---:|---|
| 93.21% | `Hex.QAdjoin.inv` |
| 93.11% | `Hex.DensePoly.xgcdLeftMonic` / `xgcdLeftMonicAux` |
| 37.18% | `Hex.DensePoly.mulImpl` |
| 25.89% | `Hex.DensePoly.divMod` / `divModArray` |
| 25.61% | `Hex.DensePoly.subtractScaledShiftStep` |
| 21.81% | `Hex.DensePoly.scaleImpl` |

The monic-normalized extended-gcd chain is the whole registered
`runQAdjoinInvLadder` operation. Its polynomial multiplication, division,
subtraction, and normalization substeps therefore map directly to that target.
GMP accounts for 59.96% of leaves, led by rational-normalization gcds, which is
consistent with the report's explicit warning that the finite-word limb proxy
does not model gcd internals. The profile exposes no dominant phase outside the
registration, so the Attribution rule is satisfied without weakening the
separate worst-case SPEC bound. The raw local profile is
`/tmp/hex-profile-runQAdjoinInvLadder-64.json.gz`; its 4.245 s timed region,
4,241 retained samples, 0.411 ms calibration residual, confidence check, and
±5 ms sensitivity check all pass.

### `lazy-arithmetic` — attributes to isolation, as declared

| share | function |
|---:|---|
| 92.11% | `Hex.AlgebraicRoot.ofEliminant?` |
| 92.11% | `Hex.isolate` / `isolateLoop` |
| 86.32% | `Hex.Component.refineAll` / `IsolationLoop.next` |
| 84.83% | `Hex.taylor` |

The former parametric `runLazyAddLadder` derivation correctly identified
isolation at separation depth as dominant, although its scaling model was not
supported. Eliminant construction is the 5.754 us `runAddEliminant` fixed case
against a 46 s call, and 92% of the call is inside `isolate`. The replacement
fixed registration keeps this phase covered without making an asymptotic claim.

### `exactification-selection` — certification, not factorization evidence

| share | function |
|---:|---|
| 95.63% | `Hex.AlgebraicRoot.exact?` |
| 95.58% | `Hex.AlgebraicRoot.exactFactor?` |
| 95.28% | `Hex.isolate` / `isolateLoop` |
| 47.39% | `Hex.AlgebraicNumber.canonicalRep?` / `ofNormalized?` |

The former `runExactLadder` declared the classical BHKS factorization bound
`n^9 + n^7 log^2 n`. The Berlekamp–Zassenhaus factorization does not appear in
the ranking at all. The cost is `exactFactor?`'s re-isolation of the candidate
factors at separation depth plus `canonicalRep?`'s canonical re-isolation —
that is, the certification work `exact?` does *after* factoring. This is why
the declared envelope over-predicts by `n^4.14`. This family is now the fixed
`runExactSelection` case, while `runExactFactorLadder` and
`runCanonicalRepLadder` register the two dominant certification phases.

### `exactification-mode3` — factorization is not controlling

| share | function |
|---:|---|
| 83.01% | `Hex.AlgebraicRoot.exactFactor?` |
| 77.19% | `Hex.isolate` / `isolateLoop` |
| 38.53% | `Hex.AlgebraicNumber.canonicalRep?` |
| **18.04%** | `Hex.ZPoly.factorize` |

At six quadratic factors, all BZ calls together account for 18.04% of the
whole exactification call: that inclusive frame contains both the enclosing
factorization and the candidate irreducibility checks. Certification and
candidate re-isolation remain more than four times larger, so the published
BHKS factorization bound cannot support mode 2 for this end-to-end family.

### Fixed certification phases — isolation controls both

| share | `runExactFactorLadder` | `runCanonicalRepLadder` |
|---:|---:|---:|
| registered operation | 95.77% | 96.27% |
| `Hex.isolate` / `isolateLoop` | 95.46% | 96.27% |
| `Hex.Component.refineAll` | 87.10% | 87.88% |
| `Hex.exactRootFree` | 84.34% | 85.20% |
| `Hex.taylor` | 77.35% | 78.18% |
| nested `canonicalRep?` | 47.63% | 96.27% |

These fresh profiles confirm the premise used before measurement: the
executable all-roots isolator controls both certification operations. No
published upper bound has been established for this executable, and its SPEC
contract is explicitly heuristic. The old `n⁵ log² n` declarations therefore
cannot become mode-2 claims merely because both operations are faster than
them. The fixed hard cases preserve the controlling paths and enforce 2 s and
1.1 s zero-grace whole-child budgets instead.

### `fixed-field-roots`, before the fix — 83% was duplicate removal

| share | function |
|---:|---|
| 90.65% | `Hex.QAdjoin.roots?` |
| 83.04% | `Hex.QAdjoin.Roots.mergeRootList` → `mergeRoot` → `sameValue?` |
| 83.04% | `Hex.AlgebraicRoot.exact?` (reached from `sameValue?`) |
| 41.49% | `Hex.AlgebraicNumber.canonicalRep?` |
| **7.61%** | `Hex.QAdjoin.Roots.componentRoots?` |

At that source commit, the `runQAdjoinRootsLadder` derivation declared that isolation of the
degree-`2n` norm eliminant is the ceiling. That whole phase — norm eliminant,
isolation, disambiguation — lives inside `componentRoots?` and is **7.61%** of
the call. The double resultant `evalEliminant`, which the derivation singles
out as lower order, never enters the ranking (`retainZero?` is 0.67% and
`evalBall?` 0.66%), so that part of the claim holds but is not where the time
went.

The time goes to the final duplicate-removal pass. `mergeRoot` compares
candidates with `sameValue?`, and `AlgebraicRoot` equality takes its slow path
whenever the stored polynomials differ — the SPEC at that source commit said
so in §Equality and
zero: "Otherwise exactify both roots and use canonical `AlgebraicNumber`
equality. The second path can factor twice and is not a fast arithmetic
primitive." The family `g^2 * (X - 1)` produces two Yun components with
different norm eliminants, so every cross-component comparison pays a full
`exact?`. That is both the Attribution-rule violation and the mechanism behind
this ladder's slower-than-declared verdict.

### `algebraic-poly-roots` — the contrast that confirms the mechanism

| share | function |
|---:|---|
| 91.87% | `Hex.isolate` / `isolateLoop` |
| 91.45% | `Hex.QAdjoin.roots?` |
| 91.45% | `Hex.QAdjoin.Roots.componentRoots?` |
| 82.90% | `Hex.taylor` |

The same `QAdjoin.roots?` entry point, profiled on an input with a single
squarefree component, spends 91.45% in `componentRoots?` and never reaches
`mergeRoot`. Isolation really is the cost here, as the shared derivation
claims. The difference between this profile and the previous one is the
cross-component merge, which is what makes the fixed-field family's residual a
finding rather than noise.

`runComponentRoots` now registers that dominant phase directly on the exact
profiled repeated degree-six component over the same quadratic field. Its companion
`runNormEliminant` and `runEvalEliminant` targets expose the two separable
resultants even though neither entered the dominant inclusive ranking.

### `fixed-field-roots`, repaired — isolation is now the cost

| share | function |
|---:|---|
| 92.96% | `Hex.QAdjoin.roots?` |
| 92.94% | `Hex.QAdjoin.Roots.componentRoots?` |
| 85.01% | `Hex.isolate` / `isolateLoop` |
| 78.37% | `Hex.taylor` |
| 7.52% | `Hex.retainZero?` |
| 7.43% | `Hex.QAdjoin.Roots.evalBall?` |

`mergeRootList`, `sameValue?`, and `AlgebraicRoot.exact?` no longer appear in
the inclusive ranking. Distinct enclosing polynomials now take a rational gcd
first; this family's linear and degree-`2n` component eliminants are coprime,
so every cross-component comparison returns false without factorization,
re-isolation, or canonicalization. The profile has moved from 83.04% merge /
7.61% component construction to no measurable merge / 92.94% component
construction. The phase named by the corrected ladder derivation is therefore
the measured dominant cost, not an inference from elapsed time. The current
fixed-mode rationale uses that attribution to identify what the canonical case
exercises; it does not infer an asymptotic model from the profile.
The `runComponentRoots` registration turns that attribution into a directly
named fixed measurement rather than leaving it implicit inside the end-to-end
roots target.

This family measures the new coprime-gcd exit that fixes the observed
pathology. If distinct enclosing polynomials share a nonconstant factor,
comparison still pays for the rational gcd before the existing two-root
exactification fallback; that branch is semantically covered but is not a
performance claim of this ladder.

## Reproduction

The exact scientific, comparator, and profiling commands appear with the
corresponding evidence above. All fixtures are deterministic, so no seed is
required. The table below pins the committed raw timing exports; sampling
profiles remain developer-local as required by `SPEC/profiling.md`.

### Artefact traceability

| artefact | source commit | host state | SHA-256 |
|---|---|---|---|
| [`bench-results/hex-number-field-phase4-final-inversion.json`](bench-results/hex-number-field-phase4-final-inversion.json) | `c94811435`, clean tree; final five-trial normalized-inversion ladder | idle | `5365e22a76a261ff3807521823315e1fe0a3cd7a82d112b8cb49462da84629ff` |
| [`bench-results/hex-number-field-phase4-final-inversion-comparators.json`](bench-results/hex-number-field-phase4-final-inversion-comparators.json) | `c94811435`, clean tree; current inversion pairs plus overhead | idle | `64b71bf96b66b0626defd7d7dbb6b89c9ea36c22f78c0c08af8acd562bf71699` |
| [`bench-results/hex-number-field-api-surface.json`](bench-results/hex-number-field-api-surface.json) | `5010a63ba`, clean tree; all 13 current parametric registrations | variable scheduler load | `b0d0a48449f71a8b8cd7f924d8a1643c53a48e05936cfff6e440f7e6766f43a2` |
| [`bench-results/hex-number-field-root-merge-current.json`](bench-results/hex-number-field-root-merge-current.json) | `2500076f9`, clean tree; authoritative three-trial merge rerun | variable scheduler load | `4c463ec14ed02a80fba3dc726458d3aad1822fb9cf6c6a31955756b2a09ccf0e` |
| [`bench-results/hex-number-field-api-surface-fixed.json`](bench-results/hex-number-field-api-surface-fixed.json) | `c7cfc4de4`, clean tree; all 35 newly added fixed registrations | idle | `6d022a22bca113cdd64e9db2d9fe8e2112100bf0bbe270fbf289c87e47d799d0` |
| [`bench-results/hex-number-field-api-model-review.json`](bench-results/hex-number-field-api-model-review.json) | `e7f5ed66b`, diagnostic audit tree before demotion | idle | `48ddca68217138efdeadcc1b5c7bde4d349b9c186fa396859809dfee9aabc320` |
| [`bench-results/hex-number-field-api-surface-of-array.json`](bench-results/hex-number-field-api-surface-of-array.json) | `22e2f31a0`, dirty audit tree; superseded by the clean current API-surface export | idle | `2ae9e42471f1359eda7493843ab10c874417e5204346e2c4bc6f8045c6cc6ddc` |
| [`bench-results/hex-number-field-phase4-scientific.json`](bench-results/hex-number-field-phase4-scientific.json) | `066f6fc29` | loaded (load average 105 to 150) | `3948bbb7107d96e7af56edcf2497b52e2b2a34f4d89376b93cc477c0f8a6517d` |
| [`bench-results/hex-number-field-phase4-scientific-quiet.json`](bench-results/hex-number-field-phase4-scientific-quiet.json) | `066f6fc29` | idle (load average 1.5) | `186d25381ce87fa6c4f4d0b6d51c03eed8f865a120dd83a5ac278c8d34be6408` |
| [`bench-results/hex-number-field-phase4-scientific-quiet-heavy.json`](bench-results/hex-number-field-phase4-scientific-quiet-heavy.json) | `a2b70b949` | idle | `71b42aaa8b45ce25f450f7b7ad8a0d537c9e2220bdddd8ab79fcb5cc51c477b3` |
| [`bench-results/hex-number-field-phase4-comparators.json`](bench-results/hex-number-field-phase4-comparators.json) | `9ae125c67`, clean tree | idle | `fd42dda533a345815205a0de1737f95cdd9a93e02ae355d78be31cb0bac62041` |
| [`bench-results/hex-number-field-phase4-scientific-fixture-corrected.json`](bench-results/hex-number-field-phase4-scientific-fixture-corrected.json) | the fixture correction (this branch head) | idle | `6a176e351a46436d7c6ae47fff666f62c85b09c549d3d3866697ae3fded4fa6a` |
| [`bench-results/hex-number-field-single-root.json`](bench-results/hex-number-field-single-root.json) | `4ae98f272`, clean tree | idle | `8fc1546f02fe7bf42c4f939ab0cefc07fe9cd2a1d00006350cbe50b71db508ba` |
| [`bench-results/hex-number-field-single-root-comparators.json`](bench-results/hex-number-field-single-root-comparators.json) | `96e0fd7ee`, clean tree | idle | `1243e69ce4256f4470700b43aba55fcb8d6ba1d30faa5ff38b1ddea0803133d4` |
| [`bench-results/hex-number-field-exactification-audit.json`](bench-results/hex-number-field-exactification-audit.json) | `e51768c1b` (end-to-end) / `b3249f4f8` (phases), clean trees | idle | `8b26157ac30a0ed58ef836e7abba04fa3aa2041e07f24a6b75e84c6aa89b41a8` |
| [`bench-results/hex-number-field-exactification-fixed.json`](bench-results/hex-number-field-exactification-fixed.json) | `b42dcf205`, clean tree | idle | `be2630c422f5da5defccffdc57a7087d05edfd3cbba7882dd81e119d4e978e8c` |
| [`bench-results/hex-number-field-exactification-mode3-2df51cf4b.json`](bench-results/hex-number-field-exactification-mode3-2df51cf4b.json) | `2df51cf4b`, clean tree | idle | `d67c1e2993f0765153f4f15781eda8527c1a9138b8aa427365e69e327e4cecce` |
| [`bench-results/hex-number-field-phase4-scientific-root-merge-fix.json`](bench-results/hex-number-field-phase4-scientific-root-merge-fix.json) | `8b6feb49c`, clean tree | idle | `c0dde1aed6c03d25871d5b846b62d70e864e525e48b50b8422899d66760f99ae` |
| [`bench-results/hex-number-field-qadjoin-inv-chain.csv`](bench-results/hex-number-field-qadjoin-inv-chain.csv) | `e3c3a03cb`, deterministic untimed replay | idle | `be5a0d89cc09877de5a58b54c085e671e4dd5efd4498e729762e1f4451b5179b` |
| [`bench-results/hex-number-field-qadjoin-inv-normalized.json`](bench-results/hex-number-field-qadjoin-inv-normalized.json) | `e3c3a03cb`, clean tree; overwrites the #9721 normalized-run artefact | idle | `73783f7c455f225d25fc5ff13e0889cd0cc31c64a5ef452e7267e65a86be4080` |
| [`bench-results/hex-number-field-lazy-add-fixed.json`](bench-results/hex-number-field-lazy-add-fixed.json) | `768afcd35`, clean tree | idle | `1cdd1336923271709affc22c45bf178ef6cb73ec4080b796e312fd0e06a43048` |
| [`bench-results/hex-number-field-qadjoin-roots-fixed.json`](bench-results/hex-number-field-qadjoin-roots-fixed.json) | `18a7a33d5`, clean tree | loaded (1-minute load average 61.25/96) | `8d6896cd7e48d4b59b6636f7b77786a38ce85820e9e418ba6b6386c40ffbee16` |
| [`bench-results/hex-number-field-algebraic-roots-fixed.json`](bench-results/hex-number-field-algebraic-roots-fixed.json) | `794f0ddf2`, clean tree | idle | `f5205917ef6c5095bbbaa820158e159472fb85752b7292d4b80f26b0cbb89c23` |

Ladder numbers come from the commits named in the table. Across the first four
the compiled ladder code is identical: `a2b70b949` differs from `066f6fc29`
only in two comments, and `9ae125c67` only changes comparator registrations
and their smoke cost. The fixture-corrected run is the exception and is the
reason it exists — it
supersedes the earlier `runAddEliminantLadder`, `runCommonPresentationLadder`
and `runAlgebraicRootsLadder` numbers in that historical parametric run. The
three isolation-fixed exports supersede the current timing and verdict for
`runLazyAddLadder`, `runQAdjoinRootsLadder`, and
`runAlgebraicRootsLadder`. The single-root run supersedes
the earlier three fixed-field arithmetic ladders after their domains expanded.
The exactification mode-3 export supersedes the current verdicts for all three
exactification registrations; the audit export remains their failed
parametric evidence.
Four of the five
profiles were taken from the `066f6fc29` binary; the `algebraic-poly-roots`
profile was re-taken after the fixture correction, and the hard-family
exactification profile uses `a20d30552`. The root-merge-fix export supersedes
only `runQAdjoinRootsLadder` and introduces `runMergeRootListLadder`; its
repaired profile comes from `4a827ea546`. The QAdjoin-roots fixed export then
supersedes that target's parametric verdict without superseding its repair or
profile evidence.
The Phase-4 completion inversion export supersedes the earlier normalized
inversion timing export, while the final inversion-comparator export supersedes
the pre-normalization inversion rows only; multiplication continues to use its
original comparator artefacts. The clean `c94811435` inversion profile at
`n = 64` refreshes attribution for the changed implementation.
The three current fixed exactification profiles come from `1e5cb8472` with the
instrumentation-only fixed-child sidecar hook described in §Profile.
The follow-up at `2df51cf4b` leaves the certified inputs and exactification
operations unchanged; it makes initialization lazy, strengthens result hashes,
and corrects the whole-child budgets. The fresh timing export was repeated at
that follow-up commit, while the phase attribution remains the immediately
preceding operation-identical profile evidence.
Toolchain throughout:
Lean 4.34.0-rc2, LeanBench 0.1.0, samply 0.13.1, cypari2 driving PARI through
`scripts/oracle/pari_bench_driver.py`. Host throughout: `chungus2`, Linux
x86-64, AMD EPYC 9455 48-Core Processor, 96 logical CPUs.

Every fixture in this library is deterministic; no registration draws from a
random seed, so a rung is identified by its parameter and the salt named in
the bench source rather than by a seed.

## Concerns
