# Algebraic samples for CAD and coverings

Use separate search and replay representations. Canonical `RealAlgebraicNumber`
coordinates are a working search baseline, but the certificate should carry
literal integer polynomials, dyadic root isolation data, and checked sample
substitutions. The measured sign replays stay in `ℚ[t]`, including a sample
whose two coordinates generate different quadratic fields. This does **not**
measure an automatic exporter from arbitrary canonical tuples to that format.

Keep one theory explanation as the unit of a cell certificate, with polynomial
and isolation data shared across its sign obligations. Keep its projection
support separate from the propositional clause: an explanation and a learned
resolvent are different objects. The small corpus below informs an experimental
interface; it does not establish a solver-scale clause-size distribution or
justify a fixed maximum clause width.

This is the measurement spike for [#10301](https://github.com/kim-em/hex-dev/issues/10301),
consumed by [coverings](../SPEC/future-work.md#real-arithmetic-satisfiability-by-cylindrical-coverings)
and [CAD](../SPEC/future-work.md#cylindrical-algebraic-decomposition). The
[alignment analysis](decision-procedures-alignment.md) describes the wider
algorithm choices. No projection operator, SAT core, or public certificate type
is implemented here.

## Corpus and sample definitions

Polynomials and root choices below define the samples independently of solver
heuristics. The SMT runs use the same polynomial examples, with the indicated
sign-query refutations; their search assignments need not be these selected
samples. Every second-level lift times the quadratic polynomial in `y` after
canonical substitution. All finite real roots are computed, even though one
root is selected for the next level.

| Example | Base polynomial and chosen `α` | Lift and selected `β` | Sign certified; solver instance |
|---|---|---|---|
| NLSAT | `16x³−8x²+x+16`, its unique real root in `(−1,0)` | `y²+α²−1`; negative root | `α³+2α²+3β²−5 < 0`; paper Example 5 |
| Circle/parabola | `x⁴+x²−1`; positive root | `y²+α²−1`; positive root, equal to `α²` | `β−α < 0`, also `β²+β−1 = 0`; circle and `y=x²` with `x>0, y≥x` |
| Two circles | `2x−1`; `α=1/2` | `y²+α²−1`; positive root | `β−α > 0`; unit circles centered at `(0,0)` and `(1,0)`, with `y>0, y≤x` |
| Kahan specialization | `16x²−8x−1`; positive root | `y²+(16α²−8α−3)/64`; positive root | `α²+β²−1 < 0`; ellipse `16x²−8x+64y²−3=0` outside/on the unit circle |
| Sphere section | `2x²−1`; positive root | `y²+α²−5/6`; positive root | `1−α²−β² > 0`; positive intersection of this section with `x²+y²+z²=1` |
| Tower 4 | `x²−2`; positive root | `y²−α`; positive root | `β−α < 0`; defining equations with `x,y>0, y≥x` |
| Tower 8 | `x⁴−2`; positive root | `y²−α`; positive root | `β−α < 0`; defining equations with `x,y>0, y≥x` |

The sphere additionally lifts `z²+α²+β²−1` at level 3, giving `γ=1/√6`.
The tower cases are supplemental degree cases, not attributed textbook examples.

The NLSAT equations are `f₂=x²+y²−1`, `f₃=−4xy−4x+y−1`, and
`f₄=x³+2x²+3y²−5`; Example 5 asks for `f₂<0, f₃>0, f₄<0`.
The selected algebraic boundary sample comes from Examples 1 and 3, rather than
from a solver model of the strict conjunction.
[Jovanović–de Moura, IJCAR 2012, Examples 1–5](https://dddejan.github.io/papers/jovanovic-ijcar2012.pdf).
Kahan's full problem has four ellipse parameters and two quantified coordinates.
Here its squared semiaxes and center are fixed to
`a=1/4, b=1/16, c=1/4, d=0`; these measurements do not cover the six-variable
parametric problem.
[Brown, *Improved Projection for Cylindrical Algebraic Decomposition*, §6](https://www.usna.edu/Users/cs/wcbrown/research/abstracts/Brown01b.pdf).

## Provenance and protocol

Measurements use commit `756b63dbbcc2f42b2966ca7407235d5d5b8b8d49`, Lean
`leanprover/lean4:v4.34.0`, on `chungus2`: AMD EPYC 9455, 48 cores/96 logical
CPUs, Linux `6.12.100`, x86-64. One automatic, nonblocking CPU lease selected
logical CPU 45. `LEAN_NUM_THREADS=1` and inherited affinity apply to child builds.
The experiment sources were committed and unchanged when collection started.
Collection took place on 2026-09-20. Host observations, exact commands, source SHA-256 hashes, and solver
binary hash are retained in [metadata](bench-results/cad-sample-costs/meta.json).

The runtime and paired proof measurements have four fixed trial-major rounds.
Solver counts use one fixed-seed invocation per case (`n=1`); their invocation
times include process startup and tracing, and are not comparative timings. Each fresh-module pair is adjacent;
its order alternates Literal/Replay and Replay/Literal. Only that module's
artifacts are removed, leaving imported dependencies warm. Runtime operations
use a non-inlined IO wrapper between monotonic clocks; inspection of generated
C verifies the ordering. Formatting is outside those clocks. Each process's
complete output, including partial output on failure, is retained. The process
limits are operational safeguards: 30 seconds for runtime/solver runs and
120 seconds for proof builds. Host load never rejects a sample and no quiet-core
wait or unchanged rerun is used. These are finite-case observations, not a
lean-bench asymptotic verdict or a Phase-4 claim.

[All raw observations](bench-results/cad-sample-costs/runs.jsonl) and compressed
logs are retained in the same directory. [Experiment instructions](../experiments/CadSampleCosts/README.md)
give the build, literal regeneration, pinned traced Z3 build, and collector
commands. Nothing is added to CI or a released library.

The carrier-input snapshot in that directory was added after collection;
the summarizer verifies its bytes against the source hash recorded at collection.
The original 99 observations retain axiom evidence per row and in their logs;
they predate the separate `validation.log.gz` used by the current collectors.
Historical paired measurements require the recorded source commit: the current
Replay and Transport modules have changed, as described below.

## Canonical lifting

`d/H` means minimal-polynomial degree and maximum absolute integer coefficient
of the primitive, positive-leading-coefficient canonical polynomial. Coefficient
columns describe the specialized constant coefficient; the other two
coefficients are `0` and `1`, both degree 1 and height 1 as canonical numbers.
All raw output polynomials, including both signs of a lifted root, are retained.
Each timing is the median [minimum, maximum] of all four completed observations,
in milliseconds. At level 1 the input column describes the integer polynomial;
at later levels it describes the algebraic constant coefficient.

| Example | Level | Input/coefficient d/H | Root d/H | Substitution ms | Root enumeration ms |
|---|---:|---|---|---:|---:|
| NLSAT | 1 | 3/16 | 3/16 | n/a | 10.187 [9.974, 11.934] |
| NLSAT | 2 | 3/961 | 3/49 | 35.672 [35.470, 36.334] | 5541.300 [5511.650, 5566.284] |
| Circle/parabola | 1 | 4/1 | 4/1 | n/a | 22.373 [22.271, 22.456] |
| Circle/parabola | 2 | 2/3 | 2/1 | 23.170 [22.993, 23.356] | 20.384 [20.366, 20.487] |
| Two circles | 1 | 1/2 | 1/2 | n/a | 0.368 [0.362, 0.382] |
| Two circles | 2 | 1/4 | 2/4 | 1.785 [1.779, 1.797] | 3.490 [3.473, 3.503] |
| Kahan specialization | 1 | 2/16 | 2/16 | n/a | 2.314 [2.295, 2.386] |
| Kahan specialization | 2 | 1/32 | 2/32 | 11.955 [11.881, 12.151] | 3.378 [3.352, 3.403] |
| Sphere section | 1 | 2/2 | 2/2 | n/a | 2.330 [2.318, 2.377] |
| Sphere section | 2 | 1/3 | 2/3 | 3.172 [3.140, 3.213] | 3.503 [3.490, 3.741] |
| Sphere section | 3 | 1/6 | 2/6 | 5.575 [5.532, 5.633] | 3.456 [3.446, 3.480] |
| Tower 4 | 1 | 2/2 | 2/2 | n/a | 2.372 [2.367, 2.467] |
| Tower 4 | 2 | 2/2 | 4/2 | 0.950 [0.948, 0.959] | 26.661 [26.452, 26.770] |
| Tower 8 | 1 | 4/2 | 4/2 | n/a | 29.530 [29.256, 29.860] |
| Tower 8 | 2 | 4/2 | 8/2 | 6.599 [6.557, 6.625] | 507.909 [504.204, 510.838] |

The base-root operation is `ZPoly.realAlgebraicRoots`. Substitution separately
includes canonical arithmetic; the next column times `RealAlgebraicPoly.roots`,
including its real-root filtering, exactification and sorting. Rational constant
construction and JSON formatting are outside these internal timers. No result
is a timing of native floating-point approximation.

The NLSAT lift costs 5.541 seconds despite its degree-3 output, versus 0.508
seconds for the degree-8 tower and about 3.5 milliseconds for the rationally
specialized circle, ellipse and sphere lifts. Output degree alone therefore
does not predict this pipeline's cost. Canonical substitution itself costs
23.170 milliseconds for the circle/parabola, slightly more than its root call.

## Kernel sign replay

The actual proof boundary is
[`Certificate.check`](../HexRCF/Certificate.lean) plus its soundness theorem.
The integer-polynomial carrier includes roots of *every atom* in the query,
including interval/sign conditions, not just the algebraic parameter polynomial.
The executable root-cell sign test uses a checked common-root gcd and an
adjacent open-cell sign. It is not an arbitrary Sturm–Tarski query:
[`SturmReplay.check`](../HexRCF/SturmCheck.lean) requires
`F′ = δ·s₁` with `δ>0`.

The original paired modules elaborate identical literal certificates and proofs of their
correspondence to the source formulas. Replay adds kernel reduction of the
checker, soundness, the source sign theorem, and the sample transport theorem
where applicable. They also run `#print axioms` on the new sign/result/sample
theorems; these traversals contribute to the difference. Cached dependency
messages in the raw logs are replayed output, not newly executed checks.
The reported difference is **fresh-module wall time**, including
proof construction/checking and ordinary process variation, not isolated kernel
CPU time. Reusable symbolic transport schemas and non-vacuity proofs are checked
in the warm dependency [Transport.lean](../experiments/CadSampleCosts/Transport.lean).
They are not untrusted per-sample data. All expected theorem names, including
coordinate identities, sample-existence proofs, and focused checker theorems,
are covered by the untimed validation module. Its 54 axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound` (or a subset).

`H` is the carrier's integer coefficient height; `chain bits` is the bit length
of the maximum absolute coefficient in its literal Sturm chain. The raw
[carrier metadata](../experiments/CadSampleCosts/kernel-inputs.json) also retains
chain length and nonconstant atom occurrence count (including duplicates).
The parameter column describes the defining polynomial of the supplied univariate
parameter `t`, as identified in the parameterizations below. A single nominal
degree is not a complexity model.

| Example (level 2 sign) | Parameter d/H | Carrier d/H | Chain bits | Literal s | Replay s | Paired difference s |
|---|---|---|---:|---:|---:|---:|
| NLSAT | 3/16 | 7/32 | 45 | 7.68 | 8.04 | 0.38 [0.30, 0.70] |
| Circle/parabola | 4/1 | 6/1 | 7 | 7.53 | 8.14 | 0.35 [-0.20, 0.81] |
| Two circles | 2/4 | 4/8 | 6 | 7.53 | 7.76 | 0.22 [0.10, 0.26] |
| Kahan specialization | 2/2 | 6/392 | 36 | 7.73 | 8.06 | 0.32 [-0.51, 0.40] |
| Sphere section | 4/10 | 11/50096 | 71 | 7.93 | 9.99 | 1.86 [0.96, 2.87] |
| Tower 4 | 4/2 | 6/2 | 7 | 7.78 | 8.14 | 0.55 [-0.15, 4.05] |
| Tower 8 | 8/2 | 10/2 | 8 | 8.29 | 8.04 | -0.25 [-4.99, 0.40] |
| Circle/parabola zero | 4/1 | 4/1 | 2 | 7.61 | 8.31 | 0.61 [0.00, 1.31] |

Arm columns are medians; differences are the median [minimum, maximum] of
the four **paired** Replay minus Literal observations. They are not the
difference of arm medians. All 64 fresh-module builds succeeded.

The sphere's paired overhead is 0.96–2.87 seconds, with a degree-11 carrier
and 71-bit chain coefficients. Several smaller effects are unresolved against
process variation: the circle/parabola, Kahan and tower ranges cross zero,
and Tower 8 has a negative median. Negative differences do not mean that
checking saves work. No sample was removed and no rerun was used; these data
do not support a replay degree-scaling curve or a portable per-sign budget.

### Focused kernel checking

The whole-process differences above do not isolate a kernel-cost model. The
focused measurement profiles only the `accepted : certificate.check input = true`
declaration, with literal inputs already elaborated, synchronous elaboration,
and Lean's exclusive profiler enabled. Its cumulative `type checking` category
measures kernel work from `decide +kernel`, including declaration checking.
The separate heartbeat count covers the whole declaration command, in Lean's
user-facing units of 1000 internal heartbeats; it is a deterministic work proxy
for this toolchain, not a time prediction.

Axiom traversals, soundness, source transport and Lake startup are outside this
profiled region. The current paired modules also move axiom traversals to the
untimed validator. The original paired observations are retained unchanged and
refer to their original source commit.

| Example (level 2 sign) | Parameter d/H | Carrier d/H | Chain bits | Kernel type checking ms | Command heartbeats |
|---|---|---|---:|---:|---:|
| NLSAT | 3/16 | 7/32 | 45 | 298.5 [280.0, 381.0] | 2943 |
| Circle/parabola | 4/1 | 6/1 | 7 | 254.0 [253.0, 351.0] | 2722 |
| Two circles | 2/4 | 4/8 | 6 | 143.0 [138.0, 185.0] | 1583 |
| Kahan specialization | 2/2 | 6/392 | 36 | 385.0 [354.0, 487.0] | 3483 |
| Sphere section | 4/10 | 11/50096 | 71 | 1335.0 [1320.0, 1790.0] | 11480 |
| Tower 4 | 4/2 | 6/2 | 7 | 232.5 [225.0, 303.0] | 2467 |
| Tower 8 | 8/2 | 10/2 | 8 | 334.5 [330.0, 453.0] | 3588 |
| Circle/parabola zero | 4/1 | 4/1 | 2 | 81.3 [74.3, 98.1] | 1035 |

Focused timings are median [minimum, maximum] of four completed runs. All
heartbeat counts agree exactly across rounds. Collection used commit
`a9c62664727e387330288b75325a275f9497042e` on the same host/toolchain, with
automatically leased CPU 16, on 2026-09-20. Its
[metadata](bench-results/cad-kernel-costs/meta.json),
[32 observations](bench-results/cad-kernel-costs/runs.jsonl), and complete logs
are retained separately. No sample was dropped or rerun.
Every focused maximum occurred in round 0; the recorded one-minute load fell
from 90.3 at the first observation to 57.4 at the last on this 96-logical-CPU
host. This is shared-host context, not evidence isolating a cause of the spread.

The smallest checker costs a median 81.3 ms and the sphere checker 1335 ms.
The degree-6 Kahan carrier costs 385 ms, versus 232.5 ms for Tower 4 (also
degree 6). Atom count, carrier height, and chain coefficient sizes differ,
so this comparison does not isolate their effects. These finite cases establish a practical
kernel cost for the supplied replay format; they do not measure general
primitive-element export, sign transport, or an asymptotic law.

The non-vacuous parameterizations are:

- Circle/parabola: `β=α²`; replay uses `α⁴+α²−1=0`. Its zero case checks
  `β²+β−1=0` through the same quartic relation.
- NLSAT: the circle equation gives `β²=1−α²`, so the sign polynomial is
  `α³−α²−2`. The sample transport theorem checks this substitution.
- Two circles: subtracting their equations gives `α=1/2`; replay uses
  `4β²−3=0` and `β>0`.
- Kahan: `α=(1+t)/4`, `β=t/8`, `t²=2`, `1<t<2`. The substituted circle
  polynomial has numerator `5t²+8t−60` and positive denominator 64.
- Sphere: `t=√2+√3` has `t⁴−10t²+1=0`, `3<t<4`.
  Here `α=(t³−9t)/4` and `β=(11t−t³)/6`. The checked coordinate identities
  establish `2α²=1`, `3β²=1` and positivity. In particular
  `β∉ℚ(α)`, yet this supplied representation keeps the replay in `ℚ[t]`.
- Towers: use `t=β`, `α=t²`, `t⁴=2` or `t⁸=2`, with `t>1`.

The public canonical root pipeline is not a literal kernel certificate:
`decide +kernel` on the sign of the positive result of
`ZPoly.realAlgebraicRoots [-2,0,1]` gets stuck, although compiled evaluation
returns `1`. The [reproducer](../experiments/CadSampleCosts/README.md) gives the exact diagnostic
command. The canonical constructor is sealed, and the library explicitly
notes the rational-polynomial gcd reduction boundary in
[Basic.lean](../HexNumberField/Basic.lean). Timing that compiled sign as “kernel
replay” would be incorrect.

For a general tuple, a production exporter still has to certify the primitive
representation, substitution identities and selected embeddings. An independently
supplied eliminant and a root interval do not establish that its root equals
`p(α,β)`: `t⁴−10t²+1`, for instance, has roots of both signs. Suitable evidence
includes integer-cleared cofactor identities for `fα(A(t))`, `fβ(B(t))`, and
`p(A(t),B(t))` modulo the parameter polynomial, together with certified root
selection/interval conditions. This experiment's explicit identities are not a
measurement of that general exporter. No claim about its cost is included in
the replay deltas.

## Solver clause counts

Z3 is pinned to `z3-4.15.3`, commit
`a121e6c6e95c60f50d1561f03762805dabc969e1`, built with tracing enabled.
The [patch](../experiments/CadSampleCosts/z3-trace.patch) adds trace statements
without changing solver decisions. The fixed SMT files run `simplify` followed
by `nlsat`, seed 0, with reordering and variable shuffling disabled and
`cell_sample=false` (original projection).

A **cell explanation** is one completed theory-explanation call. Its projection
count is the number of distinct primitive positive-leading nonconstant
polynomials obtained from factors enqueued by
`insert_fresh_factors_in_todo` during that call, excluding the original input
core. The retained traces and JSON preserve the original printed factors and
degrees. The table normalizes their integer content and leading sign, so `x`
and `−x` count once; the tower counts are 2 instead of 3 printed strings. A **learned
clause** is an allocation marked `learned` in the solver; it can be a resolvent
rather than the original theory explanation. The two totals need not agree.
Neither statistic is the number of cells in a full CAD or the number of clauses
surviving at solver shutdown. Per-call data and the complete explanation text
are in the raw observations and `trace-*.log.gz` files.

| Example | Levels | Input d/H | Result | Cell explanations | Primitive projected factors per explanation, in order | Learned clauses | Invocation ms |
|---|---:|---|---|---:|---|---:|---:|
| NLSAT | 2 | 3/5 | sat | 8 | 3, 2, 0, 2, 5, 0, 0, 5 | 7 | 18.096 |
| Circle/parabola | 2 | 2/1 | unsat | 3 | 0, 0, 0 | 2 | 8.726 |
| Two circles | 2 | 2/2 | unsat | 9 | 0, 1, 0, 4, 2, 2, 0, 0, 0 | 6 | 8.586 |
| Kahan specialization | 2 | 2/64 | unsat | 10 | 2, 2, 0, 0, 0, 2, 0, 0, 0, 0 | 7 | 8.446 |
| Sphere section | 3 | 2/6 | sat | 0 | n/a | 0 | 8.402 |
| Tower 4 | 2 | 2/2 | unsat | 2 | 2, 0 | 1 | 8.348 |
| Tower 8 | 2 | 4/2 | unsat | 2 | 2, 0 | 1 | 8.339 |

Across these invocations there are 0–10 cell explanations and 0–7 allocated
learned clauses, with 0–5 primitive projected factors per explanation. A zero
projection count does not mean an explanation has no polynomial support: its
input core is excluded. The sphere finishes without learning, while the NLSAT
example repeats projection support across explanations. Sharing support is
therefore worth accommodating, but its general memory benefit is unmeasured.

`d/H` in this table refers to the maximum total degree and integer coefficient
height of the denominator-cleared **input** polynomials; it is not a height
estimate for every projected factor. The operation is the complete fixed-seed
solver invocation. These small problems and one solver configuration cannot
fix a general clause-size distribution, a proof-DAG sharing policy, or a
search-memory budget.

## Representation decision and questions left open

Canonical coordinates remain useful for executable conformance and as the
measured lifting baseline. They should not be required fields of a kernel
certificate. Prefer a replay representation of defining polynomials, selected
real roots, and literal checkable arithmetic evidence; allow the compiled
search representation to evolve independently. For the corpus's explicit
primitive parameters, rational-polynomial replay is sufficient. Arithmetic in
`ℚ(α)` is not logically mandatory in the checker, but converting arbitrary
search tuples to the rational-polynomial format is an additional obligation.

The existing `AlgebraicRoot` is factorization-lazy, but its public arithmetic
still constructs eliminants and isolates roots. This run does not measure a
lazy lifting replacement or assume that the sign of an isolation's center is
a valid sign oracle. No canonical-versus-lazy speedup is inferred. For a
squarefree degree-`d` parameter with **one already isolated root**, recording
the signs of `f′, …, f⁽ᵈ⁻¹⁾` requires at most `d−1` direct sign/Tarski
queries; the sign of `f⁽ᵈ⁾` is known from the leading coefficient. One more
query determines the sign of a supplied evaluation polynomial. Thus the
parameter degrees 2, 3, 4 and 8 suggest at most 2, 3, 4 and 8 queries in
that restricted model. These are query counts, not measured costs or bounds
for constructing a Thom encoding of an unisolated root set. This tree has no
general Sturm–Tarski or BKR implementation to time.

The coverings SPEC can leave these choices open behind an explicit checked
interface:

1. Search storage: canonical values, lazy isolated roots, a shared number
   field, or a tower; and when to pay for exactification/common-field conversion.
2. The general literal substitution/exporter checker and its termination,
   coefficient-growth and root-selection evidence. The present handwritten
   corpus does not settle its implementation or cost.
3. Interval-only proofs for separated nonzero signs versus exact zero tests.
   Rational enclosures can settle a strict sign without an eliminant once the
   evaluated interval excludes zero; neither a refinement policy nor the
   frequency of that fast path is measured here.
4. Thom encodings, Tarski-query implementation, derivative-sign sharing and
   the degree/height regimes where they beat isolated-root replay.
5. Per-explanation versus shared polynomial/isolation storage, and the final
   relation between cell explanations, learned resolvents and resolution replay.
   Keep counts distinct and avoid a fixed clause-width assumption.
6. Nullification, general algebraic-coefficient lifts, higher parameter counts
   and variable-order sensitivity. The fixed ellipse and rationally simplifying
   sphere section are not coverage of those cases.

The SPEC should fix the semantic obligations now (correct root identity,
substitution, signs and cell coverage) without fixing a canonical-number payload
or claiming that the costs of the missing general conversion have been measured.
