# Sturm query bit-cost models

These models concern integer/dyadic computations, with binary integers and
64-bit GMP limbs. Scalar ring-operation counts alone do not predict wall time
when coefficient sizes grow. Query-degree declarations are two-sided and
family-specific. Deferred-normalization head-degree replay uses the one-sided
upper-bound mode below; older two-sided replay hypotheses are retained as
historical evidence.
The retained original declarations and samples remain in
[the performance report](hex-sturm-performance.md).

## Growing query degree

Fix `P = X² − 2`, `F = Xᵐ + 1`, even `m = 2r`, and endpoints `−2,2`.
The initial dividend is `2X^(2r+1) + 2X`. Its monic division has multiplier
one, quotient

```
2 ∑ (j = 0,…,r−1) 2ʲ X^(2(r−j)−1)
```

and remainder `(2^(r+1) + 2)X`. The quotient's nonzero coefficients have
bit lengths `2,3,…,r+1`, totaling `r(r+3)/2`. Thus materializing the
implemented output alone requires quadratic binary storage.

`DensePoly.pseudoDivMod` computes each active coefficient using at most two
correction terms. The divisor's coefficients are `−2,0,1`; its leading
coefficient powers are all one. Each nonzero arithmetic operation is an
addition or multiplication by a fixed small integer on a coefficient of at
most linear bit length. Summing these costs gives Θ(m²) binary work, with
Θ(m) array and dispatch work. Output hashing also scans at most quadratic
bits. There is no multiplication of two independently growing integers in
this recurrence.

`runInitialHigh` consumes and hashes this actual quotient. `runIntegerHigh`
materializes it in the producer; content normalization reduces the linear
remainder to `X`, leaving a fixed-length query chain. Its squarefree check
has fixed input. `runReplayHigh` checks the stored quotient by multiplying
it with a fixed quadratic; its remaining chain and endpoint checks have
fixed degree. All three therefore declare **m²** bit work.

The validation ladder is `4096,8192,16384,32768,65536`, four trial-major
trials, a 100 ms tuning target, and a 30-second operational per-call cap.
The quotient ranges from about 0.25 MiB to 64 MiB of coefficient bits;
peak allocations include additional arrays and copies. This ladder exercises
multiword arithmetic instead of the original small-integer transition.
The cap is a safeguard, not a scientific absolute budget. All samples and
source/executable hashes must be retained. No parameters or exponents are
selected from the new observations.

The rational registration also requires correction: its fixed-quadratic
division computes the same growing numerators with denominator one. Its
original finite-ladder linear pass supplies no unbounded bit-cost claim.
`runRationalHigh` declares m² on `131072,262144,524288,1048576`, four trials,
a 100 ms tuning target and a 120-second operational cap.

The wider validation ladder is `65536,131072,262144,524288`, with the same
quadratic declaration and trial settings. Its largest quotient contains
about 4 GiB of coefficient bits; temporary storage can be several times that
size. The smaller-ladder inconclusive results are retained. Extending the
schedule does not change the model or discard those observations.

The final extension is `131072,262144,524288,1048576`; the largest quotient
is approximately 16 GiB, with several simultaneous copies/temporary arrays
possible. The operational cap is 120 seconds to accommodate that allocation
and arithmetic volume. The model remains m², with four trials and all earlier
samples retained. This is a schedule extension, not an unchanged rerun.

## Earlier head-degree replay: normalization at every operation

For `P=T_n`, query `1`, the non-head derivative-chain entries are positive
primitive multiples of `U_k`, `k=n−1,…,0`. Explicitly,

```
U_k = ∑ (j=0,…,⌊k/2⌋) (−1)^j binomial(k−j,j) (2X)^(k−2j).
```

Its content is `2^v₂(k+1)`. In particular primitive normalization removes
only O(log k) binary zeros. For a linear number of indices `j < k/4`, the
primitive coefficient has Θ(k) bits and Θ(k) trailing zeros. There are
Θ(k) nonzero coefficients in an entry of degree k.

`ZPoly.evalDyadic` converts every coefficient with `Dyadic.ofInt`, hence
`ofIntWithPrec`. Lean 4.34.0's `Int.trailingZeros` repeatedly computes
remainder and division by two; it does not call a constant-time machine
count-trailing-zeros primitive on an entire multiprecision integer. For a
b-bit coefficient with t trailing zeros, the successive divisions process
Θ(∑(s<t) (b−s)) bits. The coefficients above therefore require Θ(k²)
binary work each, Θ(k³) per polynomial and Θ(n⁴) across the chain. This
lower bound holds before accounting for Horner additions, at either endpoint.

The other replay work stays within O(n⁴) bit work: there are O(n²)
coefficient operations on O(n)-bit integers; the schoolbook upper bound
for each scalar product is O(n²). Horner accumulators at fixed endpoints
also have O(n) bits. This yields the **n⁴ binary-work bound** for `runReplay`.
It characterizes the current upstream dyadic normalization algorithm, not
an optimal bound for integer Horner evaluation or a claim about every backend.

The quartic wall-time hypothesis uses the validation ladder `128,256,512,1024`, four trial-major
trials, a 100 ms tuning target and a 600-second operational per-call cap.
Smaller degrees need not be in the quartic regime: loop dispatch alone
contributes cubic work, and limb costs introduce further lower-order terms.
The machine word width does not determine the ratio between dispatch and
limb-processing time; consequently no fitted cubic/quartic mixing coefficient
is part of the declaration. The model and ladder precede new replay timings.

The untimed checker `scripts/bench/sturm_bit_costs.py` compares these formulas
with every original production certificate: five head-degree chains and six
initial quotients. It also checks the stated contents through degree 1023.
Its [retained exact counts](bench-results/sturm-bit-cost-formulas/costs.jsonl)
record total division bit volumes 13,331,767; 216,024,695; 3,477,325,117;
and 55,798,834,691 at head degrees 128,256,512,1024. These are mathematical
work counts, not timing observations or a wall-time consistency verdict.
The [degree-2048 extension](bench-results/sturm-bit-cost-formulas-2048/costs.jsonl)
checks contents through degree 2047 and records 1,426,150,547 stored bits,
719,498,752 normalization iterations and 894,038,477,175 division-bit volume.
From 1024 to 2048 the iteration count increases by 7.97 times and the bit
volume by 16.02 times, independently confirming the two distinct source costs.

## Earlier finite-regime replay timing hypothesis

The cost has two components: Θ(n³) normalization iterations/allocations and
Θ(n⁴) binary arithmetic. On a fixed-word machine these have independent
constants; a binary-work bound cannot identify which term dominates wall
time. The quartic wall-time declaration assumed that the limb-work term
dominated on the chosen ladder. The retained failed run and the operation-only
[degree-512 profile](bench-results/sturm-replay-profile/) do not support that
assumption. They do not contradict the quartic bit-volume calculation.

The source-derived iteration count is cubic (180,960 → 90,265,344 across
128 → 1024, before constant endpoint/chain multiplicities). The alternative
wall-time hypothesis tests that iteration/dispatch work on the explicitly
bounded degree ladder `128,256,512,1024`, with **n³** as its declaration and
otherwise unchanged settings. This exponent comes from the independently
counted normalizer iterations, not a fitted timing exponent. A fresh run is
required. Its claim is limited to this finite arithmetic regime; it neither
supersedes the Θ(n⁴) bit bound nor predicts unbounded-degree wall time. The
profile includes limb division as well as allocation and cannot establish
this hypothesis by itself. All quartic-model results remain retained.

The discriminating extension keeps the cubic iteration-cost declaration and
uses `256,512,1024,2048`, four trial-major trials and the same 600-second
operational cap. It is declared before collection. Pure cubic growth predicts
an eightfold time increase from 1024 to 2048; pure quartic growth predicts a
sixteenfold increase. The implemented mixed cost can lie between them. No
coefficient fitted to prior timings is used in the registered model. The
extension tests whether the finite iteration-cost characterization still holds
as limb work grows; a failed verdict remains a failure, not a reason to refit
a mixed-power constant.

Stored chain bit volume is also Θ(n³), as the exact counts show. That describes
the volume traversed by dense scans, not an automatic tight bound for the full
checker: recurrence verification also performs growing-integer products.
A cubic timing pass therefore does not certify that dyadic normalization has
optimal bit complexity. The Θ(n⁴) work of the current repeated-division
normalizer remains explicit whichever timing verdict the extension produces.

The extension's operational cap is raised to 1800 seconds before a fresh
collection with the same model, ladder and four trials. `LeanBench.Run` applies
the cap to the entire child, including `degreeInput` certificate preparation;
`LeanBench.Child.autoTune` retains the first timed call when it already exceeds
the tuning target. Thus the cap must cover preparation plus replay, even though
only replay enters the complexity comparison. The 600-second extension is
retained, including any timeout rows. This changes neither the scientific
model nor the measured operation. The larger allowance accommodates the
sixteenfold quartic scaling of both preparation and replay from degree 1024,
with additional operational margin; it is not a timing acceptance threshold.

The [completed extension](hex-sturm-performance.md#corrected-bit-cost-validation)
is inconclusive for cubic wall time (residual +0.168613). The observed
1024→2048 factor 9.97 lies between the independently counted iteration factor
7.97 and division-bit-volume factor 16.02. This comparison introduces no
fitted parameter and does not allocate the slowdown between normalization
and recurrence products. The exact bit-work calculation remains valid; the
current replay registration has no passing characterization on this full
ladder. Any changed implementation needs a new derivation of its actual costs.

## Deferred normalization: replay upper bound

The retained preregistration snapshot fixes the expression, mode and schedule.
The detailed storage and attribution arguments and cancellation discussion
below were expanded after collection. The original snapshot already states
the O(n³) allocation contribution; the declaration, schedule and samples
have not changed.

`ZPoly.hornerDyadic` carries `(a,k)` representing `a * 2^(-k)`. Multiplication
by an endpoint `(u,e)` gives `(u*a,k+e)`; adding a nonzero integer coefficient
aligns the two precisions by a shift. Zero coefficients retain the signed
precision without a shift. A zero accumulator resets its precision before
the next coefficient, including constant polynomials. `evalDyadic` normalizes
once after the array fold. The exact equality `evalDyadic_eq_fold` proves
that this returns the same canonical `Dyadic` as ordinary Horner evaluation.

For the fixed endpoints ±2, each Horner operation is a constant-size shift
or multiplication on O(k)-bit integers. There are O(k) coefficients in the
degree-k entry, giving O(k²) evaluation work and O(n³) over the chain.
The final repeated-division normalization has at most O(k²) bit work per
entry, also O(n³) in total. In this particular family its cost is smaller:
`U_k(2)/2^v₂(k+1)` is odd for even k and has exactly one factor of two for
odd k. The untimed calculation checks this through degree 2047. No coefficient
or intermediate accumulator is normalized within the fold.

The recurrence products must still be counted. Put `d_k = v₂(k+1)` and
`A = 2(k-d_k)`. For three consecutive primitive U polynomials of degrees
`k+1,k,k-1`, the production certificate has

```
leftScale  = 2^A
quotient   = 2^(A+1+d_k-d_(k+1)) X
rightScale = 2^(A+d_(k-1)-d_(k+1)).
```

This follows from `U_(k+1) = 2X U_k - U_(k-1)` and the implemented
two-cancellation pseudo-division multiplier, the square of the current
leading coefficient. In the first step `T_n = X U_(n-1) - U_(n-2)`, so
the quotient and right scale are instead `2^(A+d_k) X` and
`2^(A+d_(k-1))`. The script `scripts/bench/sturm_replay_costs.py` checks
every retained production step at degrees 8, 10, 12, 16 and 20 against these
formulas. The larger degree-128–2048 operation volumes are exact calculations
from the formulas, not counts taken from retained production certificates.
These are O(k)-bit
scalars, not constant-cost multipliers. They multiply O(k) coefficients of
O(k) bits per step. Initial and terminal checks, degree checks, literal
bindings, subtraction and evaluation add at most O(n³) bit work.

Storage work is included in the bound, independently of its unresolved caller
attribution in the profile. There are O(n²) outer coefficient operations.
Each produces only a constant number of O(n)-bit integers, with O(n) work to
initialize, copy or release their limbs; reference-count bookkeeping is
constant per reference. An array copy at such an operation visits at most
O(n) coefficient references, without deep-copying those integers. Summing
these costs gives O(n³) outer storage work. GMP's internal multiplication
workspace is included in its algorithmic multiplication bound. This is the
usual word/bit-work model, not a bound on shared-host allocator latency.

[GMP's published basecase bound](https://gmplib.org/manual/Basecase-Multiplication)
is O(N*M) limb operations. Its
[multiplication dispatch](https://gmplib.org/manual/Multiplication-Algorithms)
uses faster algorithms above architecture-dependent thresholds, including
unbalanced multiplication. Applying the schoolbook upper bound to O(n²)
products on O(n)-bit operands gives **O(n⁴)** total binary work. This is an
upper bound for the implemented kernel, not a matching lower bound. A
power-of-two operand is still passed to general GMP multiplication by `Int.mul`.
Using shifts for these products would change this family to cubic bit work;
it would also stop exercising general multiprecision multiplication. Such an
implementation would need its own declaration and a different family for
coverage of general products.

**Mode selection: mode 2, one-sided upper-bound parametric.** A tight
monomial model for this finite ladder is unavailable: the actual cost is a
sum of cubic traversal/evaluation work and size-dependent multiprecision
products. GMP's published interface does not give a single tight cost for
these sparse operands across its basecase/Toom crossovers. Assuming either
schoolbook dominance or cubic traversal dominance would repeat the unsupported
dominance assumption behind the earlier failures. Neither a fitted exponent
nor a fitted mixture is used. The cited upper bound covers the actual growing
products exercised by the family. The retained degree-1024 operation-only
profile identifies multiply/add-multiply routines as arithmetic hotspots
(17.01% in `__gmpn_addmul_1_x86_64` alone), but allocation, copying and
reference management collectively account for more samples. The storage
argument above covers this work by O(n³), within the total O(n⁴) bound;
the citation is not being used to bound allocation by itself. Stack unwinding did not recover usable kernel call chains;
no caller attribution is inferred for allocation samples.

The validation schedule is fixed before collection: degrees
`256,512,1024,2048`, four trial-major trials, 100 ms tuning target, and the
existing 1800-second whole-child operational cap. The registration declares
`n^4`. Until lean-bench provides mode 2, retain its two-sided verdict and
residual; a faster result is reported only as **within declared upper bound
(observed faster)** under SPEC/benchmarking.md. A slower result remains a
failure. A matching result is an upper-bound observation, never a two-sided
consistency claim. All original failed measurements remain evidence for the
original implementation.

The before/after comparison uses the retained cap1800 executable and the
new executable at degree 1024, four adjacent alternating AB/BA blocks,
one ordinary warm child per arm with a 100 ms tuning target. All completed
children are retained. Neither profiling rows nor nonadjacent historical
times enter this comparison. It tests the local optimization independently
of the complexity verdict.

### Cancellation tradeoff

Deferred normalization is not uniformly faster. For
`P_m = 2X^m + X^(m-1) + ... + X + 1` at `1/2`, every nonempty Horner suffix
has value 2. The former evaluator keeps a one-bit odd numerator throughout,
using O(m) fixed-size operations. After j lower coefficients the new fold
instead carries `(2^(j+1), j)`. The shifts/additions accumulate Θ(m²) binary
work, and its final normalization performs m+1 repeated divisions. The exact
result is still 2, but this family regresses from linear to quadratic bit
work. The Chebyshev replay measurements do not establish a speedup for such
cancellation-heavy fractional evaluations. The guards for constants and
zero coefficients preserve their compact behavior; the former evaluator was
also compact on constants and sparse monomials.
