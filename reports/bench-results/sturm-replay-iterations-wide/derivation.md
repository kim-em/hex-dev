# Sturm query bit-cost models

These models concern the actual integer/dyadic computations, with binary
integers and 64-bit GMP limbs. Scalar ring-operation counts alone do not
predict wall time when coefficient sizes grow. They are two-sided,
family-specific declarations, not uniform bounds for all query inputs.
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

## Growing head degree: dyadic replay

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

## Finite-regime replay timing hypothesis

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

Stored chain bit volume is also Θ(n³), as the exact counts show. That supplies
a lower bound for any evaluator, not an automatic tight bound for the full
checker: recurrence verification also performs growing-integer products.
A cubic timing pass therefore does not certify that dyadic normalization has
optimal bit complexity. The Θ(n⁴) work of the current repeated-division
normalizer remains explicit whichever timing verdict the extension produces.
