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

The unchanged rational registration describes only its original finite
ladder `16,24,32,48,64,96`; its earlier pass is not a claim of linear bit
complexity on unbounded query degrees.

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
