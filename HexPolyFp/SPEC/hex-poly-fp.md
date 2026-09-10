# hex-poly-fp (polynomials over F_p)

Specialized polynomial arithmetic over `Z/pZ` using `UInt64` coefficients.
It depends on hex-poly and hex-mod-arith today. The fast-arithmetic stage adds
hex-poly-fast and hex-modular, after both planned libraries are active.

**Contents:**
- `FpPoly p` = `DensePoly (ZMod64 p)` with specialized fast paths
- Frobenius map: `X^p mod f` via repeated squaring
- `X^(p^k) mod f` for arbitrary k (square-and-multiply on polynomials)
- Modular composition (evaluate one polynomial at another, mod a third)
- Square-free decomposition (Yun's algorithm adapted for `F_p`).
  Any internal polynomial-power helper used to reconstruct a
  decomposition's product (e.g. `factor^multiplicity`) is
  square-and-multiply, `O(log multiplicity)` polynomial
  multiplications. The textbook `n+1 ↦ f * pow f n` recursion is
  forbidden. Factor accumulation: assembling the output list of
  `(factor, multiplicity)` pairs must be linear in the output size.
  Building via repeated `acc ++ [x]` is `O(|acc|)` per append and
  `O(k^2)` overall, and is forbidden; use `Array.push` or
  cons-then-reverse.

**Key properties:**
- Frobenius endomorphism: `frob(a + b) = frob(a) + frob(b)`
- Square-free decomposition: output factors are pairwise coprime, their
  product equals the input, and each factor is square-free, stated for the
  raw executable gcd by requiring the monic normalization of
  `gcd factor (derivative factor)` to be `1`

**Lazy reduction for small p.** When `1 < p < 2^32`, the product
`a * b` of two `ZMod64 p` values fits in a `UInt64` without overflow
(since `(2^32 - 1)^2 < 2^64`). This means sums of products can be
accumulated in `UInt64` before reducing mod `p`, as long as the
accumulator doesn't overflow. For a dot product of length `k`, the
worst-case accumulator value is `k * (p - 1)^2`, which fits in
`UInt64` when `k * (p - 1)^2 < 2^64`. For p = 3, that's ~4.6 × 10^18
terms; for p = 65537, it's ~4.3 × 10^9 terms.

This applies to dot-product-shaped kernels: matrix-vector multiply,
matrix-matrix multiply, Berlekamp matrix construction. For RREF
elimination updates that aren't pure dot products, reduce after each
step or use chunked accumulation.

Implementation: provide a `LazyZMod64` type (or just `UInt64`
accumulator functions) with:
```lean
def dotModP (p : Nat) (hp : 1 < p) (hpp : p < 2^32)
    (a b : Vector (ZMod64 p) k)
    (hk : k * (p - 1)^2 < 2^64) : ZMod64 p
```
The proof obligation is just overflow bounds. The correctness theorem
says `dotModP` equals the naive `∑ aᵢ * bᵢ mod p`. This lives in
hex-mod-arith (or hex-matrix as a fast path for matrix operations).

For large p (≥ 2^32), each multiplication must reduce immediately
(or use 128-bit intermediates), so lazy reduction doesn't apply.

## Fast polynomial arithmetic

[hex-poly-fast](../../SPEC/Libraries/hex-poly-fast.md) supplies the generic
lawful-plan interface, Newton division, half-gcd, product trees, multipoint
operations, and Padé approximation. This library supplies the `FpPoly`
multiplication plan and keeps `mulPacked` as its small-input baseline.

Three NTT paths are exposed:

- direct ordinary convolution when the target prime contains a root for the
  padded transform length;
- direct cyclic or negacyclic convolution when the corresponding root-order
  condition holds;
- convolution over the fixed auxiliary NTT-prime catalogue followed by
  balanced CRT and reduction modulo the target prime.

For operand sizes `r`, `s`, put `k = min r s`. Canonical coefficient lifts
give the integer bound `B = k * (p - 1)^2`; auxiliary primes are accepted only
when their product `P` satisfies the strict uniqueness condition `2*B < P`.
`mulNtt?` and `mulNttCrt?` return `none` when no suitable length or sufficient
catalogue product is available, and a `some` result is proved equal to
`DensePoly.mul`. Direct target-modulus NTT remains caller-planned because its
availability depends on a `PrimeModulus` instance and a root of the required
order. `mulFast` is total without those extra inputs: it uses generic
schoolbook multiplication below 16 coefficients in the shorter operand,
packed lazy-reduction multiplication up to the auxiliary crossover, then
tries CRT-NTT and falls back to generic Karatsuba rather than exposing
catalogue exhaustion. The published consumers (`powModMonic`, Frobenius
powers, modular composition, and hex-gfq-ring multiplication) call
`mulPackedFast`, the same dispatcher without the CRT-NTT and Karatsuba tail;
that tail lives in `HexPolyFp.NttMul`, which imports hex-poly-fast and
hex-modular, is built by hex-dev's `HexPolyFastKernels` target, and is not
exported by the released umbrella until those libraries are published
(https://github.com/kim-em/hex-dev/issues/10001). Every measured consumer size below is under the 8192-coefficient
crossover, so the published dispatcher performs exactly the measured work.

The schoolbook-to-packed boundary is shared by `F_257` and `F_65537`. Three
warm outer trials on `chungus2` with Lean `4.34.0-rc2` give:

| field | coefficients | schoolbook median | packed median |
|---|---:|---:|---:|
| `F_257` | 8 | 1.438 µs | 1.595 µs |
| `F_257` | 16 | 4.787 µs | 3.718 µs |
| `F_65537` | 8 | 1.464 µs | 1.603 µs |
| `F_65537` | 16 | 4.802 µs | 3.769 µs |

Thus `packedCutoff = 16`. Regenerate either field's boundary with
`lake exe hexpolyfp_bench compare Hex.FpPolyBench.runMulSchoolbookChecksum Hex.FpPolyBench.runMulPackedChecksum --param-floor 8 --param-ceiling 16 --param-schedule doubling --outer-trials 3`, substituting the two `257` target names for the small field.

The committed `F_65537` balanced crossover uses three cold outer trials on
`chungus2` (AMD EPYC 9455), Lean `4.34.0-rc2`, with the benchmark executable
built from this repository:

| coefficients per operand | packed median | CRT-NTT median |
|---:|---:|---:|
| 4096 | 29.117 ms | 29.665 ms |
| 8192 | 111.930 ms | 63.145 ms |

Accordingly `nttCrtCutoff = 8192`. Regenerate the boundary samples with
`lake exe hexpolyfp_bench compare Hex.FpPolyBench.runMulPackedChecksum Hex.FpPolyBench.runMulCrtNttChecksum --param-floor 4096 --param-ceiling 8192 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1`.

The same `FpPoly` plan drives fast division and half-gcd. Fresh three-trial
comparisons on the registered families show one-shot Newton division and
half-gcd losing to the retained finite-field algorithms at every shared rung
through degree 2048. At the largest rung, division is 58.198 ms retained versus
237.784 ms Newton, while GCD is 23.736 ms Euclidean versus 286.842 ms half-gcd.
The clean-source records are
[`division`](../../reports/bench-results/hex-poly-fp-5e7d935-divmod-compare.json)
and [`gcd`](../../reports/bench-results/hex-poly-fp-5e7d935-gcd-compare.json).
Square-free decomposition and GCD consumers therefore keep the retained paths.
Fast coefficient multiplication does win inside modular power, Frobenius, and
composition. The following three-trial warm medians over `F_65537` were
refreshed from clean source revision
`5e7d93547984331e2db21178e7ff5deb636283e0`. The machine-readable records are
[`pow`](../../reports/bench-results/hex-poly-fp-5e7d935-pow-compare.json),
[`frobenius`](../../reports/bench-results/hex-poly-fp-5e7d935-frobenius-compare.json),
and [`compose`](../../reports/bench-results/hex-poly-fp-5e7d935-compose-compare.json).

| operation | parameter | schoolbook multiplication | fast multiplication |
|---|---:|---:|---:|
| modular power | 64 | 1.779 ms | 0.990 ms |
| modular power | 512 | 143.366 ms | 72.490 ms |
| Frobenius `X^p mod f` | 24 | 0.430 ms | 0.309 ms |
| Frobenius `X^p mod f` | 80 | 3.626 ms | 1.982 ms |
| modular composition | 48 | 4.182 ms | 3.497 ms |
| modular composition | 192 | 244.029 ms | 187.687 ms |

All hashes agree. Compiled modular power retains the schoolbook loop below
modulus size 18 and otherwise uses `mulFast`; modular composition retains its
schoolbook Horner loop below `packedCutoff`. The kernel-facing definitions and
theorems remain schoolbook, with proved `@[csimp]` implementations selecting
the measured paths. Reproduce the comparisons with the paired
`runPowModMonicChecksum`/`runFastPowChecksum`,
`runFrobeniusXModChecksum`/`runFastFrobeniusChecksum`, and
`runComposeModMonicChecksum`/`runFastComposeChecksum` targets and
`--outer-trials 3`. Reproduce the retained/candidate division and GCD results
with the analogous `runDivModChecksum`/`runDivModFastChecksum` and
`runGcdChecksum`/`runGcdFastChecksum` pairs.

Benchmarks include forced packed, schoolbook, Karatsuba, reusable-plan direct
NTT, cold-plan direct NTT, CRT-NTT, and dispatcher entries. The remaining
target-modulus and operand-ratio ladders are part of the broader
hex-poly-fast calibration grid. Conformance forces the available kernels and
checks them against schoolbook multiplication; an invalid direct root or
insufficient CRT product is a required fallback case.
