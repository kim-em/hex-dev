# hex-poly-fp (polynomials over F_p, depends on hex-poly + hex-mod-arith)

Specialized polynomial arithmetic over `Z/pZ` using `UInt64` coefficients.

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
