# hex-poly-z (polynomials over Z, depends on hex-poly)

Specialized polynomial arithmetic over `Z`.

**Contents:**
- `ZPoly` = `DensePoly Int`
- Polynomial congruence:
  ```lean
  def ZPoly.congr (f g : ZPoly) (m : Nat) : Prop :=
      ∀ i, (f.coeff i - g.coeff i) % m = 0

  def ZPoly.coprimeModP (f g : ZPoly) (p : Nat) : Prop := ...
  ```
- Content and primitive part: `f = content(f) * primitivePart(f)`
- Mignotte bound computation: `|gⱼ| ≤ C(k,j) · ‖f‖₂` for any degree-k
  factor `g | f` in `Z[x]`. The computation is just binomial coefficients
  and the 2-norm of `f`'s coefficients. The proof that the bound is valid
  lives in `hex-poly-z-mathlib`.

  **Complexity contract for the Mignotte computation.** Both bodies
  must be polynomial in their inputs:

  - `binom n k` uses the multiplicative formula
    `(∏ i<k, (n − i)) / k!` and runs in `O(k)` `Nat` multiplications.
    The Pascal-triangle recursion `binom (n+1) (k+1) = binom n k +
    binom n (k+1)` is forbidden as the executable body. Without
    memoisation it takes `Θ(2^k)` calls and a Mignotte computation
    over a degree-50 factor cannot terminate.
  - `floorSqrt n` runs in `O(log n)` iterations via Newton's method
    `x ← (x + n / x) / 2` (or bit-by-bit binary search). Descending
    linear search is forbidden: `coeffNormSq f` for any non-trivial
    `ZPoly` is at least `2^40`, and a linear-time `floorSqrt` makes
    `coeffNorm f` non-terminating in practice.

  These requirements prevent mathematically correct formulas with the
  wrong executable complexity. The short description "binomial
  coefficients and the 2-norm" would otherwise permit both efficient
  and exponential implementations.

**Key properties:**
- `primitivePart(f)` is primitive (content = 1)
- Gauss-style corollaries needed for downstream Mathlib-free
  factorization live in this library. The general statement
  `content(f * g) = content(f) * content(g)` still transfers from
  Mathlib via the ring equivalence in hex-poly-z-mathlib, but the
  Berlekamp–Zassenhaus Z-level reassembly path needs (at least) the
  following primitive-product corollary directly here so its proof
  stays Mathlib-free:
  - `Primitive p → Primitive q → Primitive (p * q)` (used to discharge
    `primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive`).
  - The associated rational-associate cancellation
    (`rational_associate_primitive_unit`): if two primitive nonzero
    `ZPoly`s agree as rational associates with rational factor `u`,
    then `u = ±1`.
  - The signed integer reassembly
    (`primitiveSquareFreeDecomposition_reassembly_signed`) for the
    BZ Z-level recombination chain.

**Units in `ℤ[x]`:**

```lean
/-- A ZPoly is a unit iff it equals ±1 as a constant polynomial.
    Coefficient-ring-specific (units in `R[x]` depend on units in
    `R`), so this lives in `HexPolyZ` rather than the generic
    `HexPoly`. -/
def Hex.ZPoly.IsUnit (f : ZPoly) : Prop := f = .C 1 ∨ f = .C (-1)

instance : Decidable (Hex.ZPoly.IsUnit f) := …   -- structural via DecidableEq
```

Used by downstream irreducibility predicates (in
`hex-berlekamp-zassenhaus`) and by any code that needs to test
unit-ness in `ℤ[x]`. The Mathlib correspondence theorem
`Hex.ZPoly.IsUnit f ↔ IsUnit (toPolynomial f)` lives in
`hex-poly-z-mathlib`.

## The integer product kernel: Kronecker substitution

`DensePoly.mul` is the schoolbook convolution, and it stays the
specification. Over `Int` it is also the wrong kernel above a modest
degree: every coefficient product is a GMP call with its own allocation,
so a degree-90 product at 92-bit coefficients issues 8100 of them.

`Hex.ZPoly.mulKronecker` is the production kernel for integer
polynomials. It evaluates both operands at `2 ^ b`, multiplies the two
packed integers **once**, and reads the product coefficients back off as
base-`2 ^ b` digits, which hands the work to GMP's Toom/FFT ladder
instead. Packing and unpacking are balanced divide-and-conquer over
shifts (`O(n log n)` limb operations), and the constant bias repunit is
computed by doubling rather than by a slot walk — measured as the single
largest cost in the path before it was split out.

Signed coefficients are carried by biasing every slot by `2 ^ (b - 1)`,
so digit extraction stays plain base-`2 ^ b` division with no borrow
propagation. The slot width is derived from a **runtime** scan of the
actual coefficients (`Hex.ZPoly.maxAbs`), so the no-overlap bound is
re-established on every call rather than assumed.

`Hex.ZPoly.mulKronecker_eq` proves the kernel equal to `DensePoly.mul`
on all inputs, at every degree and coefficient size, including the
threshold boundary and degenerate inputs. It rests on
`Hex.DensePoly.eval_mul_commring` (Horner evaluation is multiplicative)
and on uniqueness of base-`2 ^ b` digit expansions.

**Measured cutoffs.** Below them the schoolbook loop wins and is what
runs. Both are read off `scripts/bench/kronecker_crossover.py`, which
sweeps degree against coefficient width on host `chungus2` (AMD EPYC
9455), Lean toolchain `4.33.0-rc1`, pinned to a verified-idle core:

- `kroneckerSizeCutoff = 24` — the shorter operand must store at least
  24 coefficients.
- `kroneckerBitCutoff = 20` — the widest coefficient must be at least 20
  bits.

The second cutoff is not redundant, and it is not where a naive reading
of the schoolbook cost would put it. Schoolbook cost per coefficient pair
is flat at about 9 ns up to 12-bit coefficients, steps to about 53 ns at
16 bits, and steps again to about 120 ns at 20 bits. Kronecker cannot
amortise against the first regime at any degree in the sweep's reach
(still 1.35x *slower* at degree 90 with 12-bit coefficients), and against
the middle regime the crossover degree runs 64, 40, 24, 20, 16, 16 at 14,
15, 16, 17, 18 and 19 bits — close enough to the size cutoff that
measurement variance moves it either side of 24. Setting the width cutoff
above the second step keeps the whole uncertain band on schoolbook. No
swept cell at or above both cutoffs loses to schoolbook, at either sign;
the win grows with degree:

| coefficient bits | n=24 | n=32 | n=48 | n=90 | n=128 |
|---|---:|---:|---:|---:|---:|
| 20 | 2.00 | 2.65 | 3.93 | 7.37 | 10.38 |
| 32 | 2.18 | 2.95 | 4.36 | 7.88 | 11.21 |
| 92 | 2.54 | 3.37 | 4.76 | 8.86 | 13.02 |
| 181 | 1.50 | 1.99 | 2.73 | 4.78 | 6.47 |
| 400 | 1.56 | 1.90 | 2.66 | 4.54 | 6.01 |

`mulKroneckerAt` takes both cutoffs explicitly so the kernel benchmark
can sweep them; production fixes them to the measured constants.

**Operation counts.** For operands of `n` and `m` coefficients the
schoolbook loop issues `n * m` coefficient multiplications and as many
additions, each on a fresh heap-allocated `Int`. The substitution issues
**one** integer multiplication, `n + m - 2` shift-and-add pairs to pack
the two operands, `O(log (n + m))` to build the bias repunit, one
addition to apply it, and `3 * (n + m - 2)` shift, shift and subtract
operations to extract the digits — `O((n + m) log (n + m))` limb work
against the schoolbook's `Θ(n * m)` allocations. At `n = m = 90` with
92-bit coefficients that is 8100 multiplications against one, an 8.9x
measured speedup; at degree 178 it is 16.3x.

**What a single size cutoff leaves on the table.** The cutoff pair is
deliberately one rule, not a width-indexed table, and that costs some
measured wins at both ends. At 4-bit coefficients Kronecker draws
level around degree 90 and reaches 1.75x there, but the same band is
still 1.5x behind at degree 48, so the bit cutoff excludes all of it, as
it does the 17-to-19-bit band that crosses between degrees 16 and 20. In
the other direction, coefficients of 20 bits and up are already ahead at
12 to 16 slots, so a width-indexed size cutoff would reach further down a
product tree than 24 does. Both are
measurable refinements with their own sweeps; neither is a regression
against schoolbook today.

Two further refinements are measured-but-unspent. The slot width budgets
`A²` for `A = max (maxAbs p) (maxAbs q)`; the tighter
`maxAbs p * maxAbs q` would nearly halve the packed size when one operand
carries much smaller coefficients, at the cost of generalising
`natAbs_coeff_mul_le_min` to two bounds. And `unpackAux` builds and
concatenates two arrays per internal node; filling one preallocated array
by index would drop those allocations and the `O(n log n)` element
copying, which is the largest remaining cost in the kernel (50 µs of
149 µs at degree 90).

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_poly` via python-flint | informational | bench targets exercising arithmetic on `ZPoly` (the integer-polynomial surface inherited from `HexPoly`) |

Same comparator and rationale as `hex-poly` (informational because
of FLINT's tuned Karatsuba/Toom-Cook/FFT crossovers vs Hex's
schoolbook-plus-Kronecker implementation). The Mignotte / Hensel-lift
data surfaces specific to `hex-poly-z` have no direct FLINT
analog at the same level of abstraction; those bench targets
declare absence with the `no-comparable-surface-in-named-comparator`
reason per `SPEC/benchmarking.md §"Comparator naming"`.
