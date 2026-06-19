# hex-poly (dense polynomial library, no dependencies)

The core polynomial library.

**Dense representation:**
```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

The normalization invariant (no trailing zeros) ensures structural equality
= semantic equality. Every operation maintains this invariant.

- Index = degree, `coeffs[i]` is coefficient of `x^i`
- Normalization invariant: no trailing zeros
- Structural equality = semantic equality
- O(1) degree, O(1) coefficient access

**Operations:**
- Addition, subtraction, multiplication (schoolbook, Karatsuba for large degree)
- Division with remainder (for monic divisors; general division over fields)
- Polynomial GCD (plain Euclidean remainder sequence — **not** the extended
  algorithm). `gcd` tracks only the remainders, so it is `O(deg²)`. The extended
  algorithm additionally multiplies the divisor against the growing Bezout
  accumulators `s`, `t` at every step (`q*s₁`, `q*t₁`), which is `O(deg³)` and
  pure waste when only the gcd *value* is needed — the common case being the
  square-free / separability test `gcd(f, f') = 1`. Computing Bezout coefficients
  inside `gcd` is a correctness-neutral but ~10⁴× performance defect on the BHKS
  prime-selection hot path, so `gcd` must be the plain remainder sequence.
- Extended GCD (`xgcd`, Bezout coefficients: `a*f + b*g = gcd(f,g)`) — a
  *separate* function for the genuine Bezout use-sites (CRT, Hensel, Berlekamp
  correctness). `gcd` agrees with `xgcd`'s gcd component (`gcd_eq_xgcd_gcd`), so
  the gcd-value lemmas transfer.
- Evaluation (Horner's method)
- Composition, derivative
- Content and primitive part (for `DensePoly Int`)

**Polynomial GCD — key properties:**
- `gcd f g` divides both `f` and `g`
- Every common divisor of `f` and `g` divides `gcd f g`
- Bezout: `∃ a b, a * f + b * g = gcd f g`

**Existential CRT for polynomials** (corollary of Bezout):

```lean
def polyCRT [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R) : DensePoly R :=
  u * t * b + v * s * a

theorem polyCRT_mod_fst [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % a = u % a

theorem polyCRT_mod_snd [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % b = v % b
```

Given coprime `a, b` with Bezout coefficients `s, t`, constructs `h`
with `h ≡ u (mod a)` and `h ≡ v (mod b)`. Used by hex-hensel,
hex-gfq-ring, and hex-berlekamp-mathlib (Berlekamp correctness proof).

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_poly` via python-flint | informational | all `setup_benchmark` registrations against integer polynomial inputs |

FLINT's `fmpz_poly` is the standard reference for univariate
integer polynomial arithmetic. The comparator is `informational`
rather than `gating`: FLINT tunes Karatsuba/Toom-Cook/FFT
crossovers in `fmpz_poly_mul` and uses non-recursive Newton-style
algorithms for division and GCD; Hex's implementation is
schoolbook with the Karatsuba crossover named in the algorithm
table above. The constant-factor gap is structural, not
algorithmic — the ratio is recorded for orientation but is not a
Phase-4 gate. Wired via a persistent-subprocess Python driver per
`SPEC/benchmarking.md §"External comparators" §"Process call"`.

Structured metadata in `libraries.yml: HexPoly.phase4.comparators`.
