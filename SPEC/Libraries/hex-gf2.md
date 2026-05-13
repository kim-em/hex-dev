# hex-gf2 (GF(2) packed arithmetic, depends on hex-poly)

Packed bitwise representation of polynomials over F_2. Addition is
XOR, multiplication uses carry-less multiply. Substantially faster
than the generic `FpPoly 2` path (up to 64x for addition-heavy
workloads). Actual speedups depend on workload; benchmarks comparing
`GF2Poly` vs `FpPoly 2` for Berlekamp matrix construction and
polynomial GCD are planned.

**Contents:**

```lean
/-- Polynomial over F_2, packed into 64-bit words.
    Bit j of words[i] represents the coefficient of x^(64*i + j). -/
structure GF2Poly where
  words : Array UInt64
  degree : Nat
  wf : (words = #[] ∧ degree = 0) ∨
       (words.back! ≠ 0 ∧ degree < 64 * words.size ∧
        words[degree / 64]! &&& (1 <<< (degree % 64)) ≠ 0 ∧
        ∀ i, degree < i → i < 64 * words.size →
          words[i / 64]! &&& (1 <<< (i % 64)) = 0)
  -- Zero: words = #[], degree = 0.
  -- Nonzero: last word nonzero, bit `degree` set, no bits above.
```

- Addition: word-by-word XOR
- Multiplication: schoolbook or Karatsuba on 64-bit blocks, where
  each block multiply uses carry-less multiply via `@[extern]`
  calling a C wrapper that uses CLMUL on x86 (with compile-time
  feature detection) and a portable shift-and-XOR fallback on other
  architectures.
- Division with remainder (for polynomial GCD, modular reduction)
- GCD and extended GCD over `GF2Poly`
- Shift operations (multiply/divide by x^k)

**Key properties:**
- Ring axioms (char 2 gives `a + a = 0`; mul commutativity from the
  convolution definition over a commutative coefficient ring)
- `GF2Poly` is a Euclidean domain (degree function is the norm)
- Equivalence: `GF2Poly ≃+* FpPoly 2` (unpack/repack, in hex-gf2-mathlib)

**Carry-less multiply.** The `@[extern]` story mirrors hex-arith's
GMP externals: the pure Lean `clmul` is the logical definition used
in proofs; the C wrapper replaces it at runtime. Correctness of the
extern is trusted (same as `mpz_gcd`, `mpz_mul`, etc.).

The pure Lean fallback (also used as the logical definition):
```
def clmul (a b : UInt64) : UInt64 × UInt64 :=
  -- 64 iterations of: if bit i of b is set, XOR a << i into
  -- 128-bit accumulator (hi, lo). Must handle shift-past-64
  -- correctly by splitting into high/low word contributions.
```
Slower than hardware CLMUL but avoids the per-operation Barrett
overhead of the generic `ZMod64 2` path.

### Extern contract: `clmul`

```lean
@[extern "lean_hex_clmul_u64"]
def clmul (a b : @& UInt64) : UInt64 × UInt64 := Hex.pureClmul a b
```

`Hex.pureClmul` (shift-and-XOR, above) is the reference semantics.
The C wrapper `lean_hex_clmul_u64(uint64_t, uint64_t) → lean_obj_res`
in `HexGF2/ffi/clmul.c` returns the 128-bit product packed as `(hi, lo)`.

The C wrapper picks its implementation by preprocessor guards (no
runtime CPU detection): x86-64 `__PCLMUL__` uses
`_mm_clmulepi64_si128`; aarch64 `__ARM_FEATURE_CRYPTO` uses
`vmull_p64`; otherwise it runs a portable shift-and-XOR mirroring
`Hex.pureClmul`. Correctness of the intrinsic paths is trusted, same
as the GMP externs in hex-arith. Tests must exercise each compiled
wrapper path and the pure-Lean body (built without the extern
attached) to catch divergence.

**GF(2^n) elements.** Elements of `GF(2^n)` are polynomials of degree
< n over F_2, reduced modulo an irreducible of degree n. This library
provides the optimized representations and operations; the convenience
constructor that automatically chooses the canonical modulus lives in
`hex-gfq` as `GF2q`.

Two cases:

1. **n < 64**: a single `UInt64` suffices. The irreducible modulus
   `x^n + (lower terms)` is stored as `irr : UInt64` containing only
   the lower n coefficients (the leading `x^n` term is implicit).
   Addition is XOR, multiplication is CLMUL followed by reduction
   mod the irreducible (a few XORs with precomputed masks). This
   gives `GF(2^8)` for AES, `GF(2^16)` for coding theory, etc.
   (n = 64 excluded because reduction requires `1 <<< n` which is
   undefined for `UInt64` shift-by-64; use `GF2nPoly` for n ≥ 64.)

2. **n ≥ 64**: use `GF2Poly` with modular reduction after each
   multiply. `GF(2^64)`, `GF(2^128)` for GCM/GHASH, `GF(2^256)`
   for some post-quantum schemes.

```lean
/-- GF(2^n) packed into a single UInt64. Requires n < 64.
    irr stores the lower n coefficients of a monic degree-n
    irreducible; the leading x^n term is implicit. -/
structure GF2n (n : Nat) (irr : UInt64)
    (hn : 0 < n) (hn64 : n < 64)
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) where
  val : UInt64
  val_lt : val.toNat < 2^n

/-- GF(2^n) for arbitrary n, using GF2Poly.
    This is a quotient ring F_2[x]/(f), parallel to hex-gfq-ring
    but over GF2Poly instead of FpPoly. Operations: add via XOR,
    multiply via CLMUL then reduce mod f. -/
structure GF2nPoly (f : GF2Poly) (hirr : GF2Poly.Irreducible f) where
  val : GF2Poly
  val_reduced : val.IsZero ∨ val.degree < f.degree
```

For the small case, `GF2n` gets its executable `Field` operations and
algebraic laws directly from the irreducibility proof `hirr`, while
finiteness/cardinality stay on the Mathlib bridge side of the project
split. For large n, `GF2nPoly` likewise builds the packed quotient-field
execution structure (parallel to hex-gfq-ring/hex-gfq-field, but over
the packed `GF2Poly` representation rather than `FpPoly`) without
introducing Mathlib-only `Fintype` machinery into the computational
core.

`pow x n` on `GF2n` and `GF2nPoly` is square-and-multiply
(`O(log n)` field multiplications). The textbook `n+1 ↦ pow n * x`
recursion is forbidden — typical use cases (Tonelli–Shanks-style
square roots, Frobenius squarings, irreducibility witnesses)
exponentiate by `2^n`-sized integers, which a linear-time `pow`
cannot complete.

The ring equivalences `GF2n ≃+* FiniteField 2 f hf hirr` and
`GF2nPoly ≃+* FiniteField 2 f hf hirr` live in hex-gf2-mathlib,
transferring via `GF2Poly ≃+* FpPoly 2`; that bridge library is also the
home for `Fintype` and cardinality results about the packed
representations.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| NTL `GF2X` | informational | bench targets exercising packed-word GF(2)[x] arithmetic: addition, multiplication, division, GCD, modular reduction |

NTL is the speed reference for hand-tuned `GF(2)[x]` arithmetic:
its inner loops are optimised at the word level for carry-less
multiplication, XOR-folding division, and fast GCD. Hex's
packed-word representation is the same algorithmic shape but
the constant factors differ. The comparator is `informational`.

The wiring pattern (process-call driver vs `@[extern]` C++ shim
vs hybrid) is an implementation choice for the HO that wires
this comparator. The SPEC names NTL as the tool; the choice of
integration shape is documented in the bench module docstring
when the HO lands. Either pattern satisfies the SPEC.

Structured metadata in `libraries.yml: HexGF2.phase4.comparators`.
