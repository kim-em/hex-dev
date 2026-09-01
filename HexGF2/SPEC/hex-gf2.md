# hex-gf2 (GF(2) packed arithmetic, currently depends on hex-basic)

Packed bitwise representation of polynomials over F_2. Addition is
XOR, multiplication uses carry-less multiply. Substantially faster
than the generic `FpPoly 2` path (up to 64x for addition-heavy
workloads). Actual speedups depend on workload. Benchmarks comparing
`GF2Poly` vs `FpPoly 2` for polynomial GCD and Berlekamp matrix
construction exist, but they are cross-library, so their
registrations live in `bench/HexGF2Bench.lean` at the executable
root, outside the per-library `bench/HexGF2/` tree. The per-library
suite covers the packed core and the NTL comparator registrations.

**Contents:**

```lean
/-- Packed-word normalization: either the polynomial is zero, or its
    highest stored word is nonzero. -/
def GF2PolyNormalized (words : Array UInt64) : Prop :=
  words.size = 0 ∨ words.back? ≠ some (0 : UInt64)

/-- Polynomials over F_2, packed into 64-bit words.
    Bit j of words[i] stores the coefficient of x^(64*i + j). -/
structure GF2Poly where
  words : Array UInt64
  normalized : GF2PolyNormalized words
```

Two fields, not three. The degree is derived (`GF2Poly.degree?` reads the
highest set bit, `GF2Poly.degree` is its `getD 0` form) rather than cached in
the structure, so the only invariant to maintain is that the top word is
nonzero. Caching the degree would mean carrying a four-clause well-formedness
condition through every operation and re-establishing it after each; deriving
it costs one scan of the top word and makes equality of elements equality of
word arrays (`GF2Poly.ext_words`).

- Addition: word-by-word XOR
- Multiplication: currently schoolbook on 64-bit blocks. The planned
  multiplication ladder adds word Karatsuba and packed Schönhage dispatch.
  Each base block product uses carry-less multiplication through `@[extern]`.
  The C implementation uses CLMUL when it is enabled at compile time and a
  portable shift-and-XOR implementation otherwise.
- Division with remainder (for polynomial GCD, modular reduction)
- GCD and extended GCD over `GF2Poly`
- Shift operations (multiply/divide by x^k)

**Key properties:**
- Ring axioms (char 2 gives `a + a = 0`; mul commutativity from the
  convolution definition over a commutative coefficient ring)
- `GF2nPoly` carries the bundled `Lean.Grind.Semiring`, `Ring`, and
  `CommRing` instances, so `grind` reasons about the packed quotient the way
  it does about `hex-gfq-field`'s generic one
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
wrapper path and the pure-Lean body to catch divergence.

Because the choice is made at compile time, one build runs exactly one
path, and the Lake target passes only `-O3`, so ordinary builds compile
the portable fallback. Covering the requirement therefore needs two
compilations rather than one:

- `scripts/ci/check_clmul_paths.sh` compiles `HexGF2/ffi/clmul_selftest.c`
  against `clmul.c` twice, plain and with the flag that enables the host's
  intrinsic (`-mpclmul` on x86-64, `-march=armv8-a+crypto` on aarch64),
  and cross-checks the intrinsic against the portable reference on 100000
  deterministic pairs. A build that asked for an intrinsic and did not get
  one fails rather than passing quietly.
- `conformance/HexGF2/CrossCheck.lean` compares the extern against
  `Hex.pureClmul` over a pseudorandom stream, which is the Lean half: it
  checks the compiled wrapper against the logical definition the proofs
  use.

`clmul.c` exposes `hex_clmul_portable`, `hex_clmul_intrinsic`, and
`hex_clmul_uses_intrinsic` so both halves can address the paths
individually; `HEX_CLMUL_NO_LEAN` drops the export wrapper so the
self-test needs no Lean runtime.

## Multiplication ladder

This section specifies a planned extension. The current `GF2Poly.mul` is the
word-schoolbook convolution `mulWords`, and its existing theorems use that
definition. The extension retains `GF2Poly.mul` as the logical definition and
adds a proof-backed `@[csimp]` replacement selected by operand word count:

1. `mulWords` below the first crossover;
2. Karatsuba split at word boundaries between the two crossovers;
3. packed Schönhage multiplication above the second crossover.

The base products in both recursive rungs use the existing carry-less word
product. The committed crossover table is determined only by within-Hex
comparisons between adjacent rungs, following
[hex-poly-fast §Benchmarking and production dispatch](../../HexPolyFast/SPEC/hex-poly-fast.md).
A new rung is selected only for cells in which it wins outside the recorded
uncertainty band. Dispatch does not change the logical definition or any
coefficient theorem.

### Dense correspondence

The correctness proof converts packed polynomials to dense polynomials over
`ZMod64 2`. The new Mathlib-free API is:

```lean
def GF2Poly.toDense : GF2Poly → DensePoly (ZMod64 2)
def GF2Poly.ofDense : DensePoly (ZMod64 2) → GF2Poly
```

The coefficient theorem says that coefficient `i` of `toDense p` is the
element of `ZMod64 2` represented by bit `i % 64` in word `i / 64`.
Round-trip theorems account for normalization of the dense and packed
representations. Addition, multiplication, and the triadic carrier operations
commute with these conversions.

The names `FpPoly 2` and the equivalence `GF2Poly ≃+* FpPoly 2` remain in
hex-gf2-mathlib, which already depends on hex-poly-fp. `HexGF2` does not
import `FpPoly`. The generic Schönhage plan is instantiated at coefficient
ring `ZMod64 2`, not at coefficient ring `GF2Poly`.

### Packed Schönhage kernel

The planned packed kernel follows the generic algorithm in
[hex-poly-fast §Schönhage's radix-3 algorithm](../../HexPolyFast/SPEC/hex-poly-fast.md)
with the same `SchoenhageSchedule`, transform indices, and recursive
half-lengths. In characteristic two, subtraction is XOR and the inverse of
three is `1`. Transform addition, subtraction, and twiddle operations are
therefore packed linear operations. Pointwise multiplication is not a linear
operation. Its base cases use carry-less word multiplication.

The packed carrier holds a residue modulo `y^(2L) + y^L + 1` in
`ceil(2L / 64)` words with the unused top bits of the last word zero.
The selected `L` is not rounded to a word boundary. Brent, Gaudry, Thomé, and
Zimmermann §3.2 permits non-word-aligned `L`, and the schedule must be used
without changing its arithmetic constraints.

Packed multiplication by `y^j` implements the exact triadic reduction. For a
set bit at exponent `i`, it sets `r = (i + j) % (3 * L)`. If `r < 2 * L`, it
XORs the bit into exponent `r`. Otherwise it XORs the bit into exponents
`r - L` and `r - 2 * L`. This rule is applied directly. A single rewrite at
exponent `2L` is insufficient because `i + j` can exceed `3L`.

The required packed operations are:

- overlap-safe XOR addition and subtraction;
- multiplication by `y^j` using the rule above, including shifts across word
  boundaries and masking of the final word;
- conversion between `GF2Poly` blocks and packed triadic values;
- pointwise multiplication through the recursive packed dispatcher.

Each operation has an unpacking theorem identifying it with the corresponding
operation on `Triadic (ZMod64 2) L`. Correctness is proved in four stages:

1. packed carrier operations agree with generic triadic operations;
2. the packed forward and inverse transforms agree elementwise with the
   generic radix-3 transforms;
3. the packed recursive product agrees under `toDense` with
   `schoenhagePlan` instantiated over `ZMod64 2`;
4. the packed result has the carry-less convolution coefficients specified by
   `GF2Poly.mul`.

The fourth theorem supplies the `@[csimp]` correctness proof. None of the
dense values occur in the packed computation.

No operation-count theorem is claimed for the packed kernel. The
coefficient-operation bound in
[hex-poly-fast-cslib](../../SPEC/Libraries/hex-poly-fast-cslib.md) applies to
the generic worker. One packed XOR represents 64 coefficient additions, and
the packed base product uses CLMUL. A possible hex-gf2-cslib library would
need a separate word-operation model.

### Conformance and benchmarks for the ladder

The conformance stream will add shared-input cases that force each rung,
cases immediately below and above both crossovers, and packed carrier cases
with `L % 64 ≠ 0`. The registered conformance oracle remains python-flint at
`scripts/oracle/gf2_flint.py`. It recomputes the full product over `F_2` from
the serialized inputs. The NTL `GF2X` program is a checksum-based benchmark
comparator and is not a conformance oracle.

The benchmark family will extend far enough to bracket both within-Hex
crossovers on the reference host. Schoolbook versus Karatsuba measurements
determine the first table entry. Karatsuba versus packed Schönhage
measurements determine the second. NTL/gf2x remains informational and gives
context for the resulting large-degree performance. Its ratios do not select
either Hex crossover.

## Milestones

1. **Dense correspondence and dependencies.** Add the specified
   `HexFiniteField`, `HexPoly`, `HexPolyFast`, and `HexModArith` monorepo
   dependencies. Define `toDense` and `ofDense`, then prove coefficient,
   round-trip, and operation theorems.
2. **Word Karatsuba.** Implement the word-boundary recursion, prove its result
   equal to `mulWords`, and add forced-rung conformance and benchmark cases.
3. **Packed Schönhage.** Implement the non-word-aligned carrier operations,
   transforms, recursive product, and the four stages of correctness above.
4. **Dispatch.** Measure adjacent rungs, commit the crossover table, and add
   the proof-backed `@[csimp]` dispatcher. Extend the python-flint fixtures and
   retain NTL/gf2x as an informational comparator.

`hex-poly-fast` depends on `hex-truncated-series`. Neither library is yet
listed in `scripts/release/released.yml`. The released hex-gf2 mirror can add
the planned dependencies only after hex-truncated-series and hex-poly-fast
have been published in dependency order. Development and the combined build
inside this monorepo do not depend on that publication step.

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

For the small case, `GF2n` gets its executable `Field` operations from the
irreducibility proof `hirr`, while finiteness and cardinality stay in the
Mathlib companion.

**Irreducibility alone does not give a field.** `GF2Poly.Irreducible f` asks
that `f` be nonzero and admit no factorization into two positive-degree parts.
The constant `1` satisfies both, and `GF2nPoly 1 _` is then the trivial ring,
where every residue is `0` and `0 = 1`. So `zero_ne_one`, the field laws, and
characteristic two are *not* consequences of `hirr`; they need `0 < f.degree`
as well.

`hex-gfq-field` avoids this by carrying `hf : 0 < f.degree` as a type parameter
beside the irreducibility proof. The packed types do not, so the ring structure
is supplied as instances, which hold for every admissible modulus, and the field
laws as `fieldOfDegreePos` and `isCharPOfDegreePos`, which take the degree
hypothesis. Callers have it: every committed `PackedGF2Entry` carries
`degree_pos`. Adding the hypothesis to the structures, so the field laws could
be instances too, is the alternative and would be a breaking change. For large n, `GF2nPoly` likewise builds the packed quotient-field
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

## Irreducibility: the test, its soundness, and the committed moduli

Forming a field needs a proof that the modulus is irreducible, and this library
produces those proofs from an executable test rather than by trusting a table.
Three modules carry that, and they are a substantial fraction of the library.

**`HexGF2.Irreducibility`** defines the test. `rabinTest f` is the Rabin
criterion on the packed representation: `x^(2^deg f) ≡ x (mod f)`, and for each
maximal proper divisor `d` of `deg f`, `gcd(x^(2^d) - x, f) = 1`.
`checkIrreducibilityCertificate` replays a supplied certificate instead of
recomputing the test, and `checkIrreducibilityCertificateLinear` is its
kernel-reducible variant, for `decide` on small closed terms.

**`HexGF2.RabinSoundness`** is the soundness half, and holds the library's
headline theorem. `rabinTest_imp_irreducible` lifts a passing test to
`GF2Poly.Irreducible`, and `checkIrreducibilityCertificate_imp_irreducible`
does the same from a checked certificate. Without these the test would be a
heuristic; with them a committed modulus is irreducible as a matter of Lean
proof, and a corrupted entry fails to elaborate rather than silently yielding a
reducible modulus.

**`HexGF2.CommonIrreducibility`** commits the moduli cryptography actually
uses, each with its certificate and irreducibility proof, so a caller naming
one does not supply a proof:

| Modulus | Field | Declaration |
|---|---|---|
| `x^4 + x + 1` (`0x3`) | `GF(16)` | `gf16Modulus`, `gf16_modulus_irreducible` |
| `x^8 + x^4 + x^3 + x + 1` (Rijndael, `0x1B`) | `GF(256)` | `aesModulus`, `aes_modulus_irreducible` |
| `x^16 + x^12 + x^3 + x + 1` (`0x100B`) | `GF(65536)` | `gf65kModulus`, `gf65k_modulus_irreducible` |
| `x^128 + x^7 + x^2 + x + 1` (GHASH) | `GF(2^128)` | `ghashModulus`, `gf2nPoly_modulus_irreducible` |

The names index the field size, not the modulus degree: `gf16` is the degree-4
modulus presenting the sixteen-element field, and `gf65k` the degree-16 one.

None of these use `native_decide`; the certificates are replayed by the kernel.
The GHASH certificate stores precomputed `x^(2^k) mod ghashModulus` entries
rather than recomputing them, which is what keeps a degree-128 check inside the
proof budget.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| NTL `GF2X` | informational | performance ratios for packed multiplication, division, modular reduction, and GCD; addition is a same-input correctness/protocol anchor |

NTL is the speed reference for hand-tuned `GF(2)[x]` arithmetic. The measured
NTL 11.6.0 build links gf2x 1.3.0 for large multiplication; NTL's `GF2X`
source uses tuned base cases and Karatsuba/gf2x multiplication, crossover-based
division and remainder, and switches its GCD to `HalfGCD` above the configured
crossover. Hex currently implements packed schoolbook multiplication, long
division and remainder, and Euclidean GCD. §Multiplication ladder specifies
planned Karatsuba and Schönhage rungs with the same multiplication complexity
class as gf2x. Until those rungs are implemented, the upper multiplication
cells compare different complexity classes. The division and GCD cells
continue to do so. These ratios provide context and do not determine the Hex
dispatch table or Phase 4. Addition has the same linear packed-word
kernel shape, but the hex-framed driver measures serialization rather
than raw NTL addition, so its paired registrations are correctness and
protocol anchors rather than performance evidence. The comparator is
`informational`.

The wiring pattern (process-call driver vs `@[extern]` C++ shim
vs hybrid) is an implementation choice for the HO that wires
this comparator. The SPEC names NTL as the tool; the choice of
integration shape is documented in the bench module docstring
when the HO lands. Either pattern satisfies the SPEC.

Structured metadata in `libraries.yml: HexGF2.phase4.comparators`.
