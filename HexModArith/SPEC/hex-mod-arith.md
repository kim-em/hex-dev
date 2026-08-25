# hex-mod-arith (modular arithmetic, depends on hex-arith)

Arithmetic in `Z/pZ` with `UInt64`-backed coefficients. A single
`ZMod64 p` type stores residues in standard form (canonical
representative in `[0, p)`); Barrett and Montgomery from `hex-arith`
provide opt-in *operations* on `ZMod64` for hot loops, not parallel
types.

## Bounds typeclass and type

```lean
/-- Project-local bounds class: `ZMod64 p` is a faithful model of
`Z/pZ` only when `p` is positive and strictly below `2^31`. -/
class ZMod64.Bounds (p : Nat) : Prop where
  pPos : 0 < p
  pLtR : p < 2 ^ 31

/-- Derived machine-word bound `p < UInt64.word` (= `2^64`). -/
theorem ZMod64.Bounds.pLtWord (p : Nat) [Bounds p] : p < UInt64.word

structure ZMod64 (p : Nat) [Bounds p] where
  val  : UInt64
  isLt : val.toNat < p
```

The bounds live in a typeclass that callers provide once per
modulus, e.g. `instance : ZMod64.Bounds 7 := ⟨by decide, by decide⟩`.
Every operation takes `[Bounds p]` implicitly; nothing is threaded
through call sites. The `p < 2^31` bound is owner-blessed: every
current and anticipated application (Berlekamp-Zassenhaus, LLL,
matrix work) uses small primes. It is tight enough that `p`, every
residue, and the *sum* of two residues all fit in a `UInt64` with no
carry, and the *product* of two residues stays below `2^62` (one
word, no `__uint128_t`). This keeps `add`/`sub`/`neg` free of any
carry/borrow correction (`add` is a single conditional subtract of
the modulus word, `sub` a single sign test) and the modular multiply
a single-word product plus one `%`. Code that still needs the raw
machine-word bound goes through the derived `Bounds.pLtWord`.

Mathlib's `Fact` is unavailable to `hex-mod-arith` (it is a
computational library, not a Mathlib bridge). The project-local
`Bounds` class gives the same instance-synthesis ergonomics with no
Mathlib dependency.

## Default operations

Operations are stated as semantic contracts on the canonical
representative. `mul`, `pow`, and `inv` carry mandatory `@[extern]` runtime
paths; `add`/`sub` are one-line `ofNat` specifications, with the
division-free branchy `UInt64` bodies in `addImpl`/`subImpl` behind
proved `@[csimp]` equalities (design principle 11). `inv` retains the
`HexArith.Int.extGcd`-based logical body used by proofs, while its
`lean_hex_zmod64_inv` extern runs the same Euclidean remainder/cofactor
recurrence directly in bounded word arithmetic. **`inv` must NOT call
`Hex.pureIntExtGcd` directly at runtime** — that is the recursive proof
reference and allocates a fresh `Nat` blob per step (the same regression class
as omitting `@[extern]` on `mulHi`).

```lean
@[extern "lean_hex_zmod64_mul"]
def ZMod64.mul (a b : ZMod64 p) : ZMod64 p := ...   -- contract below
def ZMod64.add (a b : ZMod64 p) : ZMod64 p          -- spec: ofNat; runtime: addImpl (@[csimp])
def ZMod64.sub (a b : ZMod64 p) : ZMod64 p          -- spec: ofNat; runtime: subImpl (@[csimp])
def ZMod64.zero : ZMod64 p
def ZMod64.one  : ZMod64 p                          -- equals zero when p = 1
@[extern "lean_hex_zmod64_inv"]
def ZMod64.inv  (a : ZMod64 p) : ZMod64 p           -- spec: Int.extGcd; runtime: words
@[extern "lean_hex_zmod64_pow"]
def ZMod64.pow  (a : ZMod64 p) (n : Nat) : ZMod64 p
```

Key properties:

```lean
theorem ZMod64.toNat_add (a b : ZMod64 p) :
    (a.add b).val.toNat = (a.val.toNat + b.val.toNat) % p
theorem ZMod64.toNat_mul (a b : ZMod64 p) :
    (a.mul b).val.toNat = (a.val.toNat * b.val.toNat) % p
theorem ZMod64.toNat_inv (a : ZMod64 p) (hcop : Nat.Coprime a.val.toNat p) :
    (a.inv.mul a).val.toNat = 1 % p
```

### `ZMod64.mul` runtime contract

Logical body (used by Lean for proofs and as the portable fallback):

```lean
⟨.ofNat ((a.val.toNat * b.val.toNat) % p), proof_of_isLt⟩
```

The runtime implementation is supplied by `lean_hex_zmod64_mul` in
`HexModArith/ffi/zmod64_mul.c`. Acceptable runtime strategies for
the C body, in order of simplicity:

1. **Single-word 64/64 modular reduction** (the current body). Under
   the `p < 2^31` bound both residues are below `2^31`, so their
   product is below `2^62` and fits in one `uint64_t`; the extern is
   `uint64_t product = a * b; return product % modulus;` — a plain
   64/64 divide with no `__uint128_t`. (Before the bound was
   tightened this had to widen to `__uint128_t` for a 128/64 reduce.)

2. **Barrett reduction** — precompute `pinv = ⌊2^64 / p⌋` once per
   modulus (lifted from `BarrettCtx` in `hex-arith`) when
   `p < 2^32`. ~10 cycles per multiply. This needs a reused per-
   modulus context, so it belongs in convolution kernels (poly/matrix
   products), not the contextless `ZMod64.mul`.

3. **Montgomery reduction** — precompute `p'` and `R^2 mod p` once
   per modulus (lifted from `MontCtx` in `hex-arith`) when
   `p % 2 = 1`. ~10 cycles per multiply with values stored in
   Montgomery form internally; `ZMod64.mul` exposes standard form,
   so this strategy adds two `montgomeryReduce`s per call to amortize.

The Phase-1 deliverable is the strategy-1 reference body plus the
`@[extern]` wiring; later phases may swap the body for a
`p`-dispatched Barrett/Montgomery implementation behind the same
extern symbol. Whichever strategy is used, it must agree with the
logical body — the SPEC mandates the contract, not the strategy.

### `ZMod64.pow` runtime contract

Logical body (used by Lean for proofs and as the portable semantic
contract): exponentiation by squaring over `ZMod64.mul`, reading the
natural exponent from low bits to high bits.

The runtime implementation is supplied by `lean_hex_zmod64_pow` in
`HexModArith/ffi/zmod64_mul.c`. It exports large Lean `Nat` exponents
to 64-bit limbs once, then scans those limbs from high bits to low
bits while performing the same square-and-multiply recurrence on
`UInt64` residues. This keeps exponent-bit traversal linear in the
bit length instead of repeatedly dividing a shrinking arbitrary-
precision `Nat` by two. The runtime result must agree with the
logical body for every bounded modulus, including the degenerate
modulus `1`.

### `ZMod64.inv` runtime contract

The transparent logical definition of `HexArith.Int.extGcd` reduces to
`Hex.pureIntExtGcd`. The `inv` body selects that reference algorithm's first
Bézout cofactor `s` and returns `s % p`; this pins the result even when the
inputs are not coprime. The runtime implementation is `lean_hex_zmod64_inv` in
`HexModArith/ffi/zmod64_mul.c`. For the nonnegative inputs `a < p`, it follows
the same Euclidean quotient/remainder sequence as the logical reference, but
tracks the first cofactor modulo `p`:

```text
(old_r, r) := (a, p)       (old_s, s) := (1, 0)
q := old_r / r
(old_r, r) := (r, old_r % r)
(old_s, s) := (s, old_s - q*s mod p)
```

Reducing each cofactor update modulo `p` preserves the final cofactor residue,
so this agrees with the logical body for every input, including composite
moduli and non-coprime residues. This is not Fermat inversion. Under
`p < 2^31`, every remainder and reduced cofactor is below `p`, every quotient
is at most `p`, and `q*s < 2^62`; the complete runtime path therefore stays in
`uint64_t` arithmetic and never constructs a Lean `Int` or calls GMP.

## Hot-loop optimization (opt-in)

Sustained modular multiplication (polynomial arithmetic,
exponentiation by squaring, Frobenius maps) opts into `BarrettCtx`
or `MontCtx` from `hex-arith` via thin wrappers at the `ZMod64`
level:

```lean
def BarrettCtx.mulMod (ctx : BarrettCtx p) (a b : ZMod64 p) : ZMod64 p
    -- requires p < 2^32; lifts BarrettCtx.mulMod : UInt64 → UInt64 → UInt64

def MontCtx.toMont   (ctx : MontCtx p) (a : ZMod64 p)        : MontResidue p
def MontCtx.mulMont  (ctx : MontCtx p) (a b : MontResidue p) : MontResidue p
def MontCtx.fromMont (ctx : MontCtx p) (a : MontResidue p)   : ZMod64 p
```

`MontResidue p` is a `UInt64` newtype carrying the Montgomery-form
invariant; it is **not** a parallel residue type to `ZMod64 p` (its
values are not canonical representatives in `[0, p)`). Use it inside
hot loops only — convert in at the loop header, convert out at the
loop tail. The `CommRing` instance and the Mathlib bridge are stated
for `ZMod64`, not for `MontResidue`.

## Ring instance and properties

- `Lean.Grind.CommRing (ZMod64 p)` derived from the operations on
  the canonical representative; associativity and distributivity
  reduce to `Nat.mod` properties on the logical bodies. (The
  `@[extern]` on `mul` is a runtime hook; the proof obligation is
  about the logical body, not the C body.)
- `IsCharP (ZMod64 p) p`.
- `inv a * a = 1` when `Nat.Coprime a.val.toNat p` — via extended
  GCD from `hex-arith`: `s * a + t * p = 1` gives `s mod p` as the
  inverse.
- No zero divisors for prime `p`: `a * b = 0 → a = 0 ∨ b = 0` — via
  Euclid's lemma from `hex-arith`.
- Fermat's little theorem: `a ^ p = a` — lifts directly from
  `Nat.pow_prime_mod` in `hex-arith`.

## Why not `Fin n`?

`Fin n` already has `Lean.Grind.CommRing` and `IsCharP`, but its
runtime model is a `Nat` paired with a proof — every operation
routes through GMP arbitrary-precision arithmetic. `ZMod64 p`
exists to put the value in a `UInt64` and route every operation
through native machine arithmetic, with `mul`, `pow`, and `inv` going through
the mandatory C externs above.

The separate full-word `WordMod` surface retains transparent logical bodies
for `addModWord` and `subModWord` while compiled calls use scalar C externs.
These implement conditional word addition/subtraction directly and avoid
allocating Lean carry pairs in polynomial coefficient loops. The runtime and
logical bodies agree for the full word-modulus range, including operands near
`UInt64`'s upper limit.

## Reusable number-theoretic transforms

This library owns the radix-2 transform used by
[hex-poly-fast](../../SPEC/Libraries/hex-poly-fast.md), because the transform
is an operation on `ZMod64` vectors and is useful independently of any
polynomial representation.

`ZMod64.NttPlan p n` packages a power-of-two length, a root of exact order
`n`, its inverse, the inverse of `n`, and reusable forward/inverse twiddle
tables with Shoup preconditioners. `NttPlan.build?` validates the length and
root conditions; fixed auxiliary primes provide pre-verified plans for every
supported smaller length. Plan construction and transform execution are
separate benchmark operations, and callers pass plans explicitly rather than
consulting a mutable global cache.

Forward butterflies use Harvey's redundant interval `[0, 2p)` and inverse
butterflies use `[0, 4p)`. The raw words are bounded internal structures, not
a second modular type and not a ring instance. The existing `p < 2^31` bound
proves the intermediate additions fit in `UInt64`; multiplication by a
twiddle uses the existing high-word primitive and a precomputed Shoup
constant. Canonical normalization occurs only at transform boundaries.

Required theorems identify each butterfly modulo `p`, prove its raw output
bound, identify the whole forward transform with the DFT, and prove inverse
after forward is the identity. Pointwise multiplication between transforms
then gives cyclic convolution; a primitive `2n`th root gives negacyclic
convolution. No new `@[extern]` is introduced for the first implementation.

The fixed `NttPrime` catalogue records a prime below `2^31`, a maximum
power-of-two length, and a root of that exact order. It is finite by design;
failure to supply a requested transform is reported as `none` so polynomial
dispatchers can select a different verified kernel.

## External comparators

No external comparator is required.

**Justification:** scalar operations are `implementation-is-extern` per
`SPEC/benchmarking.md §"Comparator naming"`: they route through GMP or the
dedicated word-arithmetic C externs, leaving no algorithmically distinct
external implementation. The NTT surface is an internal building block rather
than a user-facing result type; FLINT comparison belongs to the `FpPoly` and
`ZPoly` convolution consumers where inputs and outputs match.

The architecturally important within-Lean comparisons — Barrett versus
Montgomery modular multiplication, and canonical versus redundant-residue
butterflies — are registered as
`compare` groups in `HexModArith/Bench.lean` (per
`SPEC/benchmarking.md §"Within-Lean comparisons"`). Those
comparisons are the right shape for this library; an external tool
would just be wrapping the same underlying word-level operations.
