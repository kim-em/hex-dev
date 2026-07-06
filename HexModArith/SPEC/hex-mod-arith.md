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
representative. `mul` and `pow` carry mandatory `@[extern]` runtime
paths; `add`/`sub` are one-line `ofNat` specifications, with the
division-free branchy `UInt64` bodies in `addImpl`/`subImpl` behind
proved `@[csimp]` equalities (design principle 11), and `inv` routes
through the
`@[extern "lean_hex_mpz_gcdext"]`-bearing `extGcd` declared in
`HexArith.Int` (see "Extern contract: `mpz_gcdext`" in
`SPEC/Libraries/hex-arith.md`). **`inv` must NOT call
`Hex.pureIntExtGcd` directly** — that's the pure-Lean reference
body the extern falls through to as a portable fallback, and is
intended for proofs only. Calling it bypasses GMP and runs the
recursive `Nat` reference at runtime, which allocates a fresh `Nat`
blob per recursive step (the same regression class as omitting
`@[extern]` on `mulHi`).

```lean
@[extern "lean_hex_zmod64_mul"]
def ZMod64.mul (a b : ZMod64 p) : ZMod64 p := ...   -- contract below
def ZMod64.add (a b : ZMod64 p) : ZMod64 p          -- spec: ofNat; runtime: addImpl (@[csimp])
def ZMod64.sub (a b : ZMod64 p) : ZMod64 p          -- spec: ofNat; runtime: subImpl (@[csimp])
def ZMod64.zero : ZMod64 p
def ZMod64.one  : ZMod64 p                          -- equals zero when p = 1
def ZMod64.inv  (a : ZMod64 p) : ZMod64 p           -- via Hex.Int.extGcd
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
through native machine arithmetic, with `mul` going through the
mandatory C extern above and the rest compiling to native UInt64
ops in pure Lean.

## External comparators

No external comparator is required.

**Justification:** `implementation-is-extern` per
`SPEC/benchmarking.md §"Comparator naming"`. HexModArith's modular
operations route through GMP (for `Nat`/`Int` residue arithmetic)
or through the dedicated `UInt64`-modular C extern (for `ZMod64`).
The Phase-4 surface is GMP / native arithmetic; there is no
algorithmically distinct reference implementation to compare
against externally.

The architecturally important within-Lean comparison — Barrett
versus Montgomery modular multiplication — is registered as a
`compare` group in `HexModArith/Bench.lean` (per
`SPEC/benchmarking.md §"Within-Lean comparisons"`). That
comparison is the right shape for this library; an external tool
would just be wrapping the same underlying word-level operations.
