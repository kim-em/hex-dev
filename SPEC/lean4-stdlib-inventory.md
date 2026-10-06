# Lean 4 stdlib inventory (v4.28.0)

What we get for free and what we need to build.

**Available:**
- `Nat.gcd` / `Int.gcd` — GMP-backed via `@[extern "lean_nat_gcd"]`
- `Nat.divExact` / `Int.divExact` — GMP-backed (`mpz_divexact`), requires
  divisibility proof; faster than regular division
- `Nat.Coprime` — `gcd m n = 1`, decidable, with lemmas
- `Nat.lcm` / `Int.lcm`
- `Rat` — proper rational field with `Lean.Grind.Field` instance
- `Vector α n` — `Array α` with size proof, rich API (~19 files)
- `Fin n` — modular arithmetic with `Lean.Grind.CommRing` and `IsCharP`
- `BitVec w` — `Fin (2^w)`, extensive API, `bv_decide` support
- `Std.HashMap` / `Std.ExtHashMap` — the latter has extensionality
- `Lean.Grind.{Semiring, Ring, CommSemiring, CommRing, Field}` hierarchy

**Not available (we build):**
- Extended GCD / Bezout coefficients — completely absent
- Modular exponentiation — absent as a stdlib primitive, but this
  project's specified path is a pure Lean implementation
- Modular inverse — absent as a stdlib primitive, but this project's
  specified path is via extended GCD
- Primality testing — absent (not needed for this project; Berlekamp-
  Zassenhaus only needs small known primes)
- Polynomial types — none (only internal `grind` polynomials)
- Matrix types — none
- Finite field types / `ZMod` — absent (only `Fin n`)

**GMP primitives to expose (via `@[extern]` FFI, ideally upstreamed):**
- `mpz_gcdext` — extended GCD with Bezout coefficients, exposed by the
  temporary `Nat.extendedGcd` backport of
  [lean4#15160](https://github.com/leanprover/lean4/pull/15160).
  Hex's signed API uses a proved compiler rewrite. See "Extern contract:
  `Nat.extendedGcd`" in `../HexArith/SPEC/hex-arith.md`. Remove the backport
  when the pinned toolchain provides the upstream primitive.

**Hardware intrinsics exposed via `@[extern]`:**
- `clmul` (64×64 carry-less multiply) — landed in `hex-gf2` as the
  `clmul` extern. Backed by CLMUL on x86-64 and `vmull_p64` on
  aarch64. See the "Extern contract: `clmul`" section in
  `Libraries/hex-gf2.md`.

Every new `@[extern]` boundary in this project must ship with an
analogous "Extern contract" section in the owning library spec, per
the project-wide policy in `SPEC.md`.
