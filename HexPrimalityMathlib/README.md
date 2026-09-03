# hex-primality-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence and tactic layer for
[`hex-primality`](https://github.com/leanprover/hex-primality). It identifies
the Mathlib-free prime predicate with Mathlib's `Nat.Prime`, transports the
certificate and segment theorems, extends `primality`, and provides an
explicitly opted-in bounded `norm_num` policy.

# Quickstart

```toml
[[require]]
name = "hex-primality-mathlib"
git = "https://github.com/leanprover/hex-primality-mathlib.git"
rev = "main"
```

```lean
import HexPrimalityMathlib

example : Hex.Nat.Prime 65537 ↔ Nat.Prime 65537 :=
  Hex.Nat.prime_iff

example : Nat.Prime 2147483647 := by primality
```

# Functionality

- `prime_iff` is the headline equivalence between `Hex.Nat.Prime` and
  `Nat.Prime`.
- `natPrime_of_checkPrime` and `natPrime_of_checkPrimeAt` transport accepted
  Pocklington certificates directly into Mathlib's vocabulary.
- `isPrime_iff_natPrime`, `millerRabin_refutes_natPrime`, and
  `nextPrime?_natPrime` transport the executable decision and search results.
- `primeTable_spec`, `primesIn_spec`, `filter_prime_range`, and
  `forall_prime_lt` expose the proved table and segment API through Mathlib.
- `primality` handles closed `Nat.Prime` goals. The
  `use_hex_primality_norm_num` command selects a bounded, thresholded
  `norm_num` policy for the current module without replacing Mathlib's global
  prime-decision instance.

# Verification

The bridge introduces no new primality search or decision procedure. Positive
proofs replay `hex-primality` certificates; negative `norm_num` proofs validate
a proper factor before using Mathlib's proof constructor. Unsupported inputs
and bounded-search exhaustion decline without an unbounded fallback.

```lean
theorem prime_iff {n : Nat} :
    Hex.Nat.Prime n ↔ Nat.Prime n

theorem primeTable_spec :
    ∀ n < primeTableBound, (n ∈ primeTable ↔ Nat.Prime n)

theorem natPrime_of_checkPrimeAt {n : Nat} {c : PrimeCert}
    (h : (c.subject == n && checkPrime c) = true) : Nat.Prime n
```

Use [`hex-primality`](https://github.com/leanprover/hex-primality) alone for
Mathlib-free computation. See the
[SPEC](SPEC/hex-primality-mathlib.md) for tactic registration, thresholds,
failure semantics, and resource bounds.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
