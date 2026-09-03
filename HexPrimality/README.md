# hex-primality

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Kernel-checkable primality certificates, bounded primality search, a proved
prime table, prime segments, and a `primality` tactic for Lean 4, without
Mathlib. It builds on [`hex-arith`](https://github.com/leanprover/hex-arith)
and [`hex-basic`](https://github.com/leanprover/hex-basic). Correspondence with
Mathlib's `Nat.Prime` lives in
[`hex-primality-mathlib`](https://github.com/leanprover/hex-primality-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-primality"
git = "https://github.com/leanprover/hex-primality.git"
rev = "main"
```

```lean
import HexPrimality

#eval Hex.Nat.isPrime 10000019
#eval Hex.Nat.primesIn 0 30

example : Hex.Nat.Prime 2147483647 := by primality
```

# Functionality

- `PrimeCert` represents stored-table leaves and the square-root and cube-root
  Pocklington criteria. `checkPrime` replays a certificate by kernel reduction.
- `primeCert?` performs explicitly seeded, fuel-bounded certificate search;
  `isPrime?` is the bounded exact decision and `isPrime` adds a total
  trial-division fallback.
- `millerRabin` and `isProbablePrime` provide runtime compositeness filters.
  A failed test has a sound refutation theorem; a passing test is not proof of
  primality.
- `rhoFactor?` and `pMinusOneStage1` expose the bounded factor primitives used
  during certificate search. Every returned factor is validated by a theorem.
- `isTablePrime` queries the proved table of primes below `100000`, while
  `primesIn` enumerates any finite interval by exact trial division.
- `nextPrime?` performs a bounded least-prime search and `orderOf` computes
  multiplicative order with a complete correctness API.

# Verification

Certificate search, random choices, and factor discovery are untrusted
producers. Only the exposed Boolean checker and its Lean proof establish
primality. Successful bounded and total decisions are exact, and every
successful factor search returns a proper divisor.

```lean
theorem prime_of_checkPrimeAt {n : Nat} {c : PrimeCert}
    (h : (c.subject == n && checkPrime c) = true) : Prime n

theorem isPrime_iff {n : Nat} : isPrime n = true ↔ Prime n

theorem rhoFactor?_spec {n d : Nat} {r r' : Rand} {fuel : Nat}
    (h : rhoFactor? n r fuel = .ok (d, r')) : 1 < d ∧ d < n ∧ d ∣ n
```

The `primality` elaborator supports certificate proofs through 512 input bits
under a fixed, bounded search policy. Search exhaustion is reported and never
turned into a mathematical result. See the [SPEC](SPEC/hex-primality.md) for
the exact fuel, failure, and trust contracts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
