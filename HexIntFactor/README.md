# hex-int-factor

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified natural-number factorization, divisor functions, multiplicative
orders, and primitive roots for Lean 4, without Mathlib. It builds on
[`hex-primality`](https://github.com/leanprover/hex-primality),
[`hex-arith`](https://github.com/leanprover/hex-arith), and
[`hex-basic`](https://github.com/leanprover/hex-basic). Correspondence with
Mathlib's factorization and order APIs lives in
[`hex-int-factor-mathlib`](https://github.com/leanprover/hex-int-factor-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-int-factor"
git = "https://github.com/leanprover/hex-int-factor.git"
rev = "main"
```

```lean
import HexIntFactor
open Hex Hex.Nat
set_option maxRecDepth 100000

def twelve : CheckedFactorization 12 :=
  ⟨⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩, rfl, by decide⟩

#guard checkFactorization twelve.raw
#guard divisors twelve == #[1, 2, 3, 4, 6, 12]
#guard totient twelve == 4
#guard squarefreePart twelve == 3
#guard squareDivisor twelve == 2
```

# Functionality

- `factor?` searches for a complete checked factorization with explicit
  randomness and a finite fuel budget. `factorPartial?` retains a checked
  residual when complete search exhausts its budget. Both accept
  `(pMinusOneStage2 := true)` to enable
  the continuation from bound 64 to 4096; the option defaults to `false`.
  It uses one extra counted attempt when fuel permits, preserving the four
  stage-1 calls (through bound 9999) and the ECM allocation.
- Both factorization APIs also accept `(squfof := .first limits)` to try
  explicitly bounded SQUFOF before rho, or `.rescue limits` after the existing
  splitters fail. The default is `.off`. The policy applies recursively and
  carries its own attempt, step, and queue limits. See the
  [complete-factorization examples and native timings](https://github.com/kim-em/hex-dev/blob/main/reports/hex-int-factor-squfof.md).
- `checkFactorization` and `checkPartial` replay untrusted factorization data.
  Prime entries carry `hex-primality` certificates, and bounded products reject
  oversized powers before constructing them.
- `divisors`, `numDivisors`, `sigma`, `totient`, `radical`, `squarefreePart`,
  `squareDivisor`, and `isSquarefree` compute from a `CheckedFactorization`.
- `checkOrder`, `isPrimitiveRoot`, and `primitiveRoot?` use a complete
  factorization of the proposed order. `carmichael` computes the Carmichael
  exponent from a complete factorization.
- `rhoSplit?`, `pMinusOneFactor`, and `ecmStage1` expose the individual split
  routes. `pMinusOneStage2Counted` continues a saved residue, and
  `pMinusOneSearchCounted` includes stage 1. Counted factor search retains
  ordered p−1 and ECM diagnostics on success and exhaustion.
  `factorPower?` adds a cyclotomic pre-split for `b ^ n ± 1`.

# Certificate construction

For bounded construction of secp256k1, P-384 and Curve448 certificates, import
`HexIntFactor.Construction` and `HexPrimality.Elab`, then use
`primality? (factor := Hex.Nat.ecmFactorSearch)` with a local
`set_option maxHeartbeats 4000000`. This explicit ECM route keeps the default
primality and factorization portfolios unchanged. Apply its emitted literal
certificate to avoid repeating search.

# Optional external production

`importFactors budget subject proposal rand` is a pure importer. A proposal
contains a signed subject and `(base, exponent, optionalPrimeCert)` entries.
Unsorted and repeated entries are validated before canonicalization. Every
accepted prime power carries a checked `PrimeCert`; omitted factors, composite
bases and unfinished primality completion remain in a checked residual.

```lean
import HexIntFactor.Import
open Hex Hex.Nat

#guard match importFactors {} 72
    ⟨72, [(3, 2, none), (2, 3, none)]⟩ (Rand.ofSeed 72) with
  | .ok r => r.value.raw.residual == 1
  | .error _ => false
```

Install PARI/GP separately, then put this explicit production command in a
batch module:

```lean
import HexIntFactor.Export
#int_factor_export MyFactors.Product cert for 72
```

Run `lake build +YourModule`. The command creates `MyFactors/Product.lean`
exclusively; remove the command afterwards. `#int_factor for 72` instead prints
the complete source for copying. `HEX_INT_FACTOR_GP` selects the executable;
otherwise the producer runs `gp` directly with a private request file.
The language server gives batch instructions and performs no production or
writing. Ordinary native APIs retain their default behavior.

Later modules need only `import MyFactors.Product` and can use
`MyFactors.Product.cert_checked : Hex.Nat.CheckedFactorization 72`.
Frozen source imports only `HexIntFactor.Replay`, with exposed raw data and
acceptance tied to the requested subject. Replay needs neither GP nor search.
The [manual](https://github.com/kim-em/hex-dev/blob/main/HexManual/Chapters/HexIntFactor.lean)
builds the pure-import and frozen complete/partial examples.

The initial POSIX producer limits subjects to 256 bits, entries to 64, decimal
fields to 78 digits, exponents to 256, stdout to 16448 bytes, stderr to 4096
bytes and runtime to 30 seconds. Import separately limits primality-certificate
syntax to 4096 nodes and depth 64, and allocates 128 native construction attempts
per distinct uncertified base. Export caps source at 262144 bytes.

Discovery does not certify primality. Missing GP, process/parse failure, invalid
arithmetic and unfinished certification have distinct diagnostics. Backend
failure invokes native search under a separate finite allocation; partial
certified progress is retained. Exhausted prime completion remains unresolved.
See the [capability and cost report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-int-factor-external.md)
for all frozen subjects and outcomes, including a discovered 255-bit base whose
completion exhausts. These examples make no general 60-digit capability claim.

# Verification

Every accepted complete certificate has positive subject, canonical positive
prime-power entries, exact product, complete prime support, and exact
multiplicities:

```lean
theorem checkFactorization_prod {F : Factorization}
    (h : checkFactorization F = true) :
    (F.factors.map (fun e => e.prime ^ e.exponent)).prod = F.subject

theorem checkFactorization_primeSupport {F : Factorization}
    (h : checkFactorization F = true) {q : Nat} (hq : Prime q) :
    q ∣ F.subject ↔ ∃ e ∈ F.factors, e.prime = q
```

Factor search is deliberately partial: zero, exhausted search, and internal
checker rejection are distinct `FactorStop` cases, with the advanced random
state and checked partial snapshot retained where available. Split algorithms
are untrusted producers; only Lean-checked certificates cross the public
correctness boundary. See the [SPEC](SPEC/hex-int-factor.md) for the route and
fuel contracts.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
