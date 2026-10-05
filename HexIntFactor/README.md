# hex-int-factor

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified natural-number factorization, divisor functions, multiplicative
orders, and primitive roots for Lean 4, without Mathlib. It builds on
[`hex-primality`](https://github.com/leanprover/hex-primality),
[`hex-arith`](https://github.com/leanprover/hex-arith), and
[`hex-basic`](https://github.com/leanprover/hex-basic). The optional mixed
extension uses [`hex-ecpp`](https://github.com/leanprover/hex-ecpp). Correspondence with
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

Import `HexIntFactor` and use `primality?` to search for Pocklington
certificates with Pollard's p-minus-one method, rho and ECM. The search
shares one finite attempt allowance across factoring, recursive child proofs
and witnesses. It proves the secp256k1, P-384 and Curve448 field primes
without supplied factors; these examples use local
`set_option maxHeartbeats 4000000`.

Apply the emitted literal certificate to keep search out of later builds.
With `HexPrimalityMathlib` also imported, the same tactic proves `Nat.Prime`.
Ordinary `primality` and integer factorization use their separate portfolios.
`primality? (factor := Hex.Nat.interleavedConstructionFactor)` explicitly
selects the new provider; `Hex.Nat.ecmFactorSearch` retains the original
fixed-curve provider. Importing only `HexPrimality` keeps its core-only
construction policy.

# Optional external production

`importFactors budget subject proposal rand` is a pure importer. A proposal
contains a signed subject and `(base, exponent, optionalPrimeCert)` entries.
Unsorted and repeated entries are validated before canonicalization. Every
accepted prime power carries a checked `PrimeCert`; omitted factors, composite
bases and unfinished primality completion remain in a checked residual. Zero
completion attempts report skipped work, which the external-assisted route may
handle with its separate native allocation. Exhausted completion stays unresolved.

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

# Optional mixed ECPP evidence

Import `HexIntFactor.Mixed.Replay` for `Hex.Nat.Mixed` complete and partial
certificates carrying either `Evidence.legacy` or `Evidence.ecpp`. Every entry
binds evidence to its base; checked types bind the result to the requested
subject. Product and ordering theorems are unconditional in the computational
library. Primality and prime-support facts take an explicit ECPP soundness
hypothesis, discharged by `HexIntFactorMathlib.Mixed`.

`HexIntFactor.Mixed.Import` supplies the pure importer. ECPP is disabled by
default; `{ ecppBits := some 256 }` or `{ ecppBits := some 512 }` explicitly
selects native completion after the legacy route. Independent defaults admit
4096 subject bits, 512 base/evidence bits, 64 entries, exponents through 4096,
4096 legacy syntax nodes and depth 64, 20 ECPP rows, 32 constructor nodes
including the base wrapper and terminal evidence, and 1024 inverses per row.
Structural budgets can tighten these ceilings. Legacy work has at most 128
attempts per base and 8192 shared attempts; ECPP reserves two full public-policy
calls without refunding failures. `ecppSeed + callIndex` is independent of the
legacy random stream. Results retain completion counters, states and distinct
exhaustion diagnostics.

Batch commands use closed exposed constructor data and numeral subjects:

```lean
import HexIntFactor.Mixed.Export
#int_factor_mixed (ecpp := 512) for 72 using ⟨72, [(2, 3, none), (3, 2, none)]⟩
#int_factor_mixed_export MyFactors.Mixed cert for 72 using ⟨72, [(2, 3, none), (3, 2, none)]⟩
```

Select `(method := pari)` instead of `using proposal` for the existing bounded
256-bit factor-discovery process. Supplied proposals support larger subjects;
ordinary completion is subprocess-free. Exports are exclusive, public and
exposed, with acceptance freshly checked in the kernel before any suggestion
or write. Source is capped at 2 MiB, expanded syntax at 1048576 nodes, and proof
replay at 20000000 heartbeats and recursion depth 65536. Editor execution only
prints batch instructions. Generated source imports `Mixed.Replay` alone.

The [frozen capability report](https://github.com/kim-em/hex-dev/blob/main/reports/intfactor/mixed/README.md)
records two complete mixed products containing ECPP-certified 512-bit bases
where the recorded legacy allocation exhausts, and a retained partial result.
A partial residual has no primality claim and may contain more powers of a
listed prime. `ofLegacy` embeds legacy data; checked `toLegacy` accepts only
legacy-bearing entries and replays the legacy checker. Existing divisor,
totient, order and square-decomposition APIs consume the legacy representation.

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
