# hex-primality-mathlib (depends on hex-primality + Mathlib)

The Mathlib bridge for
[hex-primality](../../HexPrimality/SPEC/hex-primality.md). It identifies
`Hex.Nat.Prime` with Mathlib's `Nat.Prime`, transports the core decision,
search, and initial-segment results, extends the bare `primality` tactic to
`Nat.Prime` goals, and provides an explicit opt-in `Nat.Prime` `norm_num`
policy.

This is not a correspondence-only layer. Its elaborators choose registrations,
dispatch between proof-producing routes, run bounded untrusted search, and
reify terms for kernel checking. This SPEC therefore owns their success,
decline, failure, resource, conformance, and proof-performance contracts.

## Ownership boundary

The core SPEC owns every Mathlib-free predicate, table, sieve, Miller--Rabin
test, certificate type, certificate search, factor-search primitive, checker,
and correctness theorem. In particular, this layer does not respecify
`primeCert?`, `rhoFactorCountedWith?`, `checkPrime`, or the core elaboration
policy. Their algorithms and bounds remain normative in
[the core API and tactic sections](../../HexPrimality/SPEC/hex-primality.md#the-api).

This SPEC owns only the Mathlib-facing correspondence and transport theorems,
the `Nat.Prime` tactic handler, the opt-in `norm_num` registrations and command,
the bridge-specific negative-result policy, and the evidence that those paths
elaborate kernel-checked proofs within their accepted budgets. A future
Mathlib-side primality dependency or additional elaborator also belongs here;
it must remain an accelerator over the core checker rather than a replacement
for the Mathlib-free proof boundary.

## Correspondence and transports

The whole predicate correspondence is:

```lean
theorem Hex.Nat.prime_iff {n : Nat} :
    Hex.Nat.Prime n ↔ Nat.Prime n
```

The two predicates have the same divisor characterization after unfolding
Mathlib's irreducibility packaging. Every bridge theorem transports a core
result through this equivalence; it does not introduce a second primality
argument.

The certificate, decision, compositeness, and successful-search transports
are:

```lean
theorem Hex.Nat.natPrime_of_checkPrime {c : PrimeCert}
    (h : checkPrime c = true) : Nat.Prime c.subject

theorem Hex.Nat.natPrime_of_checkPrimeAt {n : Nat} {c : PrimeCert}
    (h : (c.subject == n && checkPrime c) = true) : Nat.Prime n

theorem Hex.Nat.isPrime_iff_natPrime {n : Nat} :
    isPrime n = true ↔ Nat.Prime n

theorem Hex.Nat.millerRabin_refutes_natPrime {n a : Nat}
    (h : millerRabin n a = false) : ¬ Nat.Prime n

theorem Hex.Nat.nextPrime?_natPrime {n : Nat} {r : Rand}
    {fuel p : Nat} {r' : Rand}
    (h : nextPrime? n r fuel = .ok (p, r')) :
    n < p ∧ Nat.Prime p ∧
      ∀ q, n < q → q < p → ¬ Nat.Prime q
```

No `DecidablePred Nat.Prime` instance is declared. Mathlib's
`Nat.decidablePrime` remains the selected global instance; the bridge adds
proof transports and elaborator routes without creating instance-selection
churn.

## Initial-segment transports

The committed table and range enumeration remain core data. This layer states
their results in the forms used by Mathlib consumers:

```lean
theorem Hex.Nat.primeTable_spec :
    ∀ n < primeTableBound, (n ∈ primeTable ↔ Nat.Prime n)

theorem Hex.Nat.primesIn_spec (lo hi : Nat) :
    ∀ n, n ∈ primesIn lo hi ↔ lo ≤ n ∧ n < hi ∧ Nat.Prime n

theorem Hex.Nat.filter_prime_range [DecidablePred Nat.Prime]
    {bound : Nat} (h : bound ≤ primeTableBound) :
    (Finset.range bound).filter Nat.Prime =
      (primeTable.toList.filter (fun p => p < bound)).toFinset

theorem Hex.Nat.forall_prime_lt {P : Nat → Prop} {bound : Nat}
    (hb : bound ≤ primeTableBound)
    (h : ∀ p ∈ primeTable, p < bound → P p) :
    ∀ p, p < bound → Nat.Prime p → P p
```

`filter_prime_range` exposes the complete table as a `Finset`; the
quantified `forall_prime_lt` form lets a caller discharge a property by a
decidable fold over the committed literal. Sieve generation, table
verification, and the unrestricted `primesIn` algorithm stay in the core
SPEC.

## `Nat.Prime` elaboration routes

### Bare `primality`

After importing this library, bare `primality` closes a goal whose target is
definitionally `Nat.Prime n` for a closed natural-number numeral `n`. It uses
the core certificate route and emits `natPrime_of_checkPrimeAt` applied to the
reified certificate and a single reducible Boolean equality. Compiled search
is untrusted; the elaborator first self-checks the certificate and the kernel
then replays `checkPrime`.

The bridge registers its handler on the existing `primality` syntax kind.
Later registration gives it first refusal. A goal with any other head is
declined with `unsupportedSyntax`, after which the core handler continues to
support `Hex.Nat.Prime`. The bridge does not replace the term form
`primality n`, nor the tactic forms `primality n` and `primality h : n` that
introduce a hypothesis: those forms retain their core result type
`Hex.Nat.Prime n`.

The handler shares the core's named `withinPrimalityBudget`, `primalityFuel`,
and `primalitySearchBudget` definitions. The positive certificate input,
recursive-fuel, rho-restart, and rho-step limits therefore have one executable
and normative owner; their current values and evidence are specified in
[the core tactic contract](../../HexPrimality/SPEC/hex-primality.md#the-tactic).
The bridge must not copy those constants or silently widen them.

### Default and opt-in `norm_num`

An ordinary import leaves Mathlib's previously registered `Nat.Prime`
extension first in precedence. Thus `norm_num` retains pinned Mathlib's
trial-division behavior unless the current module contains:

```lean
use_hex_primality_norm_num
```

The command locally removes Mathlib's original registration. It exposes a
guarded alias of that extension for numerals below
`natPrimeCertThreshold = 2^24`, followed by the Hex certificate extension at
and above the threshold. Attribute erasure does not cross an import boundary:
each importing module must opt in independently.

On the certificate tier, positive results use the same bounded search,
compiled self-check, reification, and kernel replay as bare `primality`.
Negative results are supported only after certificate search returns the
fixed-tier `.composite` verdict. They use the separately bounded factor route
below. Neither Hex extension invokes the total `isPrime` decision.

## Negative-result policy

For an admitted numeral `n`, certificate search starts from
`Hex.Rand.ofSeed n`. If it returns `.composite`, factor search resumes the
returned state with:

```lean
Hex.Nat.Internal.rhoFactorCountedWith? n failure.rand
  natPrimeRhoRestartBudget natPrimeRhoStepBudget
```

where `natPrimeRhoRestartBudget = 1` and
`natPrimeRhoStepBudget = 2^16` Brent cycle steps per restart throughout the
supported input range. The current root-composite preflight consumes zero
attempts and leaves the seeded state unchanged; conformance pins that fact for
deterministic replay. The factor primitive's parity preflight may return
factor `2` without consuming a restart.

Every returned candidate `d` is revalidated as `1 < d`, `d < n`, and
`n % d = 0`. Only then may Mathlib's `deriveNotPrime` construct an
independently kernel-checked proper-factor proof. A Miller--Rabin verdict
selects this branch but never appears as the emitted negative proof.

If certificate search returns `.exhausted`, negative factor search does not
run. If factor search exhausts or returns an invalid candidate, the certificate
extension declines. The guarded trial alias also declines at and above
`2^24`, so none of these outcomes starts total or unbounded trial division.
Inputs outside the core elaboration ceiling decline before certificate or
negative-factor search.

## Success, decline, failure, and timeout semantics

| entry point and condition | required outcome |
|---|---|
| bare `primality`, accepted prime numeral | close the goal with a reified, kernel-replayed certificate proof |
| bare `primality`, composite numeral | report that the numeral is not prime, including a fixed-base Miller--Rabin witness when available |
| bare `primality`, certificate exhaustion | report exact attempts, seed, selected fuel, and policy maxima; state that no total decision ran |
| bare `primality`, over-budget numeral | reject before certificate search with the supported bit ceiling |
| bare `primality`, open or non-numeral `Nat.Prime` target | report the closed-numeral requirement |
| bridge handler, non-`Nat.Prime` target | decline so the core handler or another syntax handler can run |
| default `norm_num` | preserve pinned Mathlib registration and behavior |
| opted-in `norm_num`, numeral below `2^24` | delegate to the guarded Mathlib trial extension |
| opted-in `norm_num`, certificate-tier prime | emit the checked positive certificate proof |
| opted-in `norm_num`, certificate-tier composite with a valid factor | emit the independently checked proper-factor proof |
| opted-in `norm_num`, unsupported shape, over-budget input, or bounded exhaustion | decline; if no other extension applies, leave an unsolved goal |

An internal certificate self-check failure is never converted into a proof.
Bare `primality` reports it as an internal error; the `norm_num` extension
declines.

The resource contract is a **10-second absolute wall-clock gate for a fresh
importing module** on the designated benchmark host. It includes Lake
traversal, imports, compiled search and self-check, term construction, and
kernel replay. It is not an internal ten-second tactic timer and is not an
import-subtracted delta. A benchmark timeout or an ordinary Lean resource
interruption emits no proof; a row exceeding the absolute gate invalidates the
performance evidence rather than changing elaborator semantics.

## Conformance and proof-performance ownership

The bridge owns `conformance/HexPrimalityMathlib/Conformance.lean` and
`OptInConformance.lean`. Together they cover correspondence-facing tactic
use, default registration, module-local opt-in precedence, both sides of the
`2^24` threshold, positive and negative certificate-tier results,
deterministic seed/state replay, parity without a restart, exact negative
exhaustion, the input ceiling, ordinary failure diagnostics, import-boundary
locality, and preservation of `Nat.decidablePrime`.

Fresh importing modules under
`bench/HexPrimalityMathlib/ProofProbe/` own proof-production evidence. The
`Mathlib512`, `MathlibExhausted`, and `MathlibOverBudget` probes cover the
shared positive policy; `MathlibBaseline` is their import control. The
`Negative*` probes cover factor-found inputs at 25, 32, 64, 65, and 512 bits,
both parity and odd-factor cases, plus balanced 512-bit exhaustion.

The positive-route harness and evidence are shared with the core policy and
are cited by the core SPEC. The bridge-specific negative harness is
`scripts/bench/primality_negative_sweep.py`. Its designated-host record,
`reports/bench-results/hex-primality-negative-policy-issue-9803-chungus2.json`,
contains six balanced samples per row. Every substantive row passes the
10-second absolute gate; the maximum observed candidate wall times range from
2.131 seconds to 3.318 seconds. Import-subtracted values remain diagnostic and
need not resolve above the null envelope.

These probes are proof-performance evidence, not a claim that the layer is
correspondence-only and exempt from review. Any change to registration,
dispatch, thresholds, search budgets, reification, emitted proof shape, or
imports must refresh the affected conformance and fresh-module evidence.

## Review and attestation

Phase-2 review treats `HexPrimality` and `HexPrimalityMathlib` as distinct
libraries with distinct owned specifications. The core attestation is reviewed
against `HexPrimality/SPEC/hex-primality.md`; the bridge attestation is reviewed
against this file. A pair-level review or report must identify both SPEC owners
rather than citing the core SPEC as authority for bridge registration,
failure, resource, or evidence semantics.

## File organization

```text
HexPrimalityMathlib/
  Prime.lean       -- prime_iff and core-result transports
  Segment.lean     -- table and range statements in Mathlib vocabulary
  NormNum.lean     -- Nat.Prime tactic handler and opt-in norm_num policy
  SPEC/
    hex-primality-mathlib.md
HexPrimalityMathlib.lean

conformance/HexPrimalityMathlib/
  Conformance.lean
  OptInConformance.lean
bench/HexPrimalityMathlib/ProofProbe/
```
