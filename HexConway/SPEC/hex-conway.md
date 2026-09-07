# hex-conway (verified imported Conway polynomials)

HexConway is a Mathlib-free library of imported Conway polynomials. It depends
on HexBerlekamp for Rabin soundness and HexPrimality for factor-prime
certificates. Coefficients are Lübeck's choice. The proofs establish
irreducibility, primitivity, and compatibility; they do **not** establish
lexicographic minimality.

## Verified scope

The exact supported pairs are committed in `scripts/conway/scope.json` and
exported as `Hex.Conway.supportedPairs`. The README lists the concrete coverage.
Every advertised entry must have all of the following:

- a prime characteristic within the `ZMod64` bounds;
- a monic polynomial of the degree specified by its lookup key;
- a kernel-checked Rabin irreducibility certificate;
- primitivity of the quotient's distinguished generator;
- compatibility with every supported positive proper-divisor degree.

The scope must preserve existing supported pairs and be closed under positive
degree divisors. A coefficient row in the source cache is not verified library
coverage. Nonrectangular scopes must be described by their exact pairs or by
ranges with explicit exceptions. Prefer broad low-degree coverage and useful
depth in small characteristic over adding degree-one entries alone.

`luebeckConwayPolynomial? p n` returns `none` outside this scope. A
`SupportedEntry p n` packages a successful lookup, its polynomial and a
characteristic-primality witness. `conwayPoly` recovers the selected modulus;
`conwayPoly_monic`, `conwayPoly_nonconstant`, `conwayPoly_irreducible` and
`luebeckConwayPolynomial?_degree_eq` provide the field-construction facts.

## Rebuild budget

The ceiling is **300 seconds for a clean rebuild of Conway-specific code and
proofs with dependencies already built**. Measure `lake build HexConway`,
including coefficient tables, polynomial literals, supported-entry APIs,
irreducibility, primitivity, compatibility, regeneration tools, and the
library's normal Lean and C outputs. Remove every Conway output before each
run; do not restore those outputs from a build cache. Retain dependency caches.

Use a named benchmark machine, fixed Lean version, and fixed parallelism. The
report must identify the command, thread settings, generated-module scheduling,
and source hashes. Run the baseline and candidate scopes at least three times;
the accepted scope must remain below the ceiling in all three runs. Record
wall time, per-module costs, peak memory and generated artifact sizes. Measure
additional `HexGFqMathlib` rebuild costs separately, including generator-order
specializations and the subfield bridge. Record CI timings as additional
observations, not as a substitute for controlled designated-machine runs.

`scripts/conway/measure.py` removes the Conway output directories, disables
Lake's remote build cache and records these measurements. GNU time's maximum
child RSS and the sampled aggregate process-tree RSS have distinct labels.
Capped runs are lower bounds on an unfinished rebuild, not successful checks.
Compare an added entry together with its missing divisor dependencies and all
new compatibility obligations. Keep compiled runtime measurements distinct
from elaboration and kernel replay.

The initial expansion envelope is degrees 1–32 at characteristic 2, 1–16 at
3, 5 and 7, 1–8 at the other primes below 100, and 1–4 at primes between 100
and 1000. Also assess binary degrees 64 and 128 with their divisor dependencies.
Record unavailable source entries explicitly. If this envelope fits comfortably,
continue expanding; if it exceeds the ceiling, profile expensive cases and
improve verification before selecting a smaller scope. Generated modules may
be sharded. CI keeps the repository's existing single-job convention.

## Deterministic generation and provenance

`scripts/conway/import_source.py` is the explicit network step. It imports
`scripts/conway/candidates.json` from Lübeck's `CPimport.txt`, recording the
source URL, source-file SHA-256, ascending coefficient lists, and unavailable
requested pairs. Ordinary builds neither fetch coefficients nor search for
factorizations or certificates.

`scripts/conway/generate.py` reads that committed input and the exact scope.
With the pinned Python dependency in `scripts/conway/requirements.txt`, it
emits the coefficient dispatcher, literals, supported entries, Rabin
certificates, prime-factor certificates, primitivity facts, every required
compatibility fact, generator-order and subfield-embedding specializations, and the runtime verification
driver. It also emits `HexGFq.CommittedEntry` instances for the same scope.
`--check` checks deterministic regeneration without changing the tree.
The generator rejects missing divisor entries and loss of baseline coverage.
Its arithmetic and searches are untrusted preparation: the generated Lean
proofs must still pass the verified checkers.

The shared `scripts/oracle/luebeck_conway_cache.json` continues to supply the
integer-factorization corpus. The expansion inputs are separate so that changing
verified Conway coverage does not silently change that corpus. The preflight
checks agreement wherever the two caches overlap. Source conformance compares
all supported entries against the pinned expansion input, and optionally
against the `conway-polynomials` package.

The older `rebuild_luebeckConwayPolynomial?` and `#conway_entry_source` commands
remain available for inspecting coefficient and Tier 1 source generation. The
complete regeneration path is the Python generator; neither Lean command runs
implicitly during a build.

## Certificate replay

`HexConway.Power` supplies structural square-and-multiply and structural Horner
composition. Their equality theorems identify them with the existing polynomial
operations. Binary powers avoid work linear in the characteristic. Structural
composition avoids entering a packed implementation that the kernel cannot
reduce; a proved compiler rewrite retains the optimized runtime dispatcher.

Rabin certificates contain the Frobenius chain and Bezout witnesses. The
binary checker is proved equal to the existing incremental Rabin checker,
whose soundness yields irreducibility. There is no new trust assumption.

Primitivity validates a factorization of `N = p^n - 1`, computes the full and
prime-divided exponents directly, and verifies
`α^N = 1` and `α^(N/q) ≠ 1` for every factor prime `q`. A factor-primality proof
is shared across all entries using that prime. Factors below 100000 use bounded
trial division. Larger factors use `Hex.Nat.checkPockArith` with separately
proved child primes through `Hex.Nat.prime_of_pocklington`. Child proofs are
shared in increasing-prime order, so the same table leaf or child certificate
is not repeatedly normalized in different parents. In `GF(2)`,
`N = 1`: an empty factor list and `α^1 = 1` explicitly certify the trivial
multiplicative group.

For compatibility, when `0 < m` and `m ∣ n`, the norm

```
α ^ ((p^n - 1) / (p^m - 1))
```

must be a root of `C(p, m)`. `normX_eq_pow` and `subfieldGen_eq_norm` connect
the executable product of Frobenius images with this exponent.
`eval_conwayPoly_subfieldGen_eq_zero` promotes the checked composition to
vanishing in the quotient. Generated `compat_p_m_n` proofs cover every proper
divisor obligation; `not_compatible_11_4_6` remains a negative control.

`HexGFqMathlib` transports primitivity to `orderOf_gen_p_n` and constructs
`conwayEmbed`, the ring homomorphism sending the smaller generator to the
specified norm in the larger field. These bridges do not replace any
Conway-side certificate replay.

No `native_decide`, new axioms, or unfinished proofs are permitted in completed
certificates.

## Runtime evidence and external comparators

`hexconway_replay` checks the entire supported scope in compiled code and
reports irreducibility, primitivity and compatibility timings separately. Its
mutable polynomial input prevents compile-time folding of closed successful
checks. The LeanBench lookup registration derives its keys from `supportedPairs`;
fixed registrations provide operation budgets and expected-result checks.
See `reports/hex-conway-performance.md` for the measured limits and raw evidence.

Lübeck's database and the optional package adapter are input-source checks,
not independent performance comparators. There is no external executable
comparator for this imported-table service (`input-source-only` under
`SPEC/benchmarking.md`).

## Tier 3

On-demand search for a lexicographically minimal compatible polynomial is a
separate, unimplemented feature. Lookup and verification do not invoke it, and
expanding imported coverage does not reopen that search feature.

Primitivity and compatibility APIs expose named `primitive_p_n` and
`compat_p_m_n` facts for each supported pair. Unlike the irreducibility and
monicity APIs, these do not dispatch over an arbitrary lookup witness.
