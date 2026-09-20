# ECM stage 2 on the remaining field primes

The explicit bounded ECM provider constructs **secp256k1, P-384 and Curve448**,
and their exact literal certificates pass ordinary kernel replay. Use:

```lean
import HexIntFactor.Construction
import HexPrimality.Elab

set_option maxHeartbeats 4000000 in
example : Hex.Nat.Prime
    115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  primality? (factor := Hex.Nat.ecmFactorSearch)
```

The implementation decision is to ship this **explicit** downstream provider,
with 64 deterministic curves per unresolved component, bounds 32768/524288 and
the existing 1024 total attempts. Plain `primality?` and ordinary factorization
keep their portfolios: the three primes remain unsupported by the plain tactic.
No named prime in this investigation remains unsupported by the explicit route.
P-521 keeps the same certificate and 170 attempts under either route. Search
cost is tens of seconds natively, while the emitted literals replay in
milliseconds; the default portfolio does not absorb that cost automatically.
The local elaborator heartbeat allowance supports this deliberately expensive
invocation; it does not increase factor attempts or per-curve bounds.

## Reproduction and boundaries

```sh
python3 scripts/bench/primality_ecm_sweep.py \
  --output /tmp/ecm-stage2.json
python3 scripts/bench/primality_ecm_sweep.py --paths-only --curves 64 \
  --output /tmp/ecm-paths.json
lake build HexPrimality.Conformance HexIntFactor.Conformance \
  HexIntFactorFieldConformance hexprimality_bench hexintfactor_bench \
  hexintfactor_field_bench hexprimality_field_probe
.lake/build/bin/hexprimality_field_probe verify-ecm2
.lake/build/bin/hexprimality_bench verify
.lake/build/bin/hexintfactor_bench verify
.lake/build/bin/hexintfactor_field_bench verify
```

The [residual and eight-curve construction record](bench-results/hex-primality-ecm-stage2-issue-10362.json), [initial 64-curve record](bench-results/hex-primality-ecm-prototype-paths-issue-10362.json),
and [production 64-curve construction record](bench-results/hex-primality-ecm-paths-issue-10362.json)
retain every completed call, including failures, complete commands and outputs,
source and executable hashes, CPU placement, host load, and generated proof
sources. The initial sweep driver is preserved at commit `e8d7891c4`; the
later driver adds the `--paths-only` and `--curves` controls without changing
timed operations. The initial record's parent commit predates its uncommitted
prototype; its measured source hashes identify the implementation in that commit.
In that prototype, the complete continuation and provider lived inside the hashed
`bench/HexPrimality/FieldProbe.lean`, before extraction into production modules.
The `commit` fields preserve the original worktree HEADs, including pre-rebase
identifiers; the reachable commits above identify the measured file contents.
`completion`, `driver_source`, and `provenance_annotations` were added after the
runs. The embedded driver text matches the original recorded driver SHA-256;
termination annotations describe the retained outputs and assertion failures.
Measured samples, hashes, and original commit fields have not been rewritten.
The production measurement sources are preserved at `7d1763f16`. Subsequent
provider hardening also caps the core callback when no attempt limit is supplied;
these construction measurements always supply the explicit 1024-attempt limit.

The two prototype runs retain their completed residual and construction samples
and terminate on the P-521 certificate-agreement assertion: doing unnecessary
ECM on its residual changed the certificate and raised its cost. The production
provider returns the core result when its known product already exceeds the
square-root threshold. The final paired run tests that change; it does not
replace either failed record. Initial eight-curve construction samples are one
AB block only and are not presented as a completed paired comparison.

Each run automatically chooses one CPU and pins all measured subprocesses.
Two trial-major blocks alternate adjacent AB/BA arms. No completed observation
is rejected for host activity. Repeated deterministic schedules are timing
replicates, not independent random trials. The two secp256k1 successes repeat
the single successful parameter sigma 67; they are not two distinct curves. The 64-curve path experiment extends
the declared allocation; it is not a discarded/replaced eight-curve run.

Native construction timing excludes parsing, startup, trace I/O, and formatting,
and includes the constructor's final compiled self-check. Successful certificates
have a separate compiled checker measurement. Rendering and literal elaboration
are timed together after imports. Direct kernel measurements expand local proof
constants, drain pending checks, and use a fresh checker, with invalid-equality,
changed-subject, and zero-witness controls. An exhausted search has **no**
rendering or replay sample, rather than a zero-cost proof.

All explicit diagnostic factors are validated for range, divisibility, and exact
reconstruction by the existing Lean probe. They are used only as independent
diagnostic subjects. Neither the provider nor root construction reads that
factorization table. Screening supplies candidates, never proof. Every accepted
certificate recursively certifies its children and passes Hex's unchanged
`checkPrime`; kernel replay uses `prime_of_checkPrimeAt` and `decide +kernel`.

## Deterministic continuation

The production continuation is in `HexIntFactor/EcmStage2.lean`, and the
provider in `HexIntFactor/Construction.lean`. `import all` reuses the exact private Montgomery arithmetic and smooth scalar multiplication
from `HexIntFactor.Ecm`, without adding an upstream dependency. `Ecm.search_spec` proves that every
public search factor is a proper divisor, including on arbitrary inputs. It uses direct GMP-backed `Nat` arithmetic, matching the existing
stage-1 backend for these moduli, all larger than a machine word.

For a curve parameter `sigma`, setup and stage 1 match the current implementation.
Stage 1 success or whole modulus terminates the curve. After gcd one, retain the
curve constants and `Q = [M]P`, where `M` is the product of maximal prime powers
at most `B₁`. Stage 2 consumes that state without repeating stage 1.
Requests beyond `B₁ = 524288` or `B₂ = 4194304` are rejected at the executable
boundary. Empty/reversed intervals do no continuation work. The measured tiers
are `(B₁,B₂) = (4096,65536)` and `(32768,524288)`.

The method is the elementary baby-step/giant-step coordinate collision
continuation; see Bernstein, Birkner, Lange and Peters,
[ECM using Edwards curves, §5](https://eecm.cr.yp.to/eecm-20111008.pdf)
for the general approach. This prototype retains Montgomery projective
coordinates and does not implement polynomial multipoint evaluation.

* Enumerate **every** prime in `(B₁,B₂]` with the proved runtime
  `primesBelow (B₂+1)` enumeration, followed by the strict lower-bound filter.
  It does not depend on the committed small-prime table.
* Set `D = 210`, cache `[j]Q` for `0 ≤ j < D`, and compute `H = [D]Q`.
  Initialize the first giant to `H`. Double once to obtain `2H`, then advance
  by differential addition from the adjacent giants `iH` and `(i-1)H`.
  Empty prime blocks still advance the giant. No inversion is performed.
* For each prime use `i = q / D`, `j = q % D`. For `i > 0`, accumulate
  `t(q) = X(iH) Z(jQ) - X(jQ) Z(iH)` modulo `n`. For `i = 0`, use
  `Z([q]Q)` directly; this also handles the primes dividing 210.
  On a nonsingular curve over a prime factor, equality of these projective
  x-coordinates detects both signs, hence the desired `[iD+j]Q = O` opportunity
  as well as `[iD-j]Q = O`. The latter can add opportunities outside the prime
  interval. The implementation does not claim an exact equivalence to the
  direct `[q]Q` test or guaranteed success on degenerate coordinates.
* Multiply terms modulo `n` and flush every 32 primes, plus the final nonempty
  partial batch. Gcd one continues; a proper gcd returns; gcd `n` scans the
  retained terms in order, skipping both one and `n`, and returns the first
  proper gcd. If no term yields a proper divisor, return `whole` and stop.
  Every factor exit dynamically checks `1 < d < n` and `n % d = 0`.

Standalone residual schedules use consecutive parameters `6,7,...` and run
**all** declared curves, even after a successful split. The construction
provider runs the unchanged p−1/rho portfolio first, retains its result when
already sufficient for the square-root criterion, and otherwise tries parameters
`6..13` or `6..69` on its residual, stopping at the first proper divisor.
Each successful split returns both sides to the core factor search; remaining
composite parts enter the bounded ECM worklist. The same provider is passed to
every recursive certificate call. ECM draws no random words; the p−1/rho
provider preserves its existing `Rand` threading from `Rand.ofSeed n`.
Schedules restart for each residual and callback, so repeated failed subsets
can repeat the same curves; there is no hidden failure cache.

The original 1024 total semantic attempts, depth 32, factor cap 32, subset cap
4096, witness schedule, sieve cap, and rho budgets are retained. Stage 1 charges
one attempt; an executed continuation charges one more. A one-attempt remainder
runs only stage 1. Worklist fuel bounds the number of split-processing entries,
and leftover entries are multiplied back into the unresolved residual. Factor
range/divisibility is rechecked at the provider boundary; the constructor also
checks the factor product and residual before subset enumeration.

## Work allocation and validation

Let `c(0)=0`, `c(k)=13*floor(log₂ k)+7` for `k>0`. One ladder level uses
six reduced multiplications for differential addition and seven for doubling.
The declared stage-1 cost is `8 + Σ c(p^e)`, over maximal prime powers at most
`B₁`. The eight count variable-residue products in setup; small-constant
multiplications, the scalar `sigma²`, additions, remainder-only operations,
index arithmetic, enumeration, and gcds are separate work.

For `L` interval primes, stage 2 additionally declares the baby/step cost
`Σ_{j=0}^{210} c(j)`, `6G+1` for `G>0` giant advances (zero when `G=0`),
and three multiplications per candidate for `q≥210` (two cross products and
one accumulation). Small primes instead cost `c(q)+1`. These are conservative
full-interval budgets; early factor/whole exits can use less. Ordinary stage 2
uses at most `ceil(L/32)+32` gcds, with two additional stage-1/setup gcds.

Each curve enumerates its own stage-1 and stage-2 primes. All 210 baby points
and the step use independent scalar ladders, including residues not coprime to
210. This deliberately simple implementation is what the operation counts and
timings measure; shared prime tables and a reduced baby table are possible
future optimizations, not assumed savings in these results.

Working residues comprise 210 baby points, the step, adjacent giants, scalar
ladder temporaries, a 32-term buffer, and one accumulator: `O(210+32+log B₂)`
residues of modulus size. Enumeration additionally retains `O(B₂)` sieve bits
and `O(π(B₂))` prime indices; it is not constant-memory search. The trace keeps
counters and at most 32 recovery gcds. Arithmetic costs depend on modulus bit
length; this experiment makes no asymptotic timing claim.

| Tier | Stage 1 per curve | Two stages per curve | Shared multiplication allowance | Stage-1 curves | Two-stage curves | Stage-1 unused allowance |
|---|---:|---:|---:|---:|---:|---:|
| 4096 / 65536 | 76964 | 114134 | 1826144 | 23 | 16 | 55972 |
| 32768 / 524288 | 613349 | 765323 | 48980672 | 79 | 64 | 526101 |

Each arm shares the same declared multiplication ceiling; the stage-1 arm
cannot spend its final fragment on a complete additional curve. This is not
an equal wallclock or equal-gcd allocation, and early exits do not release
additional curve slots. Construction comparisons instead hold the semantic
attempt cap fixed and expose the additional elapsed cost of ECM explicitly.

`verify-ecm2` checks stage-1 agreement with production over six moduli, nine
parameters and five small bounds, plus the shipped bound and cap rejection;
empty intervals; stage-2 success; whole and
whole-batch recovery (including a whole leaf before a proper leaf); prime
endpoints across multiple giant blocks; exact candidate and batch counts;
giant coordinates against fresh direct scalar ladders; 31/32/33 and 63/64/65
candidate batch boundaries; and provider attempt limits and exact factor/residual
reconstruction, including zero. The fixed success cases are
`1022117 = 1009*1013`, sigma 6, bounds 16/1024 (recovery returns 1013), and
`1000036000099 = 1000003*1000033`, sigma 6, bounds 64/8192 (returns 1000033
after 608 candidates and 21 giant advances). These are executed in the existing
single CI job. They test untrusted search; no elliptic-curve success
or completeness theorem is claimed.

Pollard p−1 stage 2 was unavailable in the ECM measurement checkout.
Its independent draft implementation is compared separately below at a pinned
revision of [PR #10364](https://github.com/kim-em/hex-dev/pull/10364); it does not
supply any factor or certificate to the ECM runs.

## Residual results

Counts include **both** deterministic timing replicates. No residual trial
returned `whole`; every non-success below returned `noFactor`. The elapsed
columns are sums of native stage-1 plus stage-2 times over all calls in that
cell, including successful early exits; they exclude subprocess startup.

| Bounds | Residual | Stage-1 success / failure | Two-stage success / failure | Stage-1 total (s) | Two-stage total (s) |
|---|---|---:|---:|---:|---:|
| 4096 / 65536 | secp256k1 recursive | 0 / 46 | 0 / 32 | 1.43 | 1.35 |
| 4096 / 65536 | P-384 root | 4 / 42 | 8 / 24 | 1.53 | 1.55 |
| 4096 / 65536 | P-384 recursive | 0 / 46 | 0 / 32 | 1.52 | 1.76 |
| 4096 / 65536 | Curve448 root | 0 / 46 | 0 / 32 | 1.44 | 1.56 |
| 32768 / 524288 | secp256k1 recursive | 0 / 158 | 2 / 126 | 34.5 | 37.7 |
| 32768 / 524288 | P-384 root | 26 / 132 | 56 / 72 | 31.1 | 36.0 |
| 32768 / 524288 | P-384 recursive | 2 / 156 | 4 / 124 | 37.8 | 46.3 |
| 32768 / 524288 | Curve448 root | 2 / 156 | 4 / 124 | 33.1 | 46.8 |

Thus stage 2 adds successful curves at a comparable declared multiplication
allocation, including the secp256k1 split absent from the stage-1 arm. It does
not uniformly reduce elapsed time. The two-stage sigma range is a subset of
the stage-1 range, and continues the identical stage-1 operation after gcd one;
the arms are nested deterministic schedules, not independent samples. The larger stage-1 schedule also finds
useful P-384 and Curve448 factors; this evidence does not establish that stage 2
is necessary for every target. Nor do repeated fixed curves estimate a general
success probability. The eight-curve construction profile exhausts on all three
open targets (528, 682 and 83 attempts respectively); 64 curves are materially
different coverage, not merely a relaxed top-level attempt limit.

## Complete certificate paths

The baseline traces reproduce the previous first unresolved obligations and
attempt counts: secp256k1 needs the predecessor of its 237-bit child and stops
at 272 attempts; P-384 stops at the root residual in 14; Curve448 has only the
107-bit known product and stops in 67. P-521 still completes in 170.
These are factoring obstructions, not failed literal rendering or replay.

**secp256k1.** The root needs no new split: its 237-bit probable-prime cofactor
is already a candidate. Sigma 67 at 32768/524288 splits that child's residual,
returning `132896956044521568488119` (77 bits) after stage-1 gcd one.
The provider validates both sides and returns the 128-bit complementary
candidate `255515944373312847190720520512484175977` too. Subset selection chooses
the **128-bit** child alone for the 237-bit square-root certificate. Its own
certificate uses the table primes `2,4423,41201,96557` in a cube-root node.
It does not need to factor its predecessor completely. The full root succeeds
in 145 attempts, of which 138 are charged by the one recursive factor callback.
Both the 77-bit and 128-bit diagnostic subjects independently construct in five
attempts; the large unused predecessor factors from the old diagnosis are not
recursive proof obligations of the selected certificates.

**P-384.** Sigma 6 splits the root residual during stage 1, returning
`807145746439` and exposing the 334-bit cofactor. Its predecessor requires
further work: sigma 62 finds the 69-bit factor `529709925838459440593` in stage 2;
on the remaining composite, sigma 64 finds `1357291859799823621` (61 bits) in
stage 1. The 334-bit certificate selects the **61-bit** child plus
`2^4,8389,38557,312289`. The latter children certify from cheap factors, and the
61-bit child's cube-root certificate needs only `2²,67,6317`.
The root selects the 334-bit child, completes in 290 attempts, and passes the
checker. The 69-bit and 134-bit factors are discovered but not required by this
chosen certificate. All three diagnostic subjects independently construct
(3, 8 and 21 attempts respectively).

**Curve448.** Sigma 28 finds the 78-bit factor
`167773885276849215533569` in stage 2. Continued bounded factoring also discovers
the 115-bit candidate through the core portfolio and the 71-bit factor at
sigma 57 in stage 1. The chosen cube-root certificate needs only the **78-bit**
child together with `2,18287,1466449,2916841,6700417`; it does not need both the
71-bit and 78-bit factors used by the earlier supplied fixture. The 78-bit
child uses `2^9,7²,2531`, bypassing its large unused predecessor factor.
The provider consumes 231 attempts; recursive certification and witnesses
bring the complete root to 259. The four diagnostic factors independently
construct in 11, 11, 10 and 23 attempts.

All eleven independent diagnostic child calls succeed: the secp256k1 237-bit
child (144 attempts), P-384 334-bit child (274), and the nine smaller factors
listed above. Their traces and compiled checks are retained separately from
root construction. Only the selected subtrees of the root certificates are
claimed as the supported end-to-end kernel proofs.

**P-521.** The core factor product already meets the square-root criterion,
so the explicit provider returns it before ECM. Both final arms emit the same
certificate, with 170 attempts. The initial prototype's unnecessary continuation
used 233 attempts and changed the certificate; both stopped prototype records
retain that failed regression assertion and its completed samples.

## Construction, rendering and replay cost

These are the two retained samples per arm from the final shared-host run.
A dash denotes no certificate. Native checking is a separate compiled replay,
in addition to the self-check already included in construction.

| Target / arm | Native construction (s) | Attempts | Compiled checker (ms) | Render/elaboration (ms) | Direct kernel replay (ms) |
|---|---|---:|---|---|---|
| secp256k1 / baseline | 14.26, 13.00 | 272, exhausted | — | — | — |
| secp256k1 / ECM | 18.78, 18.07 | 145 | 0.464, 0.460 | 4.10, 3.68 | 4.35, 4.49 |
| P-384 / baseline | 0.958, 0.946 | 14, exhausted | — | — | — |
| P-384 / ECM | 39.01, 37.50 | 290 | 1.30, 1.30 | 10.43, 5.23 | 10.42, 8.99 |
| Curve448 / baseline | 1.469, 1.467 | 67, exhausted | — | — | — |
| Curve448 / ECM | 24.79, 24.30 | 259 | 2.50, 2.44 | 31.74, 6.98 | 14.63, 13.73 |
| P-521 / baseline | 1.788, 1.667 | 170 | 18.09, 13.89 | 15.23, 18.47 | 55.20, 77.27 |
| P-521 / ECM | 1.628, 1.659 | 170 | 13.73, 13.80 | 15.53, 24.90 | 59.48, 97.48 |

The final record has sixteen construction calls (three baseline failures per
block, all ten other calls successful), ten rendering/replay samples, eight
root traces, eleven child traces, four diagnostic factor validations, and one
continuation verification. The paired observation of the unchanged P-521
certificate illustrates the shared-host variation; no P-521 speedup is claimed.

`HexIntFactor.FieldConstruction` pins the three complete `Try this:` messages.
`HexIntFactor.FieldReplay` imports only the checker and proves each target
with ordinary `decide +kernel`. Three fixed native checker registrations in
`HexIntFactor.FieldBench` run in the ordinary smoke gate. The separate manual
`hexintfactor_field_bench` target adds three fixed native construction attempt
hashes. P-521 retains its existing fixed registrations. The benchmark runner's
120-second construction caps apply to measurement, not `verify`; full searches
are therefore excluded from the routine benchmark smoke gate.

The full tactic-output module took approximately 218–243 seconds in local
builds. These unpaired build observations include interpreted search and are
operational context, separate from the paired literal render/elaboration and
kernel measurements above. CI builds `HexIntFactorFieldConformance` when the
library filter includes HexIntFactor (or all libraries); ordinary checker
replay remains in unfiltered conformance. This retains the exact emitted-output
guards without charging unrelated PRs for all three full searches.

This evidence supports a bounded explicit route with direct `Nat` arithmetic;
it does not justify replacing the default portfolio or raising other budgets.
A future automatic policy would need broader positive and negative corpus cost
evidence and could investigate stopping factoring once a sufficient subset can
be certified. ECPP is not required to support these three targets: current
Pocklington and cube-root certificates suffice. Any future ECPP work should have
a separate certificate/checker design issue, motivated by a corpus that remains
inaccessible to the existing criteria, rather than by these now-constructed
examples alone.

## Independent Pollard p−1 comparison

The draft implementation in PR #10364, commit
`af894cbb8fa86164ad8da113d9b26c5bc8bff76d`, is tested in a separate checkout.
The [complete record](bench-results/hex-primality-pminus-fields-issue-10362.json)
contains 96 residual calls and 16 full construction calls, with two adjacent
AB/BA blocks on one automatically selected CPU. Every completed call is retained.
The record embeds the measurement probe and driver; all other Lean sources are
identified by the pinned commit. Reproduce with a disposable checkout:

```sh
git fetch origin refs/pull/10364/head
git worktree add --detach /tmp/hex-pminus-fields af894cbb8fa86164ad8da113d9b26c5bc8bff76d
python3 scripts/bench/primality_pminus_fields.py \
  --checkout /tmp/hex-pminus-fields \
  --output /tmp/pminus-fields.json
```

For each residual, test bases 2 and 3 at bounds 64/4096, 32768/524288,
and the contract caps 524288/4194304, twice. The stage-1 arm passes equal
bounds to the same counted search; the other arm permits continuation from
its saved residue. Proper divisors are independently checked for range and
exact divisibility. Event summaries retain candidate, multiplication, giant,
and gcd counts; the per-batch list is omitted from this supplemental record.
The comparison holds stage-1 work fixed and measures the added continuation;
it is not an equal-work ECM-versus-p−1 comparison.

Each count below is **proper factor / no factor / whole modulus**, over four
calls per arm. Times sum native search time including failures and early exits.

| Bounds | Residual | Stage-1 outcomes | Two-stage outcomes | Stage-1 total (s) | Two-stage total (s) |
|---|---|---|---|---:|---:|
| 64/4096 | secp256k1 | 0 / 4 / 0 | 0 / 4 / 0 | 0.0002 | 0.0032 |
| 64/4096 | P-384 | 0 / 4 / 0 | 0 / 4 / 0 | 0.0003 | 0.0034 |
| 64/4096 | P-384-child | 0 / 4 / 0 | 0 / 4 / 0 | 0.0003 | 0.0038 |
| 64/4096 | Curve448 | 2 / 2 / 0 | 2 / 2 / 0 | 0.0003 | 0.0022 |
| 32768/524288 | secp256k1 | 0 / 4 / 0 | 0 / 4 / 0 | 0.0715 | 0.5568 |
| 32768/524288 | P-384 | 0 / 4 / 0 | 0 / 4 / 0 | 0.1003 | 0.6325 |
| 32768/524288 | P-384-child | 0 / 4 / 0 | 0 / 4 / 0 | 0.0688 | 0.5491 |
| 32768/524288 | Curve448 | 0 / 2 / 2 | 0 / 2 / 2 | 0.0445 | 0.3036 |
| 524288/4194304 | secp256k1 | 0 / 4 / 0 | 0 / 4 / 0 | 1.1442 | 12.5207 |
| 524288/4194304 | P-384 | 0 / 4 / 0 | 0 / 4 / 0 | 1.2567 | 13.3692 |
| 524288/4194304 | P-384-child | 0 / 4 / 0 | 0 / 4 / 0 | 1.2333 | 14.1268 |
| 524288/4194304 | Curve448 | 0 / 2 / 2 | 0 / 2 / 2 | 0.7020 | 5.9613 |

Across all 48 calls per arm, both have two proper-factor results, 42 misses,
and four whole-modulus results. The two successes repeat the same Curve448
base-2 **stage-1** split at bound 64, returning
`6277101733925179126845168871845691884353629438715740815361`.
Continuation adds no successful residual split in this schedule. This does
not rule out other bases or larger allocations, and a split alone does not
establish a sufficient recursively certified subset.

Full construction toggles only the draft's `pMinusOneStage2` budget switch,
retaining the existing 1024-attempt cap and all other construction settings.
These calls exercise its production allocation, separately from the cap-sized
residual diagnostics above.

| Target | Disabled attempts / result | Enabled attempts / result | Disabled native seconds | Enabled native seconds |
|---|---|---|---|---|
| secp256k1 | 272 / exhausted | 368 / exhausted | 13.623, 11.223 | 17.373, 12.006 |
| P-384 | 14 / exhausted | 20 / exhausted | 1.299, 0.819 | 1.207, 0.826 |
| Curve448 | 67 / exhausted | 70 / exhausted | 1.828, 1.249 | 1.675, 1.044 |
| P-521 | 170 / ok | 155 / ok | 2.128, 1.393 | 1.282, 0.852 |

All twelve calls for the three open targets exhaust; all four P-521 calls
succeed and pass the compiled checker. P-521 emits the same certificate with
either switch setting. These supplemental calls do not repeat rendering or
kernel timings of that unchanged literal. Thus this independent implementation
does not replace the explicit ECM route for the three open targets under its
tested policy. No unverified result from it enters an ECM certificate.
