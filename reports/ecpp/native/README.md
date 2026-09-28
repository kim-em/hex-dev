# Bounded native ECPP production

The class number one portfolio demonstrates seven complete native 256-bit
successes where full construction exhausts, across two frozen corpora.
Search takes only a natural subject, seed and finite allocation; it reads no
certificate, trace, factorization, curve or point. Every success is complete
`Cert` data accepted by `checkAt`, and the frozen outputs below produce
unconditional kernel proofs. There is no native 512-bit support claim.

## Corpus and construction comparator

`corpus.json` freezes four tuning and four holdout subjects at each of 128
and 256 bits. It was committed in `edfb294f3` before implementing or tuning
search. SHA256 selects the starting integers; PARI `nextprime` selects the
subjects. This corpus-generation step supplies no search data to the producer.
The producer was committed in `4a02dcfa0` before evaluating the holdout.
These original commit identifiers predate rebasing onto the SQUFOF API
update; the corresponding rebased corpus and producer commits are
`44c7f6406` and `610411aad`.

`campaign.json` retains all 16 paired verdicts, complete successful outputs,
allocations, unresolved subjects, random states and timings. Adjacent arms
alternate native/construction order. The comparator uses the full default
`Construction.runTraced` profile, followed by its registered
`ecmConstructionFactor` retry with the remaining total allocation and random
state. The core allowance is 1024 attempts, 32 levels and 521 bits; its rho
profile has two restarts of at most 32768 steps. Smooth bounds are 64, 512,
4096, 32768, 262144 and 524288, with bases two and three. The ECM retry admits
64 curves per residual, B1=32768 and B2=524288. Stage two is disabled for
p-minus-one by default. This is the current default `primality?` construction
schedule with the applicable HexIntFactor extension, rather than the older
bounded Pocklington policy probe.

| Corpus | Bits | Native success | Native exhaustion | Full construction success | Full construction exhaustion |
| --- | ---: | ---: | ---: | ---: | ---: |
| Tuning | 128 | 4/4 | 0/4 | 4/4 | 0/4 |
| Tuning | 256 | 3/4 | 1/4 | 1/4 | 3/4 |
| Holdout | 128 | 4/4 | 0/4 | 4/4 | 0/4 |
| Holdout | 256 | 1/4 | 3/4 | 2/4 | 2/4 |

`campaign-rebased.json` repeats the complete frozen corpus after adapting to
the upstream SQUFOF policy API. All 16 verdicts, full construction attempt
totals and successful raw certificates are identical. SQUFOF remains off in
the default construction allocation. `elaborator-construction.json` also
confirms all four 256-bit exhaustions by calling the actual `construct`
elaborator with extension discovery and verifying that the ECM provider ran.
The probe disables the elaborator heartbeat ceiling so the finite search
allocation can finish; its initial heartbeat timeout is retained in
`elaborator-construction-initial.json`.

For that producer version, native success rates are 100% at 128 bits
and 50% at 256 bits over the entire corpus. Native and full construction each solve subjects the other exhausts
on: their union solves seven of eight 256-bit subjects. That version's holdout rate is
25% at 256 bits, so the tuning result is not a general success-rate promise.
No exhausted verdict is evidence of compositeness.

All four 256-bit native successes exhaust the full construction route:

| Case | ECPP steps | Full-route attempts | Native search | Full construction | Frozen row bytes | Expanded constructor bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| tuning-256-0 | 6 | 170 | 0.705 s | 13.134 s | 1615 | 131494 |
| tuning-256-1 | 6 | 189 | 0.316 s | 16.914 s | 1721 | 99139 |
| tuning-256-2 | 7 | 201 | 0.536 s | 16.552 s | 1753 | 135585 |
| holdout-256-1 | 1 | 156 | 0.095 s | 13.217 s | 321 | 29612 |

The constructor byte counts include complete raw data and terminal
certificates, formatted by `reprStr`; row bytes exclude terminal data and
module syntax. Explicit native export produces a 2351-byte source module for
`tuning-256-0`, including its checked terminal certificate. The class number
one portfolio suffices for this acceptance campaign; no higher-degree class
polynomial table is needed to establish the demonstrated gain.

## Validation of the current producer

`validation-corpus.json` freezes eight new subjects at each bit size in
`5e2e3be8c`, before implementing the even-coordinate norm path in
`c44995000`. This independent corpus supplies no search data. The producer
uses the same factor packages and allocations; no parameters were tuned
against this corpus. `validation.json` retains every paired verdict and raw
output from this version.

| Corpus | Bits | Native success | Native exhaustion | Full construction success | Full construction exhaustion |
| --- | ---: | ---: | ---: | ---: | ---: |
| Validation | 128 | 7/8 | 1/8 | 8/8 | 0/8 |
| Validation | 256 | 6/8 | 2/8 | 3/8 | 5/8 |

Three new 256-bit native successes exhaust the full construction allocation:

| Case | ECPP steps | Full-route attempts | Native search | Full construction | Frozen row bytes | Expanded constructor bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| validation-256-4 | 6 | 1024 | 0.288 s | 44.657 s | 1875 | 121320 |
| validation-256-5 | 6 | 1024 | 0.398 s | 33.207 s | 1670 | 108351 |
| validation-256-7 | 11 | 1024 | 1.638 s | 42.856 s | 2756 | 235220 |

For these subjects the core consumes the entire shared construction allowance,
so the ECM extension receives no remaining attempts. The actual elaborator
probe in `validation-elaborator.json` confirms the same verdicts, attempt
totals and extension allocations. `NativeValidation` replays all 13 complete
successes in a fresh module importing only the compact interface; guarded
axiom audits allow only the standard axioms. `validation-oracle.json` records
independent replay of 47 steps and primality checks for 60 distinct subjects.

The previous campaigns identify their producer commits explicitly. The leaf
depth refinement in `86b1f9395` cannot affect those default runs: all chains
have at most seven steps, leaving more than the fixed eight leaf levels.
The current producer additionally searches even-coordinate norm solutions;
`campaign-updated.json` repeats the original corpus with this implementation.
The updated original corpus has native success rates 8/8 at 128 bits and
6/8 at 256 bits, including 3/4 on its original 256-bit holdout. Full construction
still succeeds on 8/8 and 3/8 respectively. Four original 256-bit capability
gains remain; the two additional original native successes are also solved by
full construction. Together the original and fresh corpora give seven native
256-bit gains, including four on holdouts.

`NativeUpdated` replays all 14 current original-corpus successes. The two
current corpora therefore supply 27 complete kernel replays and independent
verification of 95 ECPP steps. `public-generation.json` checks every successful
subject through the actual native elaborator generator, with its row-limited
depth allocation, and confirms identical compact data after kernel proof
production. All previous reports remain available with their original source
versions.

## Arithmetic, replay and dependency evidence

`oracle.json` records the earlier independent Python inverse/scalar replay and PARI
elliptic-curve multiplication for all 35 ECPP steps from all 12 successful
native outputs. PARI independently confirms primality of all 47 distinct
subjects, including recursive children and terminal subjects. Oracle code
never participates in Lean proof production.

The existing ECPP fixture emitter and oracle now cover 6457 cases, including
composite/nonsquarefree modular root proposals, Jacobi symbols, checked norm
equations, every sextic/quartic twist family and complete native chains.
Point-count multisets match the six sextic, four quartic and ordinary
quadratic twist orders, with independent PARI j-invariant and cardinality
checks. Both odd and even-coordinate norms have regression cases.
Core conformance covers all shared allocations, local retry exhaustion,
nonunits, subject mismatch, deterministic replay and a successful search
that backtracks at depth three. Zero, one and composite inputs have
only an exhaustion result; the producer exposes no compositeness verdict.

`Native128_0`, `Native256_0`, `Native256_1`, `Native256_2` and `NativeHoldout`
are fresh-module kernel proof probes for complete native outputs. Their
axiom audits are guarded and allow only `propext`, `Classical.choice` and
`Quot.sound`. The headline soundness theorem is unchanged. Computational
source and runtime benches remain Mathlib-free; ordinary primality modules
acquire no ECPP imports.

`interface-updated-128.json` and `interface-updated-256.json` record native generation, exclusive export and verbatim
replay of both Nat.Prime and Hex.Nat.Prime suggestions in fresh modules.
Generation runs with a failing GP stub, and frozen proof modules import only
the compact interface and exported data. No GP invocation occurs and frozen
replay performs no CM search. The PARI interface regression also passes after
sharing its export implementation with native production.

## Measurements and limits

Measurements use Lean 4.34.1 and PARI/GP 2.17.3 on the shared host `chungus2`.
CPU leases select one available logical CPU without an idle-core test. Each
JSON retains the selected CPU, source version, host context and every
completed sample. Host activity never rejects a completed sample. These are
host-specific observations, not CI time limits or complexity claims.

`compiled-updated.json` records five fixed endpoint trials with expected
hashes from the current producer:

| Endpoint phase | Median |
| --- | ---: |
| Native 128-bit search and output self-check | 62.416 ms |
| Native 256-bit search and output self-check | 717.627 ms |
| Compiled checking of the native 256-bit certificate | 4.735 ms |
| Frozen conversion and recheck | 65.939 ms |

These fixed registrations are endpoint observations and hash anchors; they
make no parametric complexity claim. Proof elaboration is measured separately
in fresh modules. `phases-updated.json` retains four serial trial-major samples of each fresh target;
every sample positively confirms that its target rebuilt. The import/numeral
baseline, reification, direct kernel proof and tactic proof medians are
3.258, 3.338, 6.042 and 4.459 seconds. Peak RSS medians are approximately
3.97, 3.98, 4.22 and 4.23 GiB, respectively. Reification is indistinguishable
from module startup at this resolution. These measurements include shared
imports and do not subtract startup to claim an isolated CPU kernel time.

The mathematical checker has no search-size policy. The
public native generator is admitted through 256 bits; supplied-certificate
replay retains its independently established 512-bit policy.

The default shared search limits and fixed factor packages are documented in
the computational SPEC and `SearchBudget`. Factor-work units reserve bounded
attempt packages, including their independently bounded trial division,
subsets and witness work. Unused reservations are charged. Scalar reservations
include proposal generation and compiled checker replay. Memo entry and
per-certificate bit limits bound retained data. Failure reports the unresolved
subject and resource; no allocation or random state is restored by backtracking.

`tuning-initial.json` retains the first raw verdicts and incomplete frozen
encoding. Its clocks bracketed pure expressions that the compiler could move,
so those near-zero values do not measure search. `tuning.json` uses explicit
IO barriers and corrected compact rows; all raw verdicts agree. No completed
run was discarded. `phases-initial.json` retains the initial phase samples;
it lacks positive per-sample rebuild confirmation and overlapped other Lake
builds of the same artifacts, so it does not establish phase latencies.
The final phase protocol checks each target's rebuild explicitly.
`compiled.json`, `phases.json` and `interface.json` retain the earlier
producer observations; their updated counterparts identify the current source.

Reproduce the paired corpus with `scripts/bench/ecpp_native_campaign.py`,
independent output checks with `scripts/oracle/ecpp_native.py`, and fresh
phase probes with `scripts/bench/ecpp_native_phases.py`. Use new output paths
when collecting another campaign so existing results are preserved.
Reproduce public generation with `scripts/bench/ecpp_native_generation.py`;
it invokes native search before comparing the resulting frozen data and
kernel-checks every proof. `public-generation-initial.json` retains a harness
elaboration failure before generation caused by a missing namespace opening.
