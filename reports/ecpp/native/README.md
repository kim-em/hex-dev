# Bounded native ECPP production

The class number one portfolio demonstrates a capability gain at 256 bits.
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

Native success rates are 100% at 128 bits and 50% at 256 bits over the entire
corpus. Native and full construction each solve subjects the other exhausts
on: their union solves seven of eight 256-bit subjects. The holdout rate is
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

## Arithmetic, replay and dependency evidence

`oracle.json` records independent Python inverse/scalar replay and PARI
elliptic-curve multiplication for all 35 ECPP steps from all 12 successful
native outputs. PARI independently confirms primality of all 47 distinct
subjects, including recursive children and terminal subjects. Oracle code
never participates in Lean proof production.

The existing ECPP fixture emitter and oracle now cover 6443 cases, including
composite/nonsquarefree modular root proposals, Jacobi symbols, checked norm
equations, every sextic/quartic twist family and complete native chains.
Core conformance covers all shared allocations, local retry exhaustion,
nonunits, subject mismatch, deterministic replay and a successful search
that backtracks 13 times at depth three. Zero, one and composite inputs have
only an exhaustion result; the producer exposes no compositeness verdict.

`Native128_0`, `Native256_0`, `Native256_1`, `Native256_2` and `NativeHoldout`
are fresh-module kernel proof probes for complete native outputs. Their
axiom audits are guarded and allow only `propext`, `Classical.choice` and
`Quot.sound`. The headline soundness theorem is unchanged. Computational
source and runtime benches remain Mathlib-free; ordinary primality modules
acquire no ECPP imports.

`interface.json` records native generation, exclusive export and verbatim
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

`compiled.json` records five fixed endpoint trials with expected hashes:

| Endpoint phase | Median |
| --- | ---: |
| Native 128-bit search and output self-check | 61.640 ms |
| Native 256-bit search and output self-check | 722.381 ms |
| Compiled checking of the native 256-bit certificate | 4.775 ms |
| Frozen conversion and recheck | 67.134 ms |

These fixed registrations are endpoint observations and hash anchors; they
make no parametric complexity claim. Proof elaboration is measured separately
in fresh modules. The mathematical checker has no search-size policy. The
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

Reproduce the paired corpus with `scripts/bench/ecpp_native_campaign.py`,
independent output checks with `scripts/oracle/ecpp_native.py`, and fresh
phase probes with `scripts/bench/ecpp_native_phases.py`. Use new output paths
when collecting another campaign so existing results are preserved.
