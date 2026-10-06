# Mixed ECPP evidence for checked integer factorizations

The optional `HexIntFactor.Mixed` extension separates arithmetic proposals from
prime certification. Two frozen complete products contain native ECPP-certified
512-bit bases after the recorded legacy completion profile exhausts. A third
proposal preserves its certified small factor and an unresolved residual after
both completion routes exhaust. No new factor-discovery algorithm or external
certificate producer is involved.

## Subjects, allocations and schedule

[acceptance-v1.json](acceptance-v1.json) fixes subjects, supplied small-prime
certificates, seeds, expected outcomes and allocations before implementation
measurements. The large bases are ordinary holdout entries 0, 3 and 1 from the
existing independently generated [native 512-bit corpus](../../ecpp/native512/corpus-v1.json).
The chosen seeds are respectively 0, 0 and 1; they are recorded explicitly.
Subject bit lengths are 514, 513 and 513. Arithmetic proposals are supplied,
so their validation and certificate completion do not include discovery.

The mixed profile allocates at most 128 legacy attempts per base and 128 total
attempts in this experiment, using the existing importer profile at 512 base
bits and its registered ECM retry. Exhaustion can occur before every attempt
is consumed; the recorded failures use 26, 20 and 26 attempts. Native ECPP
reserves at most two full `public512Budget` calls, without refunding failures;
each proposal here needs one call. Seeds use an independent `ecppSeed + callIndex`
stream. Full-construction comparisons use the larger pre-existing construction
profile and are reported separately.

Admission independently bounds the whole subject at 4096 bits and bases and
certificate numerals at 512 bits. Supported structural ceilings are 64 entries,
exponent 4096, 4096 legacy constructor/list nodes and depth 64, 20 elliptic rows,
32 total certificate constructors including the base wrapper and legacy
terminal constructors, and 1024 inverses per row. Native completion supports
only explicit public 256- and 512-bit policies. The 256-bit public policy adds
depth 21, rows 20, nodes 32 and output backtracking to the existing default
work profile; the existing Native 256-bit API retains its policy. The 512-bit
work counters and terminal/order packages are the existing public policy.
Total ECPP work is bounded by the reserved call count times that selected finite
policy, including failed calls and retries. Legacy and native random states,
counters and unsuccessful outcomes remain in the importer result.

Expanded input and reified syntax has a 1048576-node limit. Export caps UTF-8
source at 2097152 bytes, charging fragments before joining them and rejecting
oversized output before kernel replay. Reification uses a fresh 20000000-heartbeat
allocation and recursion depth 65536. Synchronous kernel checking uses the same
ceiling but also counts allocations from earlier command work, including
proposal elaboration and production. Supported settings may tighten the
structural and export ceilings. Kernel validation is synchronous, receives the
cancellation token and uses a temporary declaration environment which is
discarded. No bit limit guarantees production or replay success.

[component-comparison-v1.json](component-comparison-v1.json) retains both
trial-major adjacent construction/ECPP arms, alternating their order with case
and trial. Every legacy outcome exhausts, both selected complete bases succeed
natively, and the third base exhausts at the portfolio allocation. Duplicate
expanded certificate text is represented by hashes; the accepted data itself
is frozen publicly below. [preliminary-v1.json](preliminary-v1.json) retains the
completed preliminary functional sample, which was not pinned and is not used
as a timing comparison.

[completion-v1.json](completion-v1.json) and
[completion-v2.json](completion-v2.json) retain every completed mixed sample
with the earlier unrestricted debugging kernel checker.
[completion-v3.json](completion-v3.json) measures the synchronous kernel checker
under the supported heartbeat/recursion limits, the clamped ECPP call count and
reuse of partial acceptance for complete results.
[completion-v4.json](completion-v4.json) measures incremental source-byte
charging before kernel replay. Subjects, allocations and output data are
unchanged. Each schedule has two trial-major runs. One CPU is automatically leased without checking for
an idle core, and host/load context is retained. Component arms are adjacent
and alternate order. Absolute times describe this shared host.

## Capability and measured boundaries

The table shows both final scheduled samples in milliseconds. The final column
includes reification, auditing, fresh kernel validation and source formatting;
compiled acceptance is measured separately.

| Case | Outcome | Legacy ms | ECPP ms | Compiled acceptance ms | Reification/kernel/source ms | Source bytes |
|---|---|---:|---:|---:|---:|---:|
| A | complete | 213.87 / 213.81 | 1557.67 / 1537.91 | 29.31 / 27.96 | 6311.79 / 6228.42 | 1052709 |
| B | complete | 205.92 / 201.68 | 1673.18 / 1648.93 | 29.62 / 30.49 | 6216.39 / 6586.79 | 1122771 |
| partial | checked partial | 203.00 / 204.59 | 66.43 / 66.84 | 0.03 / 0.04 | 0.80 / 0.84 | 935 |

Proposal validation is 0.058–0.063 ms. End-to-end mixed preparation is retained
separately from those isolated component measurements. Output constructors are
identical across all completed trials and all implementation schedules.
Case A has 20 elliptic rows, 10 terminal constructors and 31 total constructors;
B has 19 rows, 8 terminal constructors and 28 total constructors. Their
transcripts fit the new actual replay allocations; this was measured rather
than inferred from native production success.

The accepted complete and partial data is public and exposed in
[CaseA](../../../HexIntFactor/Mixed/Frozen/CaseA.lean),
[CaseB](../../../HexIntFactor/Mixed/Frozen/CaseB.lean) and
[Partial](../../../HexIntFactor/Mixed/Frozen/Partial.lean). These ordinary modules
import only `HexIntFactor.Mixed.Replay`, with subject-indexed kernel acceptance.
[Fresh ordinary replay](fresh-replay-v1.json) retains two serial trial-major
builds per output, with GP and generation unavailable. Complete fresh builds
take 12.87–13.37 seconds including Lake startup, parsing and kernel checking;
partial builds take 1.29 seconds. The generated text is unchanged by the final
structural/audit checks. Those measured endpoints now extend existing CI targets.

## Mathematical and independent checks

Core arithmetic, ordering and product reconstruction are unconditional.
Core primality, support and multiplicity results explicitly require ECPP checker
soundness. `HexIntFactorMathlib.Mixed` discharges that obligation using
`Hex.ECPP.natPrime_of_checkAt` and existing legacy soundness, and proves exact
Mathlib factorization correspondence. The partial equation adds the residual's
factorization; listed exponents need not be exact if the residual overlaps them.
The small fixture `578 = 2 * 17 * 17` exercises that overlap explicitly.

[Independent checks](independent-v1.json) verify the actual frozen product and
positive distinct ascending factors, all accepted prime bases and terminal
subjects with PARI `isprime`, and every inverse transcript/curve/scalar operation
with Python exact arithmetic and PARI elliptic multiplication. Both complete
chains contain genuine recursive elliptic steps. The exhausted residual has
no certificate or primality claim in the checked result.

`scripts/ci/check_intfactor_pari.py` pins the exact complete/partial `Try this:`
text, compiles it verbatim in fresh ordinary modules, checks exported public data
and changed-subject rejection, refuses overwriting an existing destination,
checks editor gating and syntax exhaustion, and exercises the real small PARI
route with native ECPP explicitly selected. The existing CI step also re-admits
both large ECPP outputs through the supplied-proposal batch command.
`Mixed.ExportTests`, built by `HexIntFactorTests`, separately pins Meta and
kernel heartbeat rejection, kernel recursion rejection, compiled-check bypass
rejection and exact source byte rejection before replay. All 425 existing
and mixed arithmetic fixtures pass the independent factorization oracle. Legacy fixture output is
preserved as an exact prefix.

The build-checked manual, computational and companion libraries, test targets,
and the large companion proof client build with `lake build`. Headline complete
and partial correspondence proofs audit to `propext`, `Classical.choice` and
`Quot.sound`; kernel acceptance has no added axioms. No unfinished proofs or
`native_decide` are used. Fresh prospective split checks verify computational
replay and batch admission with no Mathlib directory, and a separate companion
client with the intended Mathlib/AINTLIB proof closure. Their results are in
[split-v1.json](split-v1.json), [split-v2.json](split-v2.json) and
[split-v3.json](split-v3.json). The last two build all three large frozen
modules as well as batch admission and
correspondence clients.

Legacy embeddings preserve their checkers. Checked reverse conversion rejects
ECPP entries and replays legacy acceptance. Legacy divisor, arithmetic-function,
order and square-decomposition APIs still require legacy data or an explicit
consumer extension. Ordinary native dispatch and legacy suggestion behavior
remain covered. Publication is separate and remains behind manual review.
