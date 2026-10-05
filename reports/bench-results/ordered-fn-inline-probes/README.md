# Coefficient-scan inlining probes

Question: can compiler annotations remove the indirect coefficient-scan work in
the profiled height and successive-infinitesimal sign paths? The mathematical
bodies, public hypotheses, benchmark workloads and Lean toolchain are unchanged.
The two source variants are retained by `audit/issue-10575-orderedfn-inline-probes`:

- `91799d72602b33e4e8e27244512ad48dbfd37526` annotates `lowestIndex`,
  `lowestCoeff` and `sign`.
- `c7abff79dccf64ea4e14c13b0423cb607f7369d2` annotates only `lowestIndex`
  and `lowestCoeff`.

Build each variant with
`lake build HexOrderedFn HexOrderedFnMathlib.Infinitesimal hexorderedfn_bench`.
Both targeted builds completed 3233 jobs, including the companion infinitesimal
proofs. The native executable hashes are in each `decision.json`; binaries remain
local. The unmodified same-toolchain reference is the reproducible executable
`6479b2306cb778b7f34ec681020322212607e518577ecae9912f06e0a1ab0fed`
documented in [the API report](../../hex-ordered-fn-api.md). Its 215-job
rebuild used `lake build HexOrderedFn hexorderedfn_bench`, without the companion
target. The variants' parent is `7d59cacdc887a0e770f556bb7ef55a5da1c478db`.
The reference's `205cd87` adds reports to the earlier `d07b004`; the subsequent
main changes add tower/sign integration outside this benchmark's import closure.
All 65 local files in that closure, the Lean toolchain and dependency lock agree
between `205cd87` and `7d59cac`. The Lake-file differences add unrelated tower
module/executable registrations. Rebuilding the unmodified parent also
reproduces the reference executable byte for byte; [source-check.json](source-check.json)
records the closure, exact command, binary hash and both build summaries. The source tag above points to `c7abff` and
retains its ancestor `91799d`, so both variants remain fetchable.

The full-sign variant generates expanded caller bodies and specialized array
loops. The scan-only variant keeps the height caller as a 365-byte wrapper while
retaining specialized loops. These observations justified measuring an actual
source change; generated code alone did not predict improvement.

Each completed capture contains three trial-major adjacent AB/BA pairs at each
of the three named parameters. The CPU lease, host context, exact commands,
raw stdout/stderr and observation rows are retained. Observation `env.git_commit`
identifies the invocation checkout, including in reference arms; it is not the
source commit of the frozen reference binary. Canonical executable hashes are in
`probe-context.json` under `binaries`. The predeclared decision
requires both scan cases to improve by more than the existing 10% default before
expanding to a full comparison. Approximation remains a separately unresolved
path. This attribution probe cannot establish Phase-6 acceptance.

| Variant | Height @2048 | Third level @1024 | Approximation @12288 | Expand comparison |
| --- | ---: | ---: | ---: | --- |
| Full sign | +37.85% | +387.64% | −0.07% | No |
| Scan only | +40.96% | +380.94% | −0.51% | No |

Run `python3 reports/bench-results/ordered-fn-inline-probes/analyze.py` to
validate raw observations, pair hashes and the retained analyses without new
measurements. Changes compare each arm's median of three native per-call observations. Both
completed captures have 18 successful arms and matching hashes in all nine pairs.
Height and third-level signs both hash to `0x2`; this verifies that small returned
sign, rather than broad semantic equivalence of arbitrary inputs.
The cause of the scan slowdown remains undiagnosed; this result does not
rule out other implementations or compiler annotations. Neither variant is suitable to ship. The two decisions and all negative results
remain preserved; no further unchanged capture is justified.

`failed-capture` preserves the first collection, including its nine successful
reference arms and nine failed candidate invocations. Copying the executable
without its executable mode caused permission errors. `full-sign` is the single
permitted unchanged rerun, with the file mode corrected and identical binary
bytes. The failed invocations do not count as timing observations. Raw scripts and
metadata preserve their original absolute host paths and compact wording;
`orderedfn-inline-investigation` in those paths refers to `failed-capture` here,
and canonical hashes should be read from the structured `binaries` fields.
The raw description "based on d07b00469d" is incorrect: the actual variant
parent is `7d59cac`, as established above.

The annotation changes are absent from the integrated library. The retained
historical-baseline comparison and its unresolved findings remain in force.
