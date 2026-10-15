# Sturm comparison cap adaptation

Question: can the complete frozen native comparison finish with a larger
operational per-call timeout, preserving its inputs, balanced schedule and
pinned regression rule? The original run stopped when both arms hit 120 seconds
at the largest `runRationalHigh` parameter. Its consumed reservation and every
completed output remain retained. This is an unresolved Phase-6 comparison,
not a new complexity claim or another unchanged attempt.

## Collector contract

`scripts/bench/sturm_regression.py --cap-from ORIGINAL` accepts one adaptation
only when the bound decision includes `cap_protocol`. The collector checks:

- The original host and exact persistent reservation path are retained; a copied
  journal in another state directory cannot authorize adaptation. The journal
  binds the exact retained `context.json`, which must describe a failed, reserved comparison with measurements, no integrity
  failure, no prior adaptation and no inconclusive rerun.
- Both original arms were killed at their per-call cap at the same parameters
  in the same family. Other errors, truncation, interruption, regression and
  inconclusive results do not authorize adaptation.
- The original source-manifest files and guard-build provenance are reused
  unchanged. The native binary pair, guard and complete recorded producer,
  registration and dependency inputs agree. A separate tooling commit may
  descend from the original candidate only through the collector, its test and
  non-Lean files under this report directory. Its actual head is bound separately
  by `tooling_root_head`; it is never substituted for the producer build head.
- The new decision binds the original context and failed export hashes. Export
  subjects, statuses and parameters must agree with the reserved failure.
  Completed rungs have non-null result hashes that match across the source arms.
  Timeouts use whole seconds up to one day, fitting both the runner's numeric
  export precision and UInt32 millisecond deadline, exceed both failed limits and cannot lower any frozen registration or
  runner-default timeout.
- The selected names equal the entire original list, in order. No family or
  parameter is dropped. Both arms receive the same override in every block,
  and every parent export must confirm that it used the bound timeout.

The adaptation uses one additional persistent reservation for the exact native
binary pair and guard. Its filename does not depend on the timeout, question,
collector hash or output directory. Changing these cannot reserve another
adaptation. The original reservation is never overwritten. Any failure or
interruption after reservation consumes the adaptation. Input validation,
correctness verification or CPU-lease failures before reservation do not consume
an attempt. Only a completed inconclusive adaptation
can use the existing single unchanged `--rerun-of` allowance, with identical
bindings and decision bytes. The unchanged-rerun reservation is also stored
persistently beside the original journal; deleting its output-directory receipt
cannot unlock another rerun. Passing or regressing captures cannot retry.

Preflight validates the same bindings and native correctness controls without
leasing a CPU, reserving an attempt or collecting measurements. A real capture
still uses the existing CPU lease and records shared-host activity without
sample rejection or a quiet-core condition. Linux `MemTotal` and `MemAvailable`
are recorded before and after commands as context only; unavailable memory
metadata does not reject or postpone a run. Interrupted or failed parent commands
have their process group killed so workers do not continue outside the collector.

## Proposed complete campaign

Use a uniform 3,600-second per-call safety timeout for every one of the 58
families listed in `capture/context.json.gz`. This increases the explicit
timing-registration limits in the frozen `Bench.lean` (120, 600 and 1,800 seconds)
and `Frontend.lean` (600 seconds), also covering configuration inheritance and
the pinned LeanBench default of one second.
The proposal covers the unattempted reduced/replay high-bit families and
prepared-query families as well as `runRationalHigh`. It does not resume after
the failed rung: all original families and parameters run from block zero in
four trial-major adjacent AB/BA blocks.

The longer timeout is an operational limit, not a performance threshold or an
estimate that the workloads will finish. Inner targets, warmup, signal-floor
policy, parameter schedules, native hash checks and the pinned 10-percent
median comparison remain unchanged. No theorem/tactic timing is added. The fixed
correctness controls retain their own settings; their 30-second registration
value is not a timing-family limit.

Memory is a material uncertainty. The largest completed baseline rung at 524,288
retained a peak RSS of 12,793,428 KiB. If the observed quadratic storage growth
continues, doubling the parameter would require roughly four times that memory,
about 49 GiB; this is an extrapolation, not a completed measurement. Replay and
other unattempted families can have different peaks. The proposed decision accepts
an allocation error or out-of-memory kill after reservation as a consumed failure,
without another adaptation or unchanged retry. A longer timeout does not make a
workload fit memory, and memory availability is not an admission threshold.

Before reserving a campaign:

1. Review the collector change and the concrete decision. Preserve the original
   failure, source manifests, binaries and guard. Keep the original state path.
2. Create a clean tooling checkout rooted at the original candidate commit
   `8e5b3e40a69117c84bb6f0c19aaad93a26049ab8`; current main cannot serve as
   that checkout because its recorded Lean inputs have changed. Copy the reviewed
   collector, its test and this report directory, without changing any Lean or
   dependency input. Commit and push that side commit under an existing audit
   reference so it remains resolvable. Bind its actual head as `tooling_root_head`
   in the new decision, alongside the new collector/helper hashes. Keep the
   original source manifests byte-for-byte and the original `guard_build`, whose
   `source_head` remains `8e5b3e40a69117c84bb6f0c19aaad93a26049ab8`.
   Reuse the exact original native binaries and guard; no build is relabeled.
3. Copy the complete `cap_protocol` object from
   [cap-proposal.json](cap-proposal.json) into the normal, fully bound decision.
   It records the actual 58 family names, original context hash and both failed
   export hashes. This object is a proposed timeout policy, not a source/build
   attestation or complete experiment decision. A read-only check against the
   original host-local journal and exports verifies its eligibility without
   modifying the reservation or collecting samples.

4. Run the usual fully bound collector invocation with both
   `--cap-from ORIGINAL --preflight`. Inspect its source/guard checks and exact
   full selection. Only then collect with the same arguments and without
   `--preflight`. The revision receives its own output directory; original
   records remain read-only.

After collection, retain every output and finding. A completed guard pass still
requires reconciliation of the candidate computation with the polished current
library, alongside final proof/API/manual acceptance. This protocol and its
synthetic tests supply no computational performance pass or phase promotion.

If the host-local capture directory is cleaned, restore the archived
`capture/*.gz` contents at the exact recorded path
`/home/kim/.codex/tasks/hex-10575/sturm-regression-acceptance/capture`, including
`context.json`, `decision.json`, the source manifests and raw outputs. Keep the
original persistent host-state directory and all reservation markers intact.
Restoring capture data does not create a new allowance, and copying an archived
journal to another state directory is refused.
