# Nested clean/eager comparison protocol

## Workload and measured region

Use the actual validated positive roots of `(2X² - alpha)(X - 3)` in
`(0,1)`, starting with rational `alpha = 1`. Compare depths one and two,
each with 2, 4, 8 and 16 products of `(1 + alpha)`, followed by division
by `(alpha - 3)`. The selected root is never 3; the inverse exercises
the local gcd split. Both arms retain the original nonmonic descriptor.
Production clean packing keeps the unreduced polynomial, apart from canonical
zero: each head is nonmonic, so production `canReduce` is false. The bench-local
eager arm takes the remainder modulo the monic cubic defining head at every
algebraic level. That cubic retains the extraneous root 3; it is not the
minimal quadratic or a canonical field representation. Both arms use ordinary
coefficient kernels and change packing at every level. Their validated
descriptor evidence can differ even though the defining heads, root intervals
and selected roots agree. Lower-level representation and evidence affect
packing's selected-root queries inside the measured workload.

The timed IO action reads its prepared input, computes the complete product
and division, including packing's internal selected-root zero/sign queries,
encodes the resulting raw coefficients and hashes the encoding. Those queries
perform pseudo-division, prepared Sturm queries and recursive lower-level
coefficient arithmetic/signs. These costs are included in the observations.
It executes the action on every invocation. Preparation of all four contexts
and all sixteen input closures occurs before harness timing. Initial descriptor
validation, final query evidence production, final sign, checked reading and replay
are outside this measured region. Their untimed functional outputs are
retained and independently checked; they do not supply replay timings.

## Source and correctness binding

Commit the source and this protocol before any scientific observations.
The capture requires a clean checkout and the pinned clean lean-bench
dependency, builds the executable, snapshots it outside the checkout and
records its SHA256. It records the source commit, dependency pins, Lean
version, CPU description, protocol, capture, analyzer and oracle hashes.
Only the lean-bench checkout is checked against its pin and for cleanliness;
other dependency pins describe the requested environment. The complete
snapshot SHA256 is the reproduction boundary for external link inputs and
system libraries, which are not individually validated by this capture.
Source and snapshot identity are checked again after all arms.

Before timing, emit all sixteen native functional endpoints from that same
snapshot. Check each clean/eager pair with pinned python-flint 0.9.0 in the
exact field `Q(gamma)`, where `gamma^(2^depth) = 2`. Check the original heads,
the entire stored result and identical exact residues. Native checked value
reading and selected-root/query evidence replay must succeed. Bind each timed
arm to its own 64-bit non-cryptographic raw-result fingerprint and run the sixteen harness verify
registrations. Raw representations differ between arms; their exact field
values agree. A failed check ends the capture with all attempts retained.

## Schedule and host context

Collect six trials in trial-major order. Within each trial visit depth one
then depth two, and steps 2, 4, 8, 16 at each depth. Each pair is adjacent;
use clean/eager (`AB`) in trials 0, 2, 4 and eager/clean (`BA`) in trials
1, 3, 5. This produces 96 completed arms. Use lean-bench fixed children,
one untimed warmup invocation and a final batch of at least 500 ms timed work
per arm. The harness doubles batch sizes until that floor is reached; earlier
probe batches are outside the reported observation. Arms may use different
inner-repeat counts. Each child computes its complete result on every
invocation, with no memoized answer.

Lease one automatically selected CPU and inherit its affinity in every
child. Record host load before every arm. Host activity never invalidates
an observation or triggers a quiet-core wait. Retain every command, raw
stdout/stderr, exit status, failed or interrupted attempt and completed arm.
The capture enforces a 600-second timeout on each child. The registrations'
120-second per-call setting applies when the parent harness is used; these
direct fixed-child captures use the 600-second process timeout. Both settings
are operational safeguards, not scientific performance targets.

Use one fixed capture, with no reruns or recaptures. A failed or interrupted
capture ends this study with every completed arm and attempted command
retained. No samples are discarded. SIGTERM/SIGHUP are handled as interruptions
so the child process group is stopped and failure records are written.

## Analysis and limits

For each parameter and trial divide accumulated nanoseconds by inner repeats.
Report the median and full range of six per-call observations in each arm,
and the median and full range of the six paired eager/clean ratios. For six
values the median is the mean of the middle two sorted values. Describe a
consistent direction only if all six ratios are strictly on the same side
of one; otherwise report mixed/inconclusive. Check schedule, original output,
command, source and result bindings before deriving these summaries. Derive
expected fingerprints again from retained functional stdout, verify the exact
oracle commands and successful paired outputs, check the successful harness
verify command, bind every measurement command to the snapshot and compare
its SHA256 with the artifact index. Check the current analyzer, capture,
protocol and oracle content keys before analyzing retained results.

These are descriptive shared-host observations. The finite matrix supplies
no asymptotic or significance verdict, global normalization recommendation,
regression budget or whole-Phase-4 acceptance. Depth three's earlier traced clean
context preparation timeout remains retained in the separate diagnostic
archive; it is not replaced by a timing observation. Required tower8,
MetiTarski, other scaling families, sample alternatives, serialization,
kernel replay and isolation measurements remain separate obligations.
