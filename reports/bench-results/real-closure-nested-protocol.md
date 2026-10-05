# Nested clean/eager comparison protocol

## Workload and measured region

Use the actual validated positive roots of `(2X² - alpha)(X - 3)` in
`(0,1)`, starting with rational `alpha = 1`. Compare depths one and two,
each with 2, 4, 8 and 16 products of `(1 + alpha)`, followed by division
by `(alpha - 3)`. The selected root is never 3; the inverse exercises
the local gcd split. Both arms retain the original nonmonic descriptor.
Clean packing keeps the unreduced polynomial, apart from canonical zero.
Eager packing takes the remainder modulo the monic defining polynomial at
every algebraic level. Both execute the same ordinary coefficient kernels.

The timed IO action reads its prepared input, computes the complete product
and division, encodes the resulting raw coefficients and hashes the encoding.
It executes the action on every invocation. Preparation of all four contexts
and all sixteen input closures occurs before harness timing. Selected-root
validation, query evidence production, final sign, checked reading and replay
are outside this measured region. Their untimed functional outputs are
retained and independently checked; they do not supply replay timings.

## Source and correctness binding

Commit the source and this protocol before any scientific observations.
The capture requires a clean checkout and the pinned clean lean-bench
dependency, builds the executable, snapshots it outside the checkout and
records its SHA256. It records the source commit, dependency pins, Lean
version, CPU description, protocol, capture, analyzer and oracle hashes.
Source and snapshot identity are checked again after all arms.

Before timing, emit all sixteen native functional endpoints from that same
snapshot. Check each clean/eager pair with pinned python-flint 0.9.0 in the
exact field `Q(gamma)`, where `gamma^(2^depth) = 2`. Check the original heads,
the entire stored result and identical exact residues. Native checked value
reading and selected-root/query evidence replay must succeed. Bind each timed
arm to its own complete raw-result hash and run the sixteen harness verify
registrations. Raw representations differ between arms; their exact field
values agree. A failed check ends the capture with all attempts retained.

## Schedule and host context

Collect six trials in trial-major order. Within each trial visit depth one
then depth two, and steps 2, 4, 8, 16 at each depth. Each pair is adjacent;
use clean/eager (`AB`) in trials 0, 2, 4 and eager/clean (`BA`) in trials
1, 3, 5. This produces 96 completed arms. Use lean-bench fixed children,
one untimed warmup invocation and at least 500 ms accumulated timed work
per arm. Each child computes its complete result, with no memoized answer.

Lease one automatically selected CPU and inherit its affinity in every
child. Record host load before every arm. Host activity never invalidates
an observation or triggers a quiet-core wait. Retain every command, raw
stdout/stderr, exit status, failed or interrupted attempt and completed arm.
The capture enforces a 600-second timeout on each child. The registrations'
120-second per-call setting applies when the parent harness is used; these
direct fixed-child captures use the 600-second process timeout. Both settings
are operational safeguards, not scientific performance targets.

Use one fixed capture, with no rerun after mixed or inconclusive results.
At most one unchanged recapture is permitted after an operational failure,
retaining the original capture. No samples are discarded.

## Analysis and limits

For each parameter and trial divide accumulated nanoseconds by inner repeats.
Report the median and full range of six per-call observations in each arm,
and the median and full range of the six paired eager/clean ratios. For six
values the median is the mean of the middle two sorted values. Describe a
consistent direction only if all six ratios are strictly on the same side
of one; otherwise report mixed/inconclusive. Check schedule, original output,
command, source and result bindings before deriving these summaries.

These are descriptive shared-host observations. The finite matrix supplies
no asymptotic or significance verdict, global normalization recommendation,
regression budget or whole-Phase-4 acceptance. Depth three's earlier clean
context preparation timeout remains retained in the separate diagnostic
archive; it is not replaced by a timing observation. Required tower8,
MetiTarski, other scaling families, sample alternatives, serialization,
kernel replay and isolation measurements remain separate obligations.
