# Nested clean/eager product and division comparison

The actual validated roots of `(2X² − alpha)(X − 3)` in `(0,1)` form a
one- or two-level tower, starting at rational `alpha = 1`. Each arm computes
`(1 + alpha_d)^m / (alpha_d − 3)` for m = 2, 4, 8, 16.

Production clean packing leaves the nonmonic-head representations unreduced
apart from canonical zero. The benchmark's eager arm reduces once per operation
at every algebraic level modulo the monic **cubic**, retaining its extraneous
root 3. This is not a minimal quadratic or canonical representation. Both arms
use the original defining heads, selected intervals and ordinary coefficient
kernels; lower-level representations and descriptor evidence can differ.

## Measurement and provenance

Captured clean source `ca2e226dd870f247fe9ec5f5ade44989f975ce19`, published tag
`issue-10378-nested-measurement-source-ca2e22`. Executable SHA-256:
`84a51d92f2f590a302ab140364a3322f3a147c236552ef6cabbc14fc981174c2`.
The original complete capture, including the 120771072-byte executable,
remains at `/home/kim/.codex/tasks/hex-10378/nested-measurement-capture-ca2e22`.
This archive preserves the original manifest and every command stdout/stderr,
command JSON and derived analysis. `archive.json` binds all archived files and
identifies the binary omitted from git. The 395 original records are unchanged;
four additional files under `sources/` preserve the captured analyzer, capture
script, protocol and oracle. Original absolute command paths remain unchanged.
The capture tag records the measurement source; it is distinct from the merged
integration commits. The benchmark and its Lean import closure are unchanged
by this packaging and archive validation.

The protocol was committed before observations. Six fixed trial-major trials
visit depth one then two and m = 2, 4, 8, 16, with adjacent AB/BA arms alternating
between trials. All 96 arms completed in one capture; none were discarded or
rerun. Each final child batch accumulates at least 0.5 seconds of timed work;
autotuning probes and one warmup invocation are outside the observation.
Inner-repeat counts differ across arms and remain recorded in the analysis.
The 600-second process limit is an operational safeguard.

The timed action reads a prepared runtime input, performs the full products
and division, then encodes and hashes the actual raw result. Every invocation
executes that computation. Packing's selected-root zero/sign queries,
pseudo-division, Sturm queries and recursive coefficient arithmetic are inside
timing, including the query packing the final result. Context preparation,
final query evidence production, the later cached sign read, checked reading
and mathematical replay are outside timing. Untimed outputs for all sixteen
endpoints pass native root/query replay and reading, eight paired FLINT exact
checks, and all sixteen harness verifications.

Host: chungus2, AMD EPYC 9455, Linux x86_64, automatically leased CPU 21 with
single-CPU affinity. Initial load: 10.345/10.554/13.962. Every arm records its own
load; host activity never triggered rejection or a quiet-core wait. Lean
4.35.0-rc3 and lean-bench `8a37daf1074c3bdbd0da479b55538bad4a0022db` are recorded
with all declared dependency pins. Only lean-bench cleanliness/pin is checked
individually; the complete executable digest binds external link inputs.

## Observations

Medians are over six per-call observations, each accumulated nanoseconds divided
by inner repeats. The paired ratio median is over six within-trial eager/clean
ratios. The six-value median averages the middle two values. A consistent
direction requires all six ratios strictly on the same side of one.

| Depth | Products | Clean median ms (full range) | Eager median ms (full range) | Paired eager/clean median (full range) | Direction |
| ---: | ---: | --- | --- | --- | --- |
| 1 | 2 | 0.065335 (0.064857–0.066142) | 0.065685 (0.064748–0.069027) | 1.009810 (0.986933–1.043624) | mixed/inconclusive |
| 1 | 4 | 0.125460 (0.124267–0.126486) | 0.117471 (0.115849–0.119925) | 0.934034 (0.923087–0.955214) | eager lower in all six trials |
| 1 | 8 | 0.282623 (0.280157–0.287872) | 0.233025 (0.229478–0.236550) | 0.824175 (0.797153–0.836601) | eager lower in all six trials |
| 1 | 16 | 0.782241 (0.772050–0.800627) | 0.519895 (0.517559–0.522741) | 0.665654 (0.646455–0.672400) | eager lower in all six trials |
| 2 | 2 | 39.276982 (39.148054–40.147879) | 5.293715 (5.224749–5.351247) | 0.134639 (0.132005–0.136274) | eager lower in all six trials |
| 2 | 4 | 96.957614 (96.284851–98.149234) | 10.815214 (10.793161–11.108081) | 0.111728 (0.109967–0.114734) | eager lower in all six trials |
| 2 | 8 | 333.861724 (332.416852–336.254316) | 27.351069 (26.808620–36.311950) | 0.082059 (0.080648–0.108640) | eager lower in all six trials |
| 2 | 16 | 1724.400296 (1720.014695–1734.175282) | 68.573986 (67.726031–69.442516) | 0.039732 (0.039375–0.040187) | eager lower in all six trials |

The smallest depth-one case is mixed. Eager is lower in every pair of each
other parameter combination. The finite matrix supports these descriptive
observations only; it supplies no asymptotic fit, significance test, absolute
budget verdict or global production normalization decision.

## Exact values and representation growth

Pinned python-flint 0.9.0 independently evaluates every stored coefficient in
`Q(gamma)` with `gamma^(2^depth) = 2`, checks defining heads and exact values,
and confirms the two policy residues agree. It checks signs at the assumed
positive algebraic coordinates and the graph structure; it does not authenticate
the selected root or mathematically replay the graphs. The native checked
readers and descriptor/query replay perform those checks before timing.

| Depth | Products | Stored degrees by level clean/eager | Stored bytes clean/eager | Stored coefficient bits clean/eager | Final query graph bytes clean/eager |
| ---: | ---: | --- | ---: | ---: | ---: |
| 1 | 2 | [3] / [2] | 35 / 27 | 33 / 26 | 2169 / 2154 |
| 1 | 4 | [5] / [2] | 53 / 29 | 56 / 42 | 2397 / 2346 |
| 1 | 8 | [9] / [2] | 93 / 39 | 110 / 71 | 2865 / 2725 |
| 1 | 16 | [17] / [2] | 197 / 57 | 307 / 133 | 3986 / 3587 |
| 2 | 2 | [2, 3] / [2, 2] | 141 / 107 | 219 / 187 | 430847 / 4958 |
| 2 | 4 | [2, 5] / [2, 2] | 216 / 125 | 358 / 225 | 1106461 / 7114 |
| 2 | 8 | [2, 9] / [2, 2] | 383 / 151 | 666 / 313 | 2438985 / 10665 |
| 2 | 16 | [2, 17] / [2, 2] | 765 / 221 | 1433 / 557 | 6211399 / 17869 |

Stored degrees are listed from the bottom algebraic level to the top.
The final query evidence is generated outside timing; packing performs related
selected-root queries inside timing. Evidence byte growth therefore describes
the retained final evidence, and is not itself a replay timing. Full endpoint
outputs retain rational coefficient counts, numerator/denominator bits, every
root graph and their exact residues. Separate generated-C diagnostic counts
remain in `real-closure-nested-diagnostics-c7d917`; they were not collected
concurrently with these observations.

## Scope and reproduction

This family covers only depths one/two with short product chains and one
selected positive root at every level. It includes the nonconstant gcd split
in inversion. It does not measure general BKR systems, arbitrary depth,
serialization parsing, exporter checking, ordinary-kernel proof cost or
ordinary-real sample alternatives. The earlier depth-three clean **traced
preparation** timeout remains retained in the diagnostic archive; it was not
replaced by an untraced measurement or counted as an observation here.
Tower8's premise correction, MetiTarski scaling and the other specified Phase 4
requirements remain open.

To validate this git archive without restoring the executable, run:

```sh
python3 scripts/bench/analyze_real_closure_nested.py --archive reports/bench-results/real-closure-nested-measurement-ca2e22
```

This read-only check validates the complete inventory and all content digests,
binds the omitted executable's digest to the original manifest, and hash-checks
the frozen source copies. The live validator recomputes the analysis from all
96 raw arms using the versioned historical schedule and interpretation wording,
compares it to the complete recorded v1 output, and checks both tables above
against retained observations. The copied analyzer is not executed.
It runs in the existing CI job. Live capture-script, protocol and oracle changes
do not invalidate historical source keys. The executable is not rerun by this
check; its byte count is asserted by the archive metadata rather than verified
from this partial archive. The omitted binary's bytes remain available only in
the full capture.

To regenerate the original analysis, use a clean checkout of the published
capture tag with the **full original capture**, including its executable.
Move the existing `analysis.json` aside before running
`python3 scripts/bench/analyze_real_closure_nested.py /home/kim/.codex/tasks/hex-10378/nested-measurement-capture-ca2e22`;
that analyzer refuses to overwrite the derived file and checks its original
source keys. Historical absolute argv paths remain provenance, not commands
redirected by this packaging. The captured executable can emit each endpoint
with `depth steps clean|eager plain`; its `verify` command checks all sixteen
registrations. Rebuilding from the tag is a reproduction of the source, without
a guarantee of the captured executable's byte identity.
