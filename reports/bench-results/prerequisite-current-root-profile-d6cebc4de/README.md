# Current polynomial-root representative attribution

This capture supplies the required representative attribution for the
`real-polynomial-roots` input family on source `d6cebc4de`, with the certified
parent isolation reuse in merged PR #10695. It makes no scientific verdict,
portable budget or Phase-4 attestation.

The native `Hex.RealAlgebraicBench.runRationalRoots8` case, parameter 0,
uses the actual `RealAlgebraicPoly.roots` API for `X^8 - 2`. Prepared coefficients
are outside the operation; root production, exactification, filtering,
sorting and the complete ordered fingerprint remain inside it.

Command:

```sh
python3 capture.py --family rational-roots \
  --raw /home/kim/.local/state/hex/issue-10577-profiles/real-rational-roots-isolation-reuse-d6cebc4de \
  --output /home/kim/.local/state/hex/issue-10577-proposals/isolation-reuse/current-root-profile \
  --profiler-root /home/kim/.local/state/hex/issue-10377-profiles/lean-bench-samply \
  --target-nanos 2000000000
```

The manifest records automatically leased CPU 28, observed host activity,
exact executable and source hashes, all commands and 47 retained artifact
checksums. Raw perf/samply files, the kernel sidecar, source snapshots, executed
collector and frozen executable live in the persistent raw directory above.
Completed samples are retained without a host-activity filter or rerun.

The filtered 1266 kernel-window samples pass calibration, sample-count and
±5 ms sensitivity checks. These are operation-only attribution samples,
not a replacement for the retained adjacent timing comparisons. Isolation
has 94.47% inclusive share. Exactification (62.48%) and component norm-root
selection (31.60%) are inclusive shares and are not summed. The summary
classifies all leaf cost and keeps other/unresolved cost visible.
