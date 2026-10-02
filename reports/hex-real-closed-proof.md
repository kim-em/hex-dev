# Shared real-closed-field proof evidence

The probe imports the `HexRealRootsMathlib` umbrella, synthesizes `IsRealClosed ℝ`,
and applies `IsRealClosed.exists_isRoot_of_odd_natDegree` to an arbitrary
odd-degree real polynomial. The matched baseline imports the same umbrella.
This measures fresh-module elaboration and ordinary kernel checking of those
uses, with imported proofs warm. Instance synthesis and one theorem application
add little work to the import baseline; this is chiefly an export/use regression.
It does not measure construction of the instance or the future signed-query/replay
proofs, and does not isolate their kernel-checking cost.

[Raw samples and provenance](bench-results/hex-real-closed-af51d5a6d88a-chungus2.json) record published clean commit
[`af51d5a6d88abf95650c59e021df16d382c70258`](https://github.com/kim-em/hex-dev/commit/af51d5a6d88abf95650c59e021df16d382c70258),
Lean 4.34.0, all source hashes and dependency revisions, artifact sizes, axiom
sets, and host activity. The host is `chungus2` (AMD EPYC 9455), Linux,
automatically selected logical CPU 1 with SMT sibling 49.

```sh
proof_cpu=$(python3 scripts/bench/idle_core.py)
taskset -c "$proof_cpu" python3 scripts/bench/real_closed_sweep.py \
  --shared-host --cpu "$proof_cpu" --output /tmp/real-closed-proof.json
```

Four preregistered adjacent pairs alternate orientation. Before each arm,
the harness deletes only that module's generated artifacts and runs
`lake build +<module>:olean`. Imports stay warm. The per-arm timeout is 60 s;
the warmup timeout is 600 s. No sample timed out or was discarded, and the
harness reports complete, release-quality evidence with no provenance exceptions.
Host activity is recorded context.

| Round | Order | Baseline (s) | Probe (s) | Probe − baseline (s) |
| --- | --- | ---: | ---: | ---: |
| 1 | reference → candidate | 9.072856 | 9.144081 | +0.071225 |
| 2 | candidate → reference | 7.273158 | 7.579703 | +0.306545 |
| 3 | reference → candidate | 8.041754 | 9.170759 | +1.129005 |
| 4 | candidate → reference | 7.771740 | 9.138137 | +1.366398 |

Median baseline: 7.906747 s; median probe:
9.141109 s; median paired delta:
+0.717775 s. These are host-specific fresh-build
times, not isolated marginal proof costs. No null control, speedup, or complexity
verdict is claimed.

The probe artifacts are 6,360 bytes (`olean`), 2,296 bytes (`olean.private`),
1,544 bytes (`olean.server`), and 2,023 bytes (`ilean`). Both probe theorems
have exactly `propext`, `Classical.choice`, and `Quot.sound` as axioms;
compile-time guards also check the real instance and the downstream
real-algebraic instance. No runtime arithmetic benchmark or library phase
counter is changed by this evidence.

[Additional retained samples](bench-results/hex-real-closed-a57215a438ad-chungus2.json)
record the earlier source snapshot before the branch rebase, including all four
completed pairs. Their recorded commit is not published and their Lake source hash
differs from the current manifest; the current-source evidence is the published
commit and sample set linked above. No unchanged rerun was performed.
