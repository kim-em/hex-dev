# Shared real-closed-field proof evidence

The probe imports the `HexRealRootsMathlib` umbrella, synthesizes `IsRealClosed ℝ`,
and applies `IsRealClosed.exists_isRoot_of_odd_natDegree` to an arbitrary
odd-degree real polynomial. The matched baseline imports the same umbrella.
This measures fresh-module elaboration and ordinary kernel checking of those
uses, with imported proofs warm; it does not measure construction of the
instance or the future signed-query/replay bridge.

[Raw samples and provenance](bench-results/hex-real-closed-a57215a438ad-chungus2.json) record clean commit
`a57215a438adac2126507baaee25e6d5eebf91b4`, Lean 4.34.0, all source hashes and dependency revisions,
artifact sizes, axiom sets, and host activity. The host is `chungus2`
(AMD EPYC 9455), Linux, automatically selected logical CPU 18 with SMT sibling 66.

```sh
proof_cpu=$(python3 scripts/bench/idle_core.py)
taskset -c "$proof_cpu" python3 scripts/bench/real_closed_sweep.py \
  --shared-host --cpu "$proof_cpu" --output /tmp/real-closed-proof.json
```

Four preregistered adjacent pairs alternate orientation. Before each arm,
the harness deletes only that module's generated artifacts and runs
`lake build +<module>:olean`. Imports stay warm. The per-arm timeout is 60 s;
the warmup timeout is 600 s. No sample timed out or was discarded, no rerun
was performed, and the harness reports complete, release-quality evidence
with no provenance exceptions. Host activity is recorded context.

| Round | Order | Baseline (s) | Probe (s) | Probe − baseline (s) |
| --- | --- | ---: | ---: | ---: |
| 1 | reference → candidate | 21.402138 | 23.956494 | +2.554356 |
| 2 | candidate → reference | 29.482096 | 22.445486 | -7.036611 |
| 3 | reference → candidate | 21.227862 | 19.652673 | -1.575189 |
| 4 | candidate → reference | 18.232171 | 21.225076 | +2.992905 |

Median baseline: 21.315000 s; median probe:
21.835281 s; median paired delta:
+0.489583 s. The deltas vary in sign and
span several seconds, so these samples do not establish a measurable
incremental cost. No null control or complexity verdict is claimed.

The probe artifacts are 6,360 bytes (`olean`), 2,296 bytes (`olean.private`),
1,544 bytes (`olean.server`), and 2,023 bytes (`ilean`). Both probe theorems
have exactly `propext`, `Classical.choice`, and `Quot.sound` as axioms;
compile-time guards also check the real instance and the downstream
real-algebraic instance. No runtime arithmetic benchmark or library phase
counter is changed by this evidence.
