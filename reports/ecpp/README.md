# ECPP implementation measurements

These observations were collected on the shared host `chungus2` with Lean
4.34.1, PARI/GP 2.17.3, and one pinned CPU (13) on 2026-09-27. The host was
shared; no quiet-core preflight or sample rejection was used. The JSON files
retain every completed sample. Wall times are host-specific observations, not
CI limits.

## Compiled checker and conversion

`reports/ecpp/compiled.json` is the five-repeat `lean-bench` export from the
Mathlib-free `hexecpp_bench` executable, built on the issue branch at
`de25e7b` with later report/probe edits in the worktree. Input certificates
were read through `IO.Ref` at runtime. Each accepted fixture returned the
expected result hash.

| Subject size | `check` median | supplied PARI conversion and recheck median | PARI `primecertisvalid` median |
| --- | ---: | ---: | ---: |
| 65 bits | 0.155 ms | 0.751 ms | 0.050 ms |
| 256 bits | 5.544 ms | 82.320 ms | 2.390 ms |
| 512 bits | 21.084 ms | 500.681 ms | 9.950 ms |

The PARI column uses the corresponding supplied ECPP vectors, with five
trial-major repetitions of 100 validations for the 65- and 256-bit cases and
20 for 512 bits. `reports/ecpp/pari-verify.json` records the integer-millisecond
batch samples. PARI accepts a prime endpoint below 64 bits under its own
certificate convention. Hex instead verifies an explicit `PrimeCert` at each
endpoint, so the verification operations and certificate formats differ. PARI
is an independent comparator and never a proof dependency. Its
`elladd`/`ellmul` operations also agree with all accepted emitted affine cases.

The 512-bit parser alone measured 0.797 ms median. The frozen PARI text sizes
are 93, 1,999, and 6,406 bytes; the corresponding Hex raw-certificate
step-plus-inverse counts are 70, 2,067, and 6,735. The latter count excludes
embedded `PrimeCert` data and is not a serialized byte size.

## Fresh-module proof production

`reports/ecpp/proof65.json` records three trial-major runs of four fresh-module
builds, deleting the target `.olean` before each. All other dependencies
remained built. The modules are the import/numeral baseline, data reification
without checker replay, direct kernel replay, and full `ecpp using` proof.
Their medians were 3.264, 3.271, 3.463, and 3.373 seconds, respectively.
The direct and tactic modules both produce `Nat.Prime 18446744073709551629`;
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The small `Nat.Prime 17` ECPP step also replays in the kernel.

`reports/ecpp/shared17.json` contains five adjacent, alternating `EP`/`PE`
pairs on the shared subject 17, where `E` is the ECPP step and `P` is the
existing `primality` route. Each measurement deleted the target `.olean` and
used the same shared imports. The medians were 3.264 seconds for ECPP and
3.264 seconds for `primality`; these are dominated by module startup. On the
256-bit accepted ECPP subject, the existing bounded Pocklington policy
exhausts after 28 attempts, as pinned by `HexECPP.PolicyProbe`. No total
fallback is used.

The initial touch-only probe runs are retained as
`no-rebuild-probe65.json` and `no-rebuild-shared17.json`. Lake's content hashes
meant later trials did not rebuild the target, so those files measure
up-to-date checks rather than proof production. They are excluded from the
proof medians above for that methodological reason.

## Larger replay and import cost

`proof256.json` and `proof512.json` retain the five trial-major runs of import
baseline, reification, direct kernel replay and tactic replay. These runs
used temporary replay limits on source `fc032f580` (recorded in each file),
Lean 4.34.1 and automatically leased CPUs 56 and 58. Every completed sample
was retained. They establish replay of the frozen inputs, not successful
certificate generation for every subject at the same bit size.

| Bits | Import baseline | Reification | Direct kernel proof | Tactic proof | Tactic peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| 256 | 3.402 s | 3.421 s | 6.749 s | 4.934 s | 4.273 GiB |
| 512 | 3.286 s | 3.390 s | 15.220 s | 8.484 s | 4.923 GiB |

The frozen 256-bit raw constructor traversal uses 31,511 syntax nodes and
13 total certificate nodes; its largest step uses 368 inverse witnesses.
The 512-bit traversal uses 101,839 syntax nodes, 23 certificate nodes and
at most 764 inverse witnesses in one step. The admitted policy is therefore
512-bit subjects and numerals, 131,072 inspected syntax nodes, 32 certificate
nodes and 1,024 inverse witnesses per step. Fresh-module probes cover all
three admitted frozen sizes in the existing CI job. Kernel axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.

`import-cost.json` retains six adjacent alternating pairs for `Nat.Prime 17`
using `primality`, with and without importing the ECPP bridge (CPU 90).
Median fresh-module time was 1.790 s without that import and 3.420 s with it;
the median paired difference was 1.648 s. Peak RSS medians were 2.040 GiB and
3.977 GiB. The PARI interface remains an explicit optional import.

The bounded PARI parser allows 16,384 input bytes, 170 digits per integer,
20 rows, 512-bit integers and scalars, 1,200 inverse operations per scalar,
and 200 endpoint search fuel. These limits cover the measured supplied
vectors; exhaustion is reported explicitly.

## Compact source and PARI interface

`pari-interface.json` records end-to-end generation and file export using
PARI/GP 2.17.3, plus the deterministic protocol-stub test. Real PARI generation
produced a 2,661-byte source module for the 256-bit subject and a 7,098-byte
module for the 512-bit subject. The expanded constructor fixtures occupy
137,595 and 772,367 source bytes. These are representations of the same
checking obligations: compact source recomputes the inverse transcript during
elaboration and the kernel still checks the complete raw certificate.

The test builds the generated module and its importing proof after replacing
`gp` with an executable that records any invocation and fails. It also copies
both `Nat.Prime` and `Hex.Nat.Prime` TryThis replacements verbatim into fresh
theorem bodies, including computed subjects, and kernel-replays them without
calling GP. No invoked-GP marker was
created. The initial 512-bit process attempt hit PARI's 8 MB default stack;
that failure is retained in the interface record. The process policy now
starts with a fixed 64 MB stack and reports stack exhaustion as a CAS failure.

The process conformance tests cover missing executables, stderr/nonzero exit,
framing, composite results, stdout/stderr bounds, cancellation and a timeout
whose parent and descendant ignore TERM. The export test checks exclusive
creation, invalid names, an editor invocation that leaves no file and calls no
GP, and that a duplicate export preserves the original file. An exited leader
with descendants holding its pipes also exhausts cleanly; process cleanup stays
within the operational test limit. GP requests use private temporary files
with null stdin, preserving the original process-group handle.

`compact-replay.json` retains three serial trial-major fresh builds of each
large proof probe using automatically leased CPU 56. The compact
fixture module was already built, so this measures proof production rather
than compact decoding or reification. Median wall times were 4.933 s
for 256 bits and 8.561 s for 512 bits. All six axiom audits contain
only the three standard Lean axioms listed above; all completed samples and
host observations are retained.
