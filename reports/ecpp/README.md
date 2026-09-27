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

The explicit tactic limit is 65-bit subjects and numerals, 8,192 inspected
syntax nodes, 32 total certificate nodes, and 128 inverse witnesses per step.
The 256- and 512-bit fixtures are compiled-checking and oracle inputs, not
kernel-replay CI requirements or admitted tactic inputs. The bounded PARI
parser allows 16,384 input bytes, 170 digits per integer, 20 rows, 512-bit
integers and scalars, 1,200 inverse operations, and 200 endpoint search fuel.
These limits cover the measured supplied vectors; exhaustion is reported
explicitly.
