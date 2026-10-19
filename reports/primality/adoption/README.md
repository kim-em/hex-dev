# Adopted primality construction

With `import HexIntFactor`, `primality?` selects the measured interleaved
p-minus-one/rho/ECM provider before construction starts. One construction shares
1024 attempts across factoring, recursive certification and witnesses. The
checker and soundness theorem are unchanged. Ordinary `primality` and integer
factorization keep their separately specified policies.

The independent coverage comparison is in [the factor-policy report](../factor-policy/corpus-v3.md):
186/300 successes for this policy, 138/300 for the previous automatic Hex route,
and 170/300 for PrimeCert+SymPy, with every positive certificate kernel replayed.
These adoption checks revisit previously inspected subjects, rather than adding
independent coverage observations or tuning the policy.

## Exhausted-search cost

[measurements.json](measurements.json) retains four adjacent alternating
baseline/interleaved pairs on the 507-bit exhaustion fixture. Every completed
sample and both operational timeouts are retained. Native elapsed time includes
process startup, construction, self-checking and output formatting; it excludes
Lean proof elaboration and kernel replay. The runner leases one CPU and records
host load; shared-host activity is context, not a reason to discard samples.

| Trial | Order | Previous policy (s) | Interleaved policy (s) |
| --- | --- | ---: | ---: |
| 1 | AB | 17.69 | 147.92 |
| 2 | BA | 17.98 | 147.24 |
| 3 | AB | 17.79 | timeout at 180 |
| 4 | BA | 21.30 | timeout at 180 |

A is the previous core-first/fixed-curve retry; B is the adopted policy.
Every completed previous-policy run exhausted after 156 attempts. The two
completed interleaved runs exhausted after 642 attempts; the other two reached
the process limit without a semantic result. Each completed record contains
the construction events, subject-derived input seed and final random state.
A timeout does not establish exhaustion or compositeness.

The larger search can substantially increase unsuccessful-search cost. Tactics
have no wall-clock timeout: native search runs synchronously. A smaller
`maxAttempts` or explicit `factor := Hex.Nat.Construction.factorSearch` reduces
the allocation, without promising a time limit. Applying a successful
certificate suggestion removes search from later builds. The failed public
tactic is separately tested in `HexIntFactorFieldConformance`; this complete
filtered conformance build took 170 seconds on the shared host.

## ECPP comparison subjects

The earlier ECPP reports compared against the core-first/fixed-curve route.
The table below uses the adopted provider on the same subjects, the default
construction allocation and subject-derived seed, with a 180-second process
limit. ECPP outcomes are the retained native results, not fresh ECPP timings.

| Subject | Bits | Retained ECPP outcome | Current Pocklington/ECM outcome | Seconds |
| --- | ---: | --- | --- | ---: |
| `tuning-256-0` | 256 | success | exhausted | 119.82 |
| `tuning-256-1` | 256 | success | exhausted | 121.26 |
| `tuning-256-2` | 256 | success | success | 27.33 |
| `holdout-256-1` | 256 | success | exhausted | 146.54 |
| `validation-256-4` | 256 | success | timeout | 180.11 |
| `validation-256-5` | 256 | success | success | 5.96 |
| `validation-256-7` | 256 | success | success | 67.95 |
| `holdout-512-ordinary-0` | 512 | success | exhausted | 151.11 |
| `holdout-512-ordinary-1` | 512 | exhausted | exhausted | 148.93 |
| `holdout-512-ordinary-2` | 512 | exhausted | exhausted | 148.09 |
| `holdout-512-ordinary-3` | 512 | success | exhausted | 144.85 |
| `holdout-512-ordinary-4` | 512 | exhausted | success | 99.04 |
| `holdout-512-ordinary-5` | 512 | success | timeout | 180.08 |
| `holdout-512-difficult-0` | 512 | success | success | 4.30 |
| `holdout-512-difficult-1` | 512 | exhausted | timeout | 180.05 |

Three of the seven earlier 256-bit ECPP gains now have Pocklington certificates;
three still show genuine construction exhaustion, and one is inconclusive.
On the eight 512-bit holdouts, current construction succeeds twice, exhausts
four times and times out twice. Two held-out subjects remain genuine ECPP gains
against current construction: `ordinary-0` and `ordinary-3`. This preserves the
SPEC's requirement of two distinct 512-bit gains without counting timeouts.
The same comparison supplies genuine 256-bit gains.

All five new positive outputs are replayed as exact literals with guarded axiom
audits in [the Adoption proof probe](../../../bench/HexPrimalityMathlib/ProofProbe/Adoption.lean).
[kernel-replay.json](kernel-replay.json) links every successful row to its proof
and [kernel-replay.log](kernel-replay.log) retains the successful Lake build.
The probe is included in the existing `HexPrimalityMathlibProofProbe` CI target.
[dispatch.json](dispatch.json) and [dispatch.log](dispatch.log) retain a fresh
importing-module build confirming actual dispatcher exhaustion on one 256-bit
subject and those two 512-bit subjects, including allocation, attempt counts
and final random states. This functional probe has no elaborator heartbeat
limit so the finite construction allocation can finish.

## Sources and reproduction

The measurement uses a frozen executable, verifies its hash before each sample,
and preserves every scheduled result. [provenance.json](provenance.json) records
the dirty source tree, dependency revision, source hashes and executable hash;
[measured-source.patch](measured-source.patch) recovers the measured edits from
the recorded commit. The measured source hashes match the committed provider,
constructor and native runner. The toolchain and original report sources are
recorded in the measurements. No policy was retuned on these subjects.

```sh
lake build hexprimality_factor_experiment hexecpp_compare
python3 scripts/bench/primality_adoption.py --output /tmp/adoption.json
lake build HexPrimalityMathlibProofProbe HexIntFactorFieldConformance
python3 scripts/ci/check_primality_factor_replay.py
```

The runner refuses an existing output path. The separate
`scripts/bench/primality_adoption_replay.py` generated the retained literal proofs
and fresh importing-module confirmations; it also refuses existing proof outputs.
Publication remains a separate operation from adopting this development policy.
