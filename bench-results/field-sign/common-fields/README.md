# Common-field consumer sign comparison

Six adjacent pairs compare canonical algebraic-number conversion (`legacy`)
with the staged interval sign (`QAdjoin.signApprox`, `interval`) on the three complete
common-field fixtures. The quadratic inputs √2 and √3 are independently
constructed in both orders, producing degree-four coefficient fields. The
cubic inputs ∛2 and ∛4 produce a degree-three field. Each process performs field
construction, sign tables, root enumeration, selected-root signs, comparisons
and serialization. These are native end-to-end process times, including
startup; they do not isolate coefficient callback cost.

| Statistic | Observation |
| --- | --- |
| Canonical arm median | 122.203 s |
| Interval arm median | 90.871 s |
| Median within-pair canonical/interval ratio | 1.252 |
| Within-pair ratio range | 0.902–1.781 |
| Completed samples / unchanged reruns | 12 / 0 |

Five pairs favour interval signs; one favours canonical conversion. The
recorded paired median favours interval signs, with substantial variation; these
six pairs do not establish a general effect size.
The ratio of separate arm medians (1.345) is not the paired statistic. Every
completed sample is retained, including the slower interval pair. Host load is
recorded context and was not used to exclude samples or request a rerun. On
the 96-CPU host, the recorded one-minute load averages ranged from about 4 to
94. The two slowest interval runs (117.1s and 123.6s) ended at load averages
84 and 88; the canonical arm in the reversed pair ended at load 21. These
observations do not establish the cause of timing variation.

The frozen binary was built from clean commit
`615fc667c8427f8cc0f98aca21d64587a32b2d27` ([PR #10641](https://github.com/kim-em/hex-dev/pull/10641)), using the generic
`QAdjoin.signApprox` API with its per-call generator-reality check. Metadata
records the binary hash, five relevant source hashes, toolchain and shared-host
CPU placement; the clean revision fixes all other sources. `validation.json`
records matching hashes of the frozen executable and the built executable at
that unchanged checkout, as well as verification of all five source hashes. One automatically leased CPU was used for all adjacent arms;
pair order alternated AB/BA. Earlier scalar observations refer to a different
implementation and must not be attributed to this binary.

All twelve outputs are byte-identical to the retained `fixtures.jsonl` and the
committed common-field fixture. Independent FLINT qqbar evaluation accepts all
three cases, reconstructing original roots, selected embeddings, coordinates,
root signs/order and common-polynomial comparisons without Lean replay data.
The samples and summary have also been checked for pair order, successful exit,
output hash and exact median/ratio agreement. `oracle.log` retains the oracle
result and FLINT version. Zero unchanged reruns is reported by the operator;
the runner's hardcoded `reruns` field does not prove that historical claim.

Merge the implementation before using these reproduction commands. To obtain
the exact recorded source, fetch the PR history and use a separate worktree:

```sh
git fetch origin pull/10641/head
git worktree add --detach ../field-sign-measured 615fc667c8427f8cc0f98aca21d64587a32b2d27
cd ../field-sign-measured
lake build hexsigndet_emit_common_fields
python3 scripts/bench/field_sign_paired.py \
  .lake/build/bin/hexsigndet_emit_common_fields new-output-directory
uv run --with python-flint==0.9.0 python \
  scripts/oracle/sign_det_common_fields.py \
  new-output-directory/fixtures.jsonl --profile local
```

This fixed consumer comparison establishes no general dispatch threshold,
interpreter bottleneck, persistent sign cache, asymptotic scaling verdict,
allocation/live-memory result or Phase-4 attestation. Those requirements remain
separate under [#10377](https://github.com/kim-em/hex-dev/issues/10377) and
[#10635](https://github.com/kim-em/hex-dev/issues/10635). No stage-specific
counters were recorded; these timings do not establish which interval probe
handled the coefficient signs.
