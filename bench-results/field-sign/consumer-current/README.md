# Common-field consumer sign comparison

Six adjacent pairs compare canonical algebraic-number conversion (`legacy`)
with the eliminant-bounded interval sign (`interval`) on the three complete
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
recorded workload shows a modest median improvement with substantial variation.
The ratio of separate arm medians (1.345) is not the paired statistic. Every
completed sample is retained, including the slower interval pair. Host load is
recorded context and was not used to exclude samples or request a rerun.

The frozen binary was built from clean commit
`615fc667c8427f8cc0f98aca21d64587a32b2d27` (PR #10641), using the generic
`QAdjoin.signApprox` API with its per-call generator-reality check. Metadata
records the binary hash, computational source hashes, toolchain and shared-host
CPU placement. One automatically leased CPU was used for all adjacent arms;
pair order alternated AB/BA. Earlier scalar observations refer to a different
implementation and must not be attributed to this binary.

All twelve outputs are byte-identical to the retained `fixtures.jsonl` and the
committed common-field fixture. Independent FLINT qqbar evaluation accepts all
three cases, reconstructing original roots, selected embeddings, coordinates,
root signs/order and common-polynomial comparisons without Lean replay data.
The samples and summary have also been checked for pair order, successful exit,
output hash and exact median/ratio agreement.

Reproduce at the recorded source revision:

```sh
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
separate under #10377 and #10635.
