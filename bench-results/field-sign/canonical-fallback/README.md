# Two-probe sign strategy with canonical fallback

These observations concern the recorded two-probe strategy with canonical
conversion as its final fallback. They do not measure the eliminant-bounded
endpoint used by `RealAlgebraicNumber.signField` in the current implementation.

The interval strategy reduced median end-to-end time for the three common-field
oracle fixtures from 110.044 s to 86.252 s on the recorded shared host: a ratio
of 1.276, or a 21.6% reduction in elapsed time. These are host-specific
observations, not portable latency bounds or evidence of asymptotic complexity.

Both arms run the same executable and the same fixture algorithm. The reference
converts each field coordinate to a canonical real algebraic number before
determining its sign. The interval arm uses `RealAlgebraicNumber.signField`:
constants are handled directly; nonconstant coordinates are evaluated on the
generator's certified enclosure, then on a refined enclosure if needed. Exact
conversion remains the fallback after both probes are inconclusive.

The fixtures include a degree-four common field for independently selected
positive roots of `X²−2` and `X²−3`, both input orders, and a cubic field for
the positive roots of `X³−2` and `X³−4`. They exercise simultaneous signs,
root enumeration, selected-root signs, comparison, common-product re-encoding,
equality across expressions, and rejection of copied or stale evidence.
Input construction, serialization and process startup are included in each
observation. This suite is broader than the manual's sign-table example.

All twelve completed observations are retained in `samples.jsonl`. Six adjacent
blocks alternate reference/interval and interval/reference. The process and its
children run on one automatically leased CPU; load observations are recorded
as context. No sample was excluded and there was no rerun. Every observation
produced identical bytes, with SHA-256
`59838a9da9649c10170d58af62a12fe5cb74ff77ab835516a50b16e5a8a2e56b`.
The independent FLINT qqbar oracle accepted all three cases with zero failures.

`metadata.json` records the binary hash, source hashes, toolchain, baseline
revision and host placement. The measured executable was built from the
recorded baseline plus the hashed interval-sign and fixture sources. The source
hashes identify those changes even though the baseline revision predates their
commit. The paired comparison concerns the two strategies in that executable.

One explanatory native profile collected 8,392 user CPU-clock samples at 99 Hz,
with zero lost samples. Flat self samples include `malloc` (14.60%), `cfree`
(9.64%), GMP integer initialization (5.77%), Lean small-object allocation
(4.33%), and dyadic addition (2.75%). The stack data did not give reliable caller
attribution for these allocations, so this profile cannot establish how often
the interval fallback ran or assign the remaining cost to a particular phase.
It is not a Phase-4 attribution or memory gate.

To reconstruct the measured strategy, use baseline commit
`b696cf86df2175d64e26ecf6039b50aa7732a58f` in an isolated checkout and restore
`HexRealAlgebraic/FieldSign.lean`, `HexRealAlgebraic.lean`,
`conformance/HexSignDet/CommonField.lean`,
`conformance/HexSignDet/EmitCommonFields.lean` and
`scripts/bench/field_sign_paired.py` from commit
`bccae5dbc231b94c06cef5b34fb99ce63edf8e14`. The recorded hashes verify the
measured source files. Build with `lake build hexsigndet_emit_common_fields`, then run:

```sh
python3 scripts/bench/field_sign_paired.py \
  .lake/build/bin/hexsigndet_emit_common_fields new-output-directory
uv run --with python-flint==0.9.0 python \
  scripts/oracle/sign_det_common_fields.py \
  new-output-directory/fixtures.jsonl --profile local
```

The output directory must be new. The measurement driver fails if either arm
fails or their output bytes differ. Sign caching across callbacks, the claimed
interpreter bottleneck, and the remaining coefficient-size/nested-field scaling
obligations are not established by this fixed comparison.
