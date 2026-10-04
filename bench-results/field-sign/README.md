# Field-coordinate sign strategies

The eliminant-bounded interval operation is substantially faster on the recorded
close-value family. Median end-to-end time for twenty signs was 54.805 ms,
compared with 2.334 s for canonical conversion. The median within-block
reference/interval ratio was 42.567. These are observations on the recorded
shared host, including generator construction and process startup.

`scalars/` retains all twelve observations, metadata, exact outputs and summary.
Its computational source hashes match commit
`7b2b23f7f68406e58ba0345d7d4d8e6ffc0cdae1`, before the number-field API
refactoring. Rebuild that version in a separate worktree with
`lake build hexsigndet_emit_common_fields`. The reported times refer to the
recorded binary; they do not measure the current per-call reality check.
Six adjacent blocks alternate reference/interval and interval/reference on one
automatically leased CPU. No completed sample was excluded and there was no
rerun. All outputs agree byte for byte. An independent FLINT qqbar evaluation
accepted all twenty coordinate signs.

The quadratic family evaluates both signs of `(3−2√2)^n` for
`n = 4, 8, 16, 32, 64, 128`. Its reduced power-basis coordinates have large
opposing coefficients while the selected value approaches zero. The cubic
family evaluates both signs of `(∛2−1)^n` for `n = 8, 16, 32, 80`.
This exercises cancellation and tiny values, including the final bounded
precision probe. It is a fixed family comparison, not a general degree/height
dispatch threshold or a Phase-4 scaling gate.

The interval arm handles constants directly, first reads the stored generator
enclosure, then requests a modest refinement. If both probes are inconclusive,
it computes an integer norm eliminant of `T−value` and derives a finite output
precision from its reciprocal-Cauchy lower bound. The correctness and endpoint
success proofs cover every branch. The executable interval arm performs no
canonical algebraic-number conversion.

`canonical-fallback/` retains observations for the explicitly identified
two-probe strategy whose final fallback canonicalizes the value. Its source and
binary hashes define that separate comparison; its timings do not describe the
eliminant-bounded endpoint. All completed observations remain available.

Build and run the close-value comparison with:

```sh
lake build hexsigndet_emit_common_fields
python3 scripts/bench/field_sign_paired.py \
  .lake/build/bin/hexsigndet_emit_common_fields new-output-directory --mode scalars
uv run --with python-flint==0.9.0 python \
  scripts/oracle/sign_det_common_fields.py \
  new-output-directory/fixtures.jsonl --scalars --profile local
```

The output directory must be new. Metadata records the executable hash,
computational source hashes, baseline revision, dirty-tree state, toolchain and
host placement. The source hashes identify the measured code even when its
changes are not committed at measurement time. The paired statistic uses the
six within-block ratios; separate arm medians are also retained.

These observations establish neither a sign cache across callbacks nor the
claimed interpreter bottleneck. [Common-field consumer observations](common-fields/README.md) retain a
separate comparison of the generic API at its recorded source revision,
including the per-call reality check and all twelve completed samples.
Allocation, nested-field scaling and ordinary-kernel proof-checking costs
retain separate evidence obligations.
