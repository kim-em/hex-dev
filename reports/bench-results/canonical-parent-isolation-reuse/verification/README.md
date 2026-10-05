# Local verification

`full-build-fixed.log` and `review-fix-full-build.log` each finish successfully
with 13929 jobs. The post-review source changes to Lean are docstrings only;
`runtime-equivalence.json` checks that both rebuilt benchmark executables are
byte-identical to the frozen measured After binaries.

`review-fix-wrapper-final.log` exercises the actual CI wrapper, including its
scoped abort-on-panic guard, with all 92 NumberField and 196 real-algebraic
checks passing in 55 seconds total. This is a two-executable local observation,
not whole-repository CI headroom. The first `review-fix-wrapper.log` lacks the
local PARI interpreter override and fails 12 external PARI cases; that setup
failure is retained, and the corrected run supplies the passing check.

`review-fix-admissions-final.log` records the ordinary-kernel admission scan:
354 roots, 1171 local modules, no admissions. The first post-review invocation
used an incorrect script path and did not run; its diagnostic is retained in
`review-fix-admissions.log`.

The final conformance and fixture/oracle logs predate the docstring edits and
retain their original scope. The rebuilt benchmark binaries are unchanged;
these checks are reused without a blanket timing or oracle rerun.
