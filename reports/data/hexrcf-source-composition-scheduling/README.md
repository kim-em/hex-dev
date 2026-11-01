# Scheduling registration compatibility

The [parent integration record](../hexrcf-source-composition-merge/README.md) retains the source composition proof evidence and its original pins. This record verifies merge `0f27eb2275064438d30ba93c75a9075e9cafc098` with upstream Groebner scheduling. Among the167 bound sources only `lakefile.lean` changes; all166 other bindings remain identical. Every target from both parents is retained, including `HexGroebner.SchedulingConformance` and `HexGroebner.SchedulingResumeConformance`.

The same nine adapter, proof audit and manual targets plus those two new scheduling targets pass14,481 Lake jobs with cached artifacts reused in2min39.453s, peak1.7GiB/no swap. Ten repository checks including12DAG tests pass in33.136s. These are integration observations, not regenerated proof or numerical performance claims. All own builds remain serial under hard aggregate32GiB/no swap/two Lean threads.

Run `python3 reports/data/hexrcf-source-composition-scheduling/verify.py --check-head` to check the current167bindings, complete parent evidence chain, actual successful build/check logs and the union of registrations. Omit the flag for the immutable merge source. GitHub CI for the final pushed commit must pass before merge. Full #10358 remains incomplete.
