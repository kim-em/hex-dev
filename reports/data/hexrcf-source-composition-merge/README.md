# Current-main source composition integration

The [parent record](../hexrcf-source-composition/README.md) retains the actual quoted proofs, fresh private-body audits, reviewed implementation and six inspected final manual captures. This record verifies the subsequent merge with current main. Of its167 bound sources, only `lakefile.lean` changes; all166 other adapter/proof/manual/owner bindings remain identical. Both parents' target registrations are retained, including the new trie conformance target. Existing immutable records keep their original source pins.

The same nine affected targets pass14,421 Lake jobs with cached artifacts reused in21.393seconds, peak1.4GiB/no swap. Ten repository checks including12DAG tests pass. These are compatibility observations, not a new numerical measurement or regenerated proof claim. All own Lean/Lake jobs remain serial under the32GiB/no-swap/two-thread cap.

Run `python3 reports/data/hexrcf-source-composition-merge/verify.py --check-head` for the current167bindings and full parent verification, or omit the flag for the immutable integration commit. Full #10358 remains open.
