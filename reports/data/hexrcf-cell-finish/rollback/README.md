# Joint late-exhaustion rollback

Run `python3 reports/data/hexrcf-cell-finish/rollback/verify.py --check-head`.
This supplement binds the current 108 sources to test-only commit
`111ce080624edf549479112ea69c5e176e630c50`, preserving the parent record's
source pin and artifacts.

The same action succeeds at 448,469 proof nodes. At limit 448,468, quotation
has already completed and created fresh declarations; source finishing consumes
448,274 nodes and requests 195 more. It exhausts, then restores every checked
metavariable field and the complete caller declaration list. The regression
asserts that fresh quotation declarations existed before failure, so rollback
is not vacuous.

The targeted build and fresh importing audit pass in 33.282s, peak 1.1 GiB/no
swap, under the unchanged serial 32 GiB wrapper. The audit remains 163 theorem
bodies/43 definitions/170 nonempty traces, with the same producer exclusions
and complete standard-three axiom closure. Header, line, admission and diff
checks pass. No production code, theorem statement, API or manual changed;
the parent's 47-target/manual validation is retained, not rerun or repinned.

This closes one composition-regression gap. The full #10358 implementation
and evidence requirements remain incomplete.
