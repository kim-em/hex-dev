# Public replay-tree quotation evidence

This record pins the implementation at `e1c37242b659592b1a2c16c836cd844194c1f642`.
It retains successful public examples, fresh body audits, compatibility and
manual checks, six actually inspected desktop/narrow captures and unsuccessful
complete-packet diagnostics. The implementation has no dependency on debug
snapshots or stored unchecked expression data.

Run from the repository root:

```sh
python3 reports/data/hexrcf-tree-quotation/verify.py --check-head
```

`--check-head` also checks current source bytes. Without that flag the verifier
checks the pinned revision and retained artifacts. Hashes authenticate these
files, not mathematical claims; the fresh ordinary-kernel conformance modules
establish the stated reader equations. No complete source-goal acceptance or
algebraic completeness is claimed. See the [report](../../hexrcf-tree-quotation.md)
for scope and remaining work.
