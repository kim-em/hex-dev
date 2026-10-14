# Current SignDet companion reference evidence

The capture resolves all 226 individually assessed declarations in 451 compiled
constants attributed to the 37 companion production modules. Its axiom union is
`propext`, `Classical.choice`, `Quot.sound`. All seventeen private helpers have
paths to handwritten public interfaces. Five structure fields are recorded from
Lean metadata. The existing declaration assessment covers their mathematical
meaning separately.

The import scan covers all 364 tracked production modules that transitively
reach a SignDet module root; no required module is absent from the capture.
Source roles distinguish production from tests, diagnostics, manual examples
and external dependencies. The imported environment contains 14,867 modules.
This checks import coverage, not runtime use or computational performance.

The graph merges known compiler aliases within the selected constants and
identifies 64 public declarations without a path to a production user outside
the companion. Their individual purposes are recorded in
[the disposition table](public-dispositions.md), using the existing assessment.
Twenty-eight have no direct compiled references at all. Every private helper
has a direct compiled reference. Anonymous examples, automation registrations,
external projects and aliases targeting unaudited modules remain outside the
reference model.

The earlier inventory at the parent report remains a retained snapshot. This
capture does not advance phase counters or establish complete core review.
The checkpoint binds 4,738 source inputs and nine report artifacts. A separate
compiled capture reproduced all six derived JSON artifacts byte for byte.
Final API/manual acceptance remains necessary before using this evidence as
a completed phase attestation.

## Reproduction and source checkpoint

`normalize.py --check` reconstructs the alias-merged graph, private paths and
production coverage using the existing Sturm audit helpers and source parser.
`check_bindings.py` checks exact checkpoint bytes, current reviewed module hashes,
axioms and the contiguous public-disposition table. The checkpoint binds all
tracked root-package Lean inputs, the audit tools, the assessment and the exact
lock/toolchain. External source bytes follow those pins. It does not establish
mathematical API quality or external-client completeness mechanically.

To reproduce the compiled capture in a separate output directory:

```sh
mkdir -p /tmp/signdet-audit-output
cp reports/sign-det-declaration-review/current/audit.lean.txt \
  conformance/HexSignDetMathlib/Diagnostics/DeclarationAudit.lean
HEX_SIGNDET_AUDIT_OUTPUT=/tmp/signdet-audit-output \
  lake build +HexSignDetMathlib.Diagnostics.DeclarationAudit
python3 reports/sign-det-declaration-review/current/normalize.py \
  --directory /tmp/signdet-audit-output
rm conformance/HexSignDetMathlib/Diagnostics/DeclarationAudit.lean
```

Compare the resulting six derived JSON artifacts with the committed ones.
Use the recorded source checkpoint and pinned dependencies. The check intentionally
refuses later source changes until a fresh compiled capture and manual assessment
justify re-attestation. The borrowed audit helper rejects optimized Python, so
run these tools without `-O` or `PYTHONOPTIMIZE`.
