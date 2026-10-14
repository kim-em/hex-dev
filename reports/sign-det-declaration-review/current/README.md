# Current SignDet companion reference evidence

The capture resolves all 226 individually assessed declarations in 451 compiled
constants attributed to the 37 companion production modules. Its axiom union is
`propext`, `Classical.choice`, `Quot.sound`. All seventeen private helpers have
paths to handwritten public interfaces. Five structure fields are recorded from
Lean metadata. The existing declaration assessment covers their mathematical
meaning separately.

The import scan covers all 364 tracked Hex production modules that transitively
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
The checkpoint binds the root-package source inputs and report artifacts
listed in `bindings.json`. Reproduction compares all nine raw/derived JSON artifacts, including the
imported module list and supplementary qualified-name references. The two
Markdown disposition tables remain manual assessments; their inventories,
reference counts and cited declaration bindings are checked.
Final API/manual acceptance remains necessary before using this evidence as
a completed phase attestation.

## Reproduction and source checkpoint

`normalize.py --check` reconstructs the alias-merged graph, private paths and
production coverage using the existing Sturm audit helpers and source parser.
`check_bindings.py` checks exact checkpoint bytes, axioms and the contiguous
public-disposition table. Its `--current` mode also checks reviewed module hashes
and the live source inputs. The checkpoint binds all
tracked root-package Lean inputs, the audit tools, the assessment and the exact
lock/toolchain. External source bytes follow those pins. It does not establish
mathematical API quality or external-client completeness mechanically.

The source checkpoint tag is
`audit/issue-10575-sign-det-current-reviewed-input-v2`. The complete archive is
`audit/issue-10575-sign-det-current-reviewed-complete-v2`. Fetch both tags and
use an isolated checkout at the complete archive:

```sh
git fetch origin tag audit/issue-10575-sign-det-current-reviewed-input-v2
git fetch origin tag audit/issue-10575-sign-det-current-reviewed-complete-v2
git worktree add /tmp/signdet-audit-source \
  audit/issue-10575-sign-det-current-reviewed-complete-v2
```

Build with the exact pinned dependencies, then run `reproduce.py` from that
checkout after `check_bindings.py --current` passes. Reproduction requires
exact agreement with the bound input and artifact hashes. It uses a fresh temporary directory, removes only the temporary
audit module's build artifacts, forces compilation and refuses missing outputs.
It compares all nine raw/derived JSON artifacts before removing the temporary
source. An unchanged Lake trace cannot stand in for a fresh capture.

The default `check_bindings.py` mode verifies checkpoint integrity: source
bytes from the tag and report bytes in the current tree. `--current` additionally
checks live source currency and recomputes the graph. Later source changes can
leave the archive intact while correctly refusing a current attestation.
New source/use evidence requires a fresh capture and manual review.
The borrowed audit helper rejects optimized Python, so
run these tools without `-O` or `PYTHONOPTIMIZE`.

## Additional constants and fields

The 451 attributed constants are completely partitioned into 226 source
manifest declarations, five field projections and 220 additional constants.
The [additional-constant inventory](generated-origins.json) records recognized
compiler naming conventions and Lean constant kinds. Unmatched extras and
source declarations missing from the manifest are refused. Naming conventions
are not proof of compiler provenance.

The [field dispositions](field-dispositions.md) include the unused direct-count
projection. The [supplementary lexical references](source-references.json)
distinguish existing manual, SPEC and axiom-audit mentions from term references.
Rows without either kind of client state an explicit public API retention
decision rather than claiming an example exists.
