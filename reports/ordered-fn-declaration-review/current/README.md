# OrderedFn compiler capture snapshot

The current compiler capture records 545 constants in fourteen production
modules: the five computational modules and nine companion modules, including
`HexOrderedFnMathlib.Sign`. Lean metadata records thirteen structure fields.
The transitive axiom union is `propext`, `Classical.choice`, `Quot.sound`;
none of the selected constants is an axiom declaration.

The producer imports the full manual, current API lint checks and the existing
infinitesimal examples. Its reference counts describe named constant types and
bodies in that environment. They do not establish production liveness:
anonymous examples, elaborator reductions and external clients can leave no
named edge, and evidence modules can supply references. Generated declarations
are included. The earlier 545-constant inventory and its 49 handwritten
zero-reference dispositions remain separate retained evidence.

The source comparison against the integrated declaration assessment shows only
the shared sign-lemma relocation/import changes and use of `Bounds.width_add`
in convergence. The two relocated statements and proofs are unchanged. The
existing individual assessments still apply; the current capture does not
supply a new assessment for every generated constant or establish Phase 6.

`bindings.json` records the exact imported root-package Lean source closure,
the assessments and the lock/toolchain bytes. The source tag
`audit/issue-10575-orderedfn-current-input-v3` preserves those inputs; the complete
tag `audit/issue-10575-orderedfn-current-complete-v3` preserves the report.
The default checker verifies source bytes at the recorded source tag and report
bytes in the current tree, including byte equality of every report file with
the complete archive tag. The recorded Lean input set must match the imported
local source closure at the input revision. `--current` additionally requires current source
bytes to match. Later source drift can preserve the archive while correctly
refusing a current attestation. Main has already changed two RootOrder sources
since this snapshot, so the archive passes there while `--current` refuses;
that conservative refusal is intentional. External source bytes follow the dependency pins. `check_capture.py` verifies those bindings, selected
module coverage, unique constant/field inventories and the axiom union. Run:

```sh
python3 reports/ordered-fn-declaration-review/current/check_capture.py
```

For reproduction, fetch both named tags and use an isolated checkout of the
complete tag with its pinned dependencies. To force a new capture, use a fresh directory, copy `audit.lean.txt` to the
otherwise absent `HexOrderedFnMathlib/UsageAudit.lean`, and remove only that
temporary module's `.lake/build/{lib/lean,ir}/HexOrderedFnMathlib/UsageAudit.*`
build artifacts. Set `HEX_ORDEREDFN_AUDIT_OUTPUT` to the fresh directory and
build `+HexOrderedFnMathlib.UsageAudit` through Lake. Refuse missing output files;
then remove the temporary source. Run `normalize.py <fresh-directory>` to sort declaration rows, reference and
axiom lists, field rows and JSON object keys into the recorded layout; compare
all three normalized JSON files with the archived report. The imported-module
list retains its captured ordering. The producer refuses
an absent output variable. A capture is an axiom inventory of the imported
compiled declarations, rather than a separate kernel replay of all oleans. The environment variable alone cannot invalidate
an unchanged Lake trace.

Final proof/API, production-reference and manual acceptance remains necessary.
The computational comparison findings are retained with their existing owners
and reports. This capture changes no operation, phase counter, performance
verdict or publication eligibility.

## Changes in references from the earlier snapshot

Six declarations with earlier zero-reference dispositions now have named
users. `Oracle.Bounds.width_add` is used by the changed convergence proof.
`Infinitesimal.sign_neg`, `sign_eq_zero_iff`, `sign_of_neg` and `sign_of_pos`
are used by the RealClosure specialization/coefficient-embedding production
modules added to the manual's import closure. `Infinitesimal.X_lt_pow` is used
by the newly included existing infinitesimal proof examples. These environment
changes explain five of the six new reference counts; they are separate from
source changes in OrderedFn. The earlier zero-reference table remains a
disposition of its recorded environment. The number of all captured constants
with no named users decreases from 107 to 101.
