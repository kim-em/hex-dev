# Current OrderedFn compiler capture

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

`bindings.json` records every tracked root-package Lean source, the
assessments and the lock/toolchain bytes. Later source drift causes this
current-source checker to refuse the snapshot. External source bytes follow
the recorded dependency pins. `check_capture.py` verifies those bindings, selected
module coverage, unique constant/field inventories and the axiom union. Run:

```sh
python3 reports/ordered-fn-declaration-review/current/check_capture.py
```

To force a new capture, use a fresh directory, copy `audit.lean.txt` to the
otherwise absent `HexOrderedFnMathlib/UsageAudit.lean`, and remove only that
temporary module's `.lake/build/{lib/lean,ir}/HexOrderedFnMathlib/UsageAudit.*`
build artifacts. Set `HEX_ORDEREDFN_AUDIT_OUTPUT` to the fresh directory and
build `+HexOrderedFnMathlib.UsageAudit` through Lake. Refuse missing output files;
then remove the temporary source. Sort declaration rows by module/name and
field rows by structure/field before comparing captures. The producer refuses
an absent output variable. The environment variable alone cannot invalidate
an unchanged Lake trace.

Final proof/API, production-reference and manual acceptance remains necessary.
The computational comparison findings are retained with their existing owners
and reports. This capture changes no operation, phase counter, performance
verdict or publication eligibility.
