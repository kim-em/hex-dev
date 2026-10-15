# OrderedFn compiler capture snapshot

The current compiler capture records 545 constants in fourteen production
modules: the five computational modules and nine companion modules, including
`HexOrderedFnTheory.Sign`. Lean metadata records thirteen structure fields.
The transitive axiom union is `propext`, `Classical.choice`, `Quot.sound`;
none of the selected constants is an axiom declaration.

The producer imports the full manual, API lint checks, infinitesimal examples
and every tracked client in the root or adapter libraries that transitively imports one of the
fourteen production modules. Explicit imports include evidence clients;
reference counts do not promote those clients to production. Separate
benchmark and conformance sub-projects, executable entry points and their
importers are outside this single-environment import-coverage claim. Executable
modules can define conflicting root `main` declarations. Its reference counts describe named constant types and
bodies in that environment. They do not establish production liveness:
anonymous examples, elaborator reductions and external clients can leave no
named edge, and evidence modules can supply references. Generated declarations
are included. The earlier 545-constant inventory and its 49 handwritten
zero-reference dispositions remain separate retained evidence.

The fourteen owned modules are byte-identical to the v4 source checkpoint
after applying the Mathlib-to-Theory module rename. The existing assessment
already covers the shared sign-lemma relocation and use of `Bounds.width_add`
in convergence. The rename changes no proof statement or executable body. The
existing individual assessments still apply; the current capture does not
supply a new assessment for every generated constant or establish Phase 6.

`bindings.json` records the exact imported root-package Lean source closure,
the assessments and the lock/toolchain bytes. The source tag
`audit/issue-10575-orderedfn-current-input-v5` preserves those inputs; the complete
tag `audit/issue-10575-orderedfn-current-complete-v5` preserves the report.
The default checker verifies source bytes at the recorded source tag and report
bytes in the current tree, including byte equality of every report file with
the complete archive tag. The recorded Lean input set must match the imported
local source closure at the input revision. Every imported Hex module must
resolve to exactly one tracked path, and the package/lock/toolchain inputs
are required explicitly. This checks the capture-reported imported module list;
it does not independently reconstruct Lean imports. `--current` additionally requires current source
bytes to match. Later source drift can preserve the archive while correctly
refusing a current attestation. The current snapshot uses the Theory import names; the earlier Mathlib-named
capture remains available at its v4 checkpoint. External source bytes follow the dependency pins. `check_capture.py` verifies those bindings, selected
module coverage, unique constant/field inventories and the axiom union. Run:

```sh
python3 -I -B reports/ordered-fn-declaration-review/current/check_capture.py
```

For reproduction, fetch both named tags and use an isolated checkout of the
complete tag with its pinned dependencies. To force a new capture, use a fresh directory, copy `audit.lean.txt` to the
otherwise absent `HexOrderedFnTheory/UsageAudit.lean`, and remove only that
temporary module's `.lake/build/{lib/lean,ir}/HexOrderedFnTheory/UsageAudit.*`
build artifacts. Set `HEX_ORDEREDFN_AUDIT_OUTPUT` to the fresh directory and
build `+HexOrderedFnTheory.UsageAudit` through Lake. Refuse missing output files;
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

## Retained evidence

The v4 source and complete tags preserve the earlier import environment,
reference counts and explanation of six changed references from the original
assessment. Current counts are observations of the current capture. Neither
snapshot establishes runtime use or computational performance.

The imported environment contains 14,908 modules. The 336 required
library clients are listed in the binding record and are all present. The
checker verifies that coverage list and the exact rename-only comparison of
all fourteen owned modules with the preserved v4 source. It does not
independently reconstruct the entire import graph.

The three omitted executable modules are `HexOrderedFnTheory.LiouvilleRun`,
`HexRealClosure.TowerTransportTests` and `HexRealClosure.TrivialTowerTests`.
The number of selected constants without named users is 101. These counts
include generated declarations and retain the reference-model limits above.
