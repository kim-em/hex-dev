# SignDet core declaration-use assessment

The retained source is `398f34c7f15ac4c7e9da1fff83ecbfc62eb69c72`, preserved by
`audit/issue-10575-sign-det-core-use-input-v1`. Its ordinary-kernel capture matches
all 728 individually assessed handwritten declarations in 58 core modules among
3,085 attributed constants. The 98 structure-field projections are recorded
separately. Every one of the 44 private helpers has a path through the
alias-merged graph to a handwritten public declaration. The owned constants'
axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.

The existing source-role and import helpers verify that all 377 tracked Hex
production modules transitively reaching either SignDet root are imported.
The environment contains 14,884 modules. This is production import coverage,
not a claim about runtime calls or external projects. Core modules are not
counted as external production roots; the Theory companion can be such a root.
Anonymous examples and compiler registrations need separate interpretation.

The [149 individual public decisions](public-dispositions.md) adopt the existing
mathematical source assessments. All 73 public declarations without direct
alias-merged named clients are theorems. No assessed handwritten executable
definition has zero direct named clients. Of the 149 declarations without a
production path outside the core, 109 are theorems, 35 definitions and five
inductive/structure declarations. A named client may itself be a proof or test;
these counts are not runtime-use or API-quality conclusions.

The decisions retain exact acceptance/refusal, literal data, finite sign
congruence and parser roundtrip interfaces without manufacturing clients.
In particular:

- `Values.toList_impl` is a proved `csimp` registration and `toListLoop` its
  replacement for the public reference conversion. The term graph does not
  model compiler registrations; no internal compiled caller is claimed here.
- `referencePrepared` and `words` supply the independent full-ternary reference
  calculation used by `Conformance.agrees` and the required reduced/full
  comparison. Production does not fall back to exponential reference solving.
- `Dependencies` keeps raw packets, structural guards, local typed readers and
  ordered results separate. It does not construct missing tower/tactic evidence.
- Diagnostic equality from `compare_ofError` is not selected-root equality.
  Byte-loop equality from `forIn_data` is not an allocation measurement.

The private paths and public judgments supplement the individual assessments;
counts and lint output do not replace those assessments. Anonymous instances
and field meaning retain the dispositions in the owning source-review groups.
This report does not classify every additional compiler constant as handwritten
API, complete the computational regression gate, advance a phase or establish
publication eligibility.

## Evidence and verification

The `.json.gz` files preserve the raw capture and derived graph. Their hashes,
the producer and analysis scripts, source inputs and helper versions are bound
in `bindings.json`. The producer reuses the companion audit body, selecting the
58 core modules and explicitly refusing a missing module. `derive.py` reuses
its namespace-aware source parser, role index, compiler-alias graph and import
parser. It verifies source matching before deriving the results. The capture
build completed 14,286 jobs; its temporary source was removed afterwards.
All installed Git dependencies matched the exact lock and had no tracked edits.

```sh
git fetch origin tag audit/issue-10575-sign-det-core-use-input-v1
python3 reports/sign-det-declaration-review/core-use/check_bindings.py
python3 reports/sign-det-declaration-review/core-use/check_bindings.py --current
python3 reports/sign-det-declaration-review/core-use/test_tools.py
```

Default mode checks the source checkpoint, helper bytes, saved artifacts and
public-decision inventory. Current mode additionally checks live source bytes
and recomputes the derived graph. Later source changes can preserve the archive
while correctly refusing a current-source claim. This is not a new capture of
the companion's preserved v10 evidence; that archive is unchanged.

To repeat the kernel capture, use an isolated worktree at the input tag with
its exact pinned dependencies. Copy `audit.lean.txt` into the temporary module
`conformance/HexSignDetTheory/Diagnostics/CoreUseAudit.lean`, set
`HEX_SIGNDET_AUDIT_OUTPUT` to an empty directory, and run
`lake build +HexSignDetTheory.Diagnostics.CoreUseAudit`. Remove the temporary
source afterwards. The three raw outputs are `declaration-use.json`,
`structure-fields.json` and `audit-imports.json`. Compare JSON rows after sorting
by name/module as appropriate; the imported module sequence retains its original
order. A successful cached build without new output is not a capture.

No new measurements were collected. The core remains at Phase 5; its applicable
computational baseline comparison and final phase acceptance remain separate.
