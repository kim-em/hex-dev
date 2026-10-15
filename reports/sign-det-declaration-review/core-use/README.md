# SignDet core declaration-use assessment

The retained computational source is `398f34c7f15ac4c7e9da1fff83ecbfc62eb69c72`,
preserved by `audit/issue-10575-sign-det-core-use-input-v1`. The scoped kernel
capture matches the individually assessed source declarations, records structure
projections separately, and traces every private helper to a handwritten public
interface. Its owned-constant axiom union is exactly `propext`, `Classical.choice`,
`Quot.sound`. All additional attributed constants have an explicit retained
inventory; this is not a proof of compiler provenance from their names.

## Captured counts

| Quantity | Count |
| --- | ---: |
| Core modules | 58 |
| Attributed constants | 3,085 |
| Handwritten declarations | 728 |
| Structure fields | 98 |
| Private helpers | 44 |
| Private helpers without a public path | 0 |
| Required production import consumers | 377 |
| Selected evidence modules | 120 |
| Excluded executable entry points | 14 |
| Imported environment modules | 15,028 |
| Public declarations without an external-core production path | 149 |
| Public declarations without direct named clients | 60 |
| Outside-path theorems | 109 |
| Outside-path definitions | 35 |
| Outside-path inductive or structure declarations | 5 |
| Open API or integration decisions | 30 |

## Scope and API judgments

The source-role and import helpers cover every tracked Hex production module
transitively reaching either SignDet root. Core modules are not external
production roots; the Theory companion can be one. Evidence selection is explicit
in [evidence-scope.json](evidence-scope.json): core conformance, benchmark support,
selected-root tests, real-closure conformance and KernelReplay examples.
The excluded executable modules can contain named helper declarations too; those
helpers and their uses remain outside this term inventory. FieldChecks is a
standalone executable whose source Lake does not resolve as a library import.
Its separately built native checks remain available. No complete inventory of
all evidence clients, runtime calls or external projects is claimed.

The [individual API dispositions](public-dispositions.md) supplement the existing
mathematical assessments. They give distinct reasons for keeping characterizations,
finite sign congruence, parser roundtrips, literal transports and reference checks.
All no-direct-client public entries in this capture are theorems. No assessed
handwritten executable definition has zero direct named clients. A client may be
a proof or test, so that observation does not establish runtime usefulness.
Anonymous examples, compiler registrations and production metaprograms quoting
names are outside the term-reference model.

`Values.toList_impl` is a proved compiler-simplification registration and
`toListLoop` its replacement for the public reference conversion; no internal
compiled caller is asserted. `referencePrepared` and `words` supply the independent
full-ternary comparison used by the captured `Conformance.agrees`.
`Codec.bindings_iff` is used by the named `FastCheck.graph_roundtrip` theorem.
Diagnostic `compare_ofError` equality is not selected-root equality;
`forIn_data` proves iteration correspondence without an allocation claim.

The open dependency-envelope rows describe one unresolved integration requirement:
[the owning SPEC's cross-level dependency DAG](../../../HexSignDet/SPEC/hex-sign-det.md).
`Dependencies` supplies raw packets, structural guards, typed local readers and
ordered results. At this checkpoint, production tower/tactic code does not use this envelope;
its conformance reader examples do not supply automatic reached-data/all-live
assembly or semantic reader provenance. [#10378](https://github.com/kim-em/hex-dev/issues/10378)
and [#10358](https://github.com/kim-em/hex-dev/issues/10358) retain that implementation
ownership. This assessment keeps the existing APIs and makes the unconnected
production path explicit, rather than introducing another implementation.

Anonymous instances and field meaning retain the dispositions in the owning
source-review groups. Counts, paths and lints do not replace those judgments.
This report changes no algorithm, certificate contract or phase counter, and
supplies no computational regression or publication acceptance.

## Verification and reproduction

Compressed JSON preserves the raw capture and derived graph. `bindings.json`
binds the source checkpoint, helper versions, producer, tools, artifacts and
individual dispositions. The producer reuses the companion audit body with the
core module selection and the additional evidence imports. `derive.py` reuses
its source parser, role index, compiler-alias graph and import parser. It refuses
unaccounted constants, unsupported source declaration forms, unreviewed module
selections, private helpers without public paths and missing selected evidence.
Existing experiments can emit diagnostic results while building; that output
carries no computational performance attestation.

```sh
git fetch origin tag audit/issue-10575-sign-det-core-use-input-v1
python3 reports/sign-det-declaration-review/core-use/check_bindings.py
python3 reports/sign-det-declaration-review/core-use/check_bindings.py --current
python3 reports/sign-det-declaration-review/core-use/test_tools.py
```

Default mode checks checkpoint bytes, artifacts, per-section decisions and the
counts above. Current mode also requires matching live source and helper bytes,
then derives fresh output from raw inputs. It never seeds derived output with
archived answers. The checkpoint deliberately binds the whole root Lean input
set: later source changes preserve the archive but can refuse current mode.
The companion's earlier v10 archive remains unchanged.
Current-source controls in `test_tools.py` skip explicitly when live inputs have
moved; run the isolated-checkout procedure below to exercise those controls.

To reproduce after the source has moved, create an isolated checkout at the
input tag and copy this report directory into it. Its Python, Markdown, compressed
data and `.txt` producer add no tracked Lean input. From the current checkout:

```sh
git worktree add /tmp/signdet-core-use audit/issue-10575-sign-det-core-use-input-v1
cp -R reports/sign-det-declaration-review/core-use \
  /tmp/signdet-core-use/reports/sign-det-declaration-review/
cd /tmp/signdet-core-use
# Install the exact locked dependencies before indexing their source roots.
lake env lean --print-prefix
python3 reports/sign-det-declaration-review/core-use/check_bindings.py --current
```

That recomputes the graph from saved raw output. To repeat the kernel capture,
install the exact locked dependencies using the usual repository setup, copy
`audit.lean.txt` to
`conformance/HexSignDetTheory/Diagnostics/CoreUseAudit.lean`, and set
`HEX_SIGNDET_AUDIT_OUTPUT` to an empty directory. Run
`lake build +HexSignDetTheory.Diagnostics.CoreUseAudit`, then remove the temporary
source. The raw outputs are `declaration-use.json`, `structure-fields.json` and
`audit-imports.json`. Compare constant/field rows after sorting by name/module;
retain the imported-module sequence in its original order. Cached success without
new output is not a capture. No new timing campaign was run. The computational
baseline comparison and final phase acceptance remain separate requirements.
