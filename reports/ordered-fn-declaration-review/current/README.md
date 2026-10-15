# OrderedFn compiler capture snapshot

The capture inventories 545 constants attributed to fourteen production modules:
five computational modules and nine Theory modules. Lean metadata records
thirteen structure fields. The selected constants have exactly the axiom union
`propext`, `Classical.choice`, `Quot.sound`, with no owned axiom declaration.

The producer imports the manual, API lint checks, existing infinitesimal examples
and all 591 library clients selected from the root Lake configuration. This
includes libraries with source directories under `examples/`, `conformance/`,
`bench/` and `experiments/`, as well as root and adapter sources. Evidence clients
remain evidence; import coverage does not establish production liveness.

The source checker independently resolves library roots and globs from the pinned
`lakefile.lean`, using Lake's library-module rules. It walks reverse imports from
the fourteen production modules and requires exact agreement with the recorded
client set. It supports the literal arrays, concatenations, glob maps and the
explicit parked-conformance filter used by this configuration; unsupported
expressions are refused. The same computation on the live tree includes untracked Lean files and detects added
or removed clients in `--current` mode. Controls exercise the previously omitted
consumer, conformance, diagnostic and benchmark-support modules.

Four executable modules define conflicting `main` declarations and cannot share
one imported environment: `HexOrderedFnTheory.LiouvilleRun`,
`HexRealClosure.TowerTransportTests`, `HexRealClosure.TrivialTowerTests` and
`HexRCF.InverseFixture`. Their exclusions are derived from source and checked
against the record and imported-module list. A library client that imports one
of these executable modules is refused. Executable drivers outside the library
source sets are outside this coverage claim.

The producer's reference counts describe named constant types and bodies in this
imported environment. Anonymous examples, elaborator reductions and external
clients can leave no named edge. Tests can supply references, and generated
constants are included. The original declaration assessment and its 49
zero-reference dispositions remain separate retained evidence; counts alone do
not decide whether an API should remain public.

All fourteen owned source files match the preserved v4 files after the global
Mathlib-to-Theory module rename. This is a source-identity check, not a proof
that every imported dependency or elaborated type is identical. The checker also
compares declaration names, owning modules, kinds and axiom lists with the
renamed v4 capture. The individual source assessments remain applicable; final
API-use acceptance and the retained computational regression findings remain
open. No phase, performance verdict or publication eligibility advances here.

## Source and artifact checkpoints

The source tag is `audit/issue-10575-orderedfn-current-input-v7`; the complete tag
is `audit/issue-10575-orderedfn-current-complete-v7`. The binding record covers
the imported root-package Lean closure, the source assessments, audit tools,
the Lake block parser, toolchain and lock. Imported Hex modules must resolve to
one tracked path. External source bytes follow the pinned dependencies.

Fetch the source and complete tags, together with
`audit/issue-10575-orderedfn-current-input-v4` and
`audit/issue-10575-orderedfn-current-complete-v4` for the predecessor comparison.
Use an isolated checkout of the complete tag with its pinned dependencies:

```sh
python3 -I -B reports/ordered-fn-declaration-review/current/check_capture.py
python3 -I -B reports/ordered-fn-declaration-review/current/check_capture.py --current
python3 reports/ordered-fn-declaration-review/current/test_capture.py
```

The default checker verifies source bytes and coverage at the source tag, report
bytes against the complete tag, normalization, selected-module coverage, unique
constant/field inventories and the axiom union. `--current` additionally checks
live input bytes and library-client coverage. Later source changes can preserve
the archive while correctly refusing a current attestation. This inventories
imported compiled declarations; it does not independently replay every olean
through the kernel.

For reproduction, create a fresh output directory, copy `audit.lean.txt` to the
otherwise absent `HexOrderedFnTheory/UsageAudit.lean`, and remove only that
temporary module's `.lake/build/{lib/lean,ir}/HexOrderedFnTheory/UsageAudit.*`
artifacts. Set `HEX_ORDEREDFN_AUDIT_OUTPUT` to the fresh directory and build
`+HexOrderedFnTheory.UsageAudit` through Lake. Refuse missing outputs and remove
the temporary source afterwards. Run `normalize.py <fresh-directory>` and compare
all three JSON files with the archive. The import list retains its captured
ordering. An output variable alone does not invalidate an unchanged Lake trace.

The v4 tags preserve the earlier Mathlib-named capture. The v5 input and both
`complete-v5` and `complete-v5-context` tags preserve an incomplete library-client
capture; its omissions are corrected here. Those tags remain historical evidence
and do not establish the complete client-coverage claim above.

The capture imports 15,241 modules. 100 of the selected constants have no
named users in this environment. `RealClosureConsumer.successive_order` is
recorded as a user of both `Infinitesimal.X_pos` and `X_lt_pow`. These
observations retain the reference-model limits above.

Runtime executable consumers and independent Lake projects under `experiments/`
are outside this library-reference environment. No complete runtime-use census
is claimed. The four recorded `main` exclusions use the ordinary declaration
syntax in this source snapshot; their root-level placement was reviewed.
The client total includes the fourteen selected production modules themselves.
