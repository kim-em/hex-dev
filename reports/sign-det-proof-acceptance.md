# Sign-determination proof acceptance

HexSignDet and HexSignDetTheory satisfy the [Phase-5 criteria](../PLAN/Phase5.md):
complete proofs, a successful build on the pinned toolchain and passing existing
conformance. The core remains at Phase 5; the companion’s independent
[Theory acceptance](sign-det-declaration-review/theory-acceptance.md) records
its subsequent Phases 6–7. The owner Phase-4 attestation is merged in
[#10861](https://github.com/kim-em/hex-dev/pull/10861). Its
[performance report](sign-det-performance.md) and
[conformance report](sign-det-final-conformance.md) retain the independent
oracle evidence, source scope, computational findings and limits.
This proof acceptance does not advance Phases 6–7 or publication eligibility.

## Verification

The full monorepo build at source `42843589d50b707eecc5c336ad639ce1984c66a0`
with this documentation-only change passes on `leanprover/lean4:v4.35.0-rc3`. A focused build
passes both production libraries, `HexSignDetTheoryProofProbe`,
`HexSignDetTheoryDiagnostics` and every module under `conformance/HexSignDet/`
and `conformance/HexSignDetTheory/`, including the depth-three examples.
Run the focused build from the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess

targets = ["HexSignDet", "HexSignDetTheory", "HexSignDetTheoryProofProbe",
           "HexSignDetTheoryDiagnostics"]
for library in ("HexSignDet", "HexSignDetTheory"):
    for path in sorted((Path("conformance") / library).rglob("*.lean")):
        targets.append("+" + ".".join(path.relative_to("conformance").with_suffix("").parts))
subprocess.run(["lake", "build", *targets], check=True)
PY
```

Existing core `#guard` controls, finite matrix/support examples, producer and
arbitrary-replay proofs, selected-root contracts, noncanonical coefficients,
changed contexts and nested accepted/rejected evidence are reused.

The kernel axiom inventories retain only `propext`, `Classical.choice` and
`Quot.sound`. A source scan of both umbrellas, both production directories and
both conformance directories finds no admission tokens outside comments and
strings across 151 Lean files. The named-admission production import cones
also pass. The source scan is reproducible from the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
from scripts.ci.check_named_admissions import ADMISSION, code_only

paths = [Path("HexSignDet.lean"), Path("HexSignDetTheory.lean")]
for directory in ("HexSignDet", "HexSignDetTheory", "conformance/HexSignDet",
                  "conformance/HexSignDetTheory"):
    paths.extend(sorted(Path(directory).rglob("*.lean")))
for path in paths:
    assert not ADMISSION.search(code_only(path.read_text(encoding="utf-8"))), path
print(f"Admission scan: {len(paths)} files")
PY
```

The published trust scan applies to released prerequisites, rather than these
unreleased libraries.

Building fixture emitters does not run their emitted fixtures through an
external oracle. Executed full-suite evidence is the
[successful main CI run](https://github.com/kim-em/hex-dev/actions/runs/38055354782)
at owner source `112de5a94de8598e6a3fc8c2b48bbd09df1547c8`. Its conformance build
runs the field checks; its architecture step runs the in-process replay probe;
its oracle tail checks the emitted FLINT/Z3 and JSON-byte fixtures. The
Phase-5 counter change is documentation-only; its CI checks use the docs-only
path. The direct Sturm oracle and shared-helper changes select full CI. The SignDet-owned computational source, both conformance directories,
fixtures and dependency pins remain byte-identical to that owner source.
The shared exact-root Python helper is extracted without changing its functions;
the unchanged SignDet corpus and its refusal controls are rechecked alongside
the [direct Sturm oracle](sturm-direct-conformance/README.md). The companion proof/API polish has its separate assessment and
current kernel builds. The executed conformance/replay import cones have
unchanged upstream computational source; only ten companion proof modules
differ from the owner source. The field-check/replay executable stanzas and
the CI workflow (`.github/workflows/ci.yml`) are unchanged. Recheck the retained-source and companion-manifest
bindings from the repository root:

```sh
python3 - <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess

source = "112de5a94de8598e6a3fc8c2b48bbd09df1547c8"
paths = [Path("HexSignDet.lean"), Path("lake-manifest.json"), Path("lean-toolchain"),
         Path(".github/workflows/ci.yml")]
for directory in ("HexSignDet", "conformance/HexSignDet", "conformance/HexSignDetTheory"):
    paths.extend(sorted(Path(directory).rglob("*.lean")))
paths.extend(sorted(Path("conformance-fixtures/HexSignDet").glob("*.jsonl")))
paths.extend(Path("scripts/oracle") / name for name in ("common.py", "real_algebraic_qqbar.py"))
for path in paths:
    assert path.read_bytes() == subprocess.check_output(["git", "show", f"{source}:{path}"]), path
manifest = json.loads(Path("reports/sign-det-declaration-review/manifest.json").read_text(encoding="utf-8"))
for module in manifest["modules"]:
    assert hashlib.sha256(Path(module["path"]).read_bytes()).hexdigest() == module["reviewed_sha256"], module["path"]
print(f"Retained source: {len(paths)} files; companion manifest: {len(manifest['modules'])} modules")
PY
```

`python3 scripts/ci/check_named_admissions.py` checks the named production
import cones. The conformance suite also imports RationalFn and OrderedFn as
coefficient-field consumers. RationalFn's retained rollback concerned performance, not
a discovered wrong answer; current compiled conformance still passes.
The owner CI evidence and current shared-helper conformance remain separately
identified; this proof-completion change preserves every Lean
source and fixture. No new timing, oracle or benchmark implementation is added.

## Headline correctness and public API

`Hex.SignDet.determine_correct` is the headline theorem: every returned table
establishes the lawful domain and gives the exact count of roots for **every**
ordered sign word, including omitted conditions. It concerns the actual public
producer, not an assumed moment system. Its ordinary-kernel guard is in
[`Diagnostics/RootSemantics`](../conformance/HexSignDetTheory/Diagnostics/RootSemantics.lean).
The owning SPECs additionally justify arbitrary replay, descriptor validity,
completion, selected signs, root enumeration, comparison and transport as
independently useful public contracts. The
[companion correspondence table](../HexSignDetTheory/SPEC/hex-sign-det-theory.md#headline-correspondence-and-completeness)
maps these to actual public theorems; the computational SPEC's required
statement shapes have an explicit implemented-name mapping.

## Remaining work

The [Theory acceptance](sign-det-declaration-review/theory-acceptance.md)
completes the companion’s own proof/API and manual requirements. The separate
computational source assessments cover 728 named declarations. Final core
acceptance still requires its applicable computational regression check and
final API/use decisions; source review alone does not discharge those criteria.
Publication eligibility also remains separate.

The [computational comparison](bench-results/sign-det-phase6-comparison/README.md)
retains the stopped primary attempt and the complete two-workload interacting
pass. The primary runner exported complete successful rows below its timing
threshold, then returned 2; the collector stopped before the remaining blocks
and families. This consumed attempt is not eligible for the completed-inconclusive
rerun allowance. The collector correction preserves such exports for an
inconclusive native verdict, without changing the thresholds. A complete primary
comparison with adequate timing resolution remains required; no phase advances.

Upstream nested numeral construction is repaired in
[#10871](https://github.com/kim-em/hex-dev/pull/10871), closing
[#10863](https://github.com/kim-em/hex-dev/issues/10863) and restoring
HexRationalFn to Phase 4; its companion remained at 4. The
[nested-sign report](sign-det-nested-signs.md) retains the pre-repair
constructor-cost finding that motivated the
[#10864](https://github.com/kim-em/hex-dev/pull/10864) rollback;
the [constant-construction report](rationalfn-constants.md) retains the
separate repair comparisons. They do not establish the SignDet Phase-6
regression pass. Tower/tactic assembly and
all external distribution prerequisites remain with their owners and the
[publication plan](real-closure-publication.md).
