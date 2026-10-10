# Sturm proof acceptance

HexSturm and HexSturmMathlib satisfy the [Phase-5 criteria](../PLAN/Phase5.md):
complete proofs, a successful build on the pinned toolchain and passing
conformance. Both counters are 5. The owner Phase-4 attestation is merged in
[#10860](https://github.com/kim-em/hex-dev/pull/10860); its
[readiness matrix](real-closure-prerequisites.md) and
[performance report](hex-sturm-performance.md) retain evidence and limits.
This acceptance does not advance Phases 6 or 7 or establish publication eligibility.

## Build and conformance

A full monorepo `lake build` passes on `leanprover/lean4:v4.35.0-rc3`.
The focused command also passes:

```sh
lake build HexSturm HexSturmMathlib HexSturmMathlibTests \
  +HexSturm.Conformance \
  +HexSturmMathlib.Tests.Replay.Semantics \
  +HexSturmMathlib.Tests.Replay.SemanticsBaseline
```

The computational conformance checks actual ordinary/prepared queries, root
counts, certificates, cached/plain replay, endpoint retargeting and positive
certificate transport through its Lean `#guard` suite. It includes constants, invalid domains, repeated heads,
noncanonical storage, changed literal bindings and corrupted evidence. Its
integer/field comparisons are differential controls; they do not replace the
ordinary-kernel semantic proofs or the shared integer owner's exact oracle.
The differential comparison reuses the integer Tarski implementation whose
fixtures are checked by the pinned
[HexRealRoots FLINT oracle](../scripts/oracle/realroots_flint.py).
This supplies inherited exact selected-root sign evidence for squarefree integer
heads at finite dyadic endpoints; it is not an
independent oracle for the Sturm-owned frontend. The readiness matrix's FLINT/Z3
comparisons are performance orientation, and its Z3 de Moura–Passmore check is
downstream consumer evidence. This focused suite runs no external oracle.
Sturm has no independently serialized oracle fixtures with its own seeds and
version provenance. This is an open deviation from both owning SPECs' oracle
choice, tracked by [#10575](https://github.com/kim-em/hex-dev/issues/10575) and the
[unresolved requirements](real-closure-requirements.md#unresolved-requirements-and-ownership).
Infinite endpoints, half-open counts and noncanonical storage are outside the
inherited FLINT fixture coverage. Integration acceptance requires discharging
that deviation; it is not assigned to the Phase-6 lint or Phase-7 manual checks.
This missing-evidence finding does not invalidate the passing attested Phase-3
suite or establish an implementation defect, so it does not trigger a rollback
under the [rollback rule](../PLAN/Conventions.md#rollback-is-a-normal-action).

The companion tests apply domain/query contracts to canonical and noninjective
coefficient storage and accepted/rejected literal replay. Semantic replay and
root-count guards build through the existing adapter test modules. Their axiom
inventories admit only `propext`, `Classical.choice` and `Quot.sound`.
The named-admission import cones cover the production modules and pass. A
separate source scan of both umbrellas and `HexSturm/`, `HexSturmMathlib/`,
`adapters/HexSturmMathlib/` and `conformance/HexSturm/` finds no admission tokens
outside comments and strings. Compiled kernel guards and that source scan
establish the absence of sorries, new axioms and `native_decide` in completed
production claims. The published trust scan checks released inputs; the Sturm
pair is unreleased and is not covered by that scan.

## Scope and remaining work

The [declaration assessment](sturm-declaration-review/README.md) covers the
48 computational and 78 companion handwritten production declarations.
All eleven reviewed production modules match the manifest's
`documented_sha256` values byte for byte. The source scan and manifest comparison
can be reproduced from the repository root:

```sh
python3 - <<'PY'
import hashlib
import json
from pathlib import Path
from scripts.ci.check_named_admissions import ADMISSION, code_only

paths = [Path("HexSturm.lean"), Path("HexSturmMathlib.lean")]
for directory in ("HexSturm", "HexSturmMathlib", "adapters/HexSturmMathlib",
                  "conformance/HexSturm"):
    paths.extend(sorted(Path(directory).rglob("*.lean")))
for path in paths:
    assert not ADMISSION.search(code_only(path.read_text(encoding="utf-8"))), path
manifest = json.loads(Path("reports/sturm-declaration-review/manifest.json").read_text(encoding="utf-8"))
for module in manifest["modules"]:
    assert hashlib.sha256(Path(module["path"]).read_bytes()).hexdigest() == module["documented_sha256"], module["path"]
print(f"Admission scan: {len(paths)} files; manifest: {len(manifest['modules'])} modules")
PY
```

Phase 5 requires proof completion rather than a new implementation or repeated
performance measurements. No Lean source changes accompany these counters.

Phase 6 still requires final lint/docstring/use acceptance and the computational
comparison against the prescribed committed benchmark baseline. The existing
[manual chapter](../HexManual/Chapters/HexSturm.lean) does not complete those checks.
The [publication plan](real-closure-publication.md) retains companion dependency
pins, split fixtures, candidate consumer checks and external distribution
requirements. Real-algebraic and rank Phases 5–7 remain outside this pair's scope.
