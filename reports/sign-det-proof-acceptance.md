# Sign-determination proof acceptance

HexSignDet and HexSignDetMathlib satisfy the [Phase-5 criteria](../PLAN/Phase5.md):
complete proofs, a successful build on the pinned toolchain and passing existing
conformance. Both counters are 5. The owner Phase-4 attestation is merged in
[#10861](https://github.com/kim-em/hex-dev/pull/10861). Its
[performance report](sign-det-performance.md) and
[conformance report](sign-det-final-conformance.md) retain the independent
oracle evidence, source scope, computational findings and limits.
This proof acceptance does not advance Phases 6–7 or publication eligibility.

## Verification

The full monorepo build passes on `leanprover/lean4:v4.35.0-rc3`. A focused build
passes both production libraries, `HexSignDetMathlibProofProbe`,
`HexSignDetMathlibDiagnostics` and every module under `conformance/HexSignDet/`
and `conformance/HexSignDetMathlib/`, including the depth-three examples.
Run the focused build from the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess

targets = ["HexSignDet", "HexSignDetMathlib", "HexSignDetMathlibProofProbe",
           "HexSignDetMathlibDiagnostics"]
for library in ("HexSignDet", "HexSignDetMathlib"):
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

paths = [Path("HexSignDet.lean"), Path("HexSignDetMathlib.lean")]
for directory in ("HexSignDet", "HexSignDetMathlib", "conformance/HexSignDet",
                  "conformance/HexSignDetMathlib"):
    paths.extend(sorted(Path(directory).rglob("*.lean")))
for path in paths:
    assert not ADMISSION.search(code_only(path.read_text(encoding="utf-8"))), path
print(f"Admission scan: {len(paths)} files")
PY
```

The published trust scan applies to released prerequisites, rather than these
unreleased libraries.

Building fixture emitters does not run their emitted fixtures through an
external oracle. The independent FLINT/Z3 and byte-conformance evidence remains
bound to the owner report; this proof-completion change preserves every Lean
source and fixture. No new timing, oracle or benchmark implementation is added.

## Remaining work

The [companion assessment](sign-det-declaration-review/README.md) treats its
226 handwritten production declarations, retains compiled references and
axiom inventories, and disposes of its public zero-reference statements.
The computational core still needs its separate declaration assessment.
Phase 6 also needs final lint/docstring/use acceptance and the computational
comparison against the prescribed benchmark baseline. The built manual does
not complete the Phase-6 requirements or advance Phase 7.

Upstream nested numeral construction remains with
[#10863](https://github.com/kim-em/hex-dev/issues/10863), and the RationalFn
performance rollback is merged in
[#10864](https://github.com/kim-em/hex-dev/pull/10864). Those findings are retained
rather than converted into a new performance pass. Tower/tactic assembly and
all external distribution prerequisites remain with their owners and the
[publication plan](real-closure-publication.md).
