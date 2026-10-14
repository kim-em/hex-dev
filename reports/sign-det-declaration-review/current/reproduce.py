"""Force a fresh compiled audit and compare its raw and derived artifacts."""
import json
import os
import subprocess
import tempfile
from pathlib import Path

from normalize import derive, require

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
MODULE = "HexSignDetMathlib.Diagnostics.DeclarationAudit"
AUDIT = ROOT / "conformance/HexSignDetMathlib/Diagnostics/DeclarationAudit.lean"


def main():
    require(not AUDIT.exists(), "temporary capture source already exists")
    with tempfile.TemporaryDirectory(prefix="signdet-audit-") as directory:
        output = Path(directory)
        AUDIT.write_bytes((BASE / "audit.lean.txt").read_bytes())
        try:
            for subtree in ("lib/lean", "ir"):
                folder = ROOT / ".lake/build" / subtree / "HexSignDetMathlib/Diagnostics"
                for artifact in folder.glob("DeclarationAudit.*"):
                    if artifact.is_file():
                        artifact.unlink()
            env = {**os.environ, "HEX_SIGNDET_AUDIT_OUTPUT": str(output)}
            subprocess.run(["lake", "build", "+" + MODULE], cwd=ROOT, env=env, check=True)
            for raw in ("declaration-use.json", "structure-fields.json", "audit-imports.json"):
                require((output / raw).is_file(), "capture did not write " + raw)
            derived = derive(output)
            for name, value in derived.items():
                (output / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
            names = set(derived) | {"audit-imports.json"}
            for name in sorted(names):
                require((output / name).read_bytes() == (BASE / name).read_bytes(),
                        "reproduction differs: " + name)
            print(f"Reproduced {len(names)} raw/derived JSON artifacts byte for byte.")
        finally:
            AUDIT.unlink()


if __name__ == "__main__":
    main()
