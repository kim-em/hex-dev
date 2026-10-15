"""Force a fresh compiled audit and compare its raw and derived artifacts."""
import json
import importlib.util
import os
import subprocess
import tempfile
from pathlib import Path

from normalize import derive, require

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
MODULE = "HexSignDetTheory.Diagnostics.DeclarationAudit"
AUDIT = ROOT / "conformance/HexSignDetTheory/Diagnostics/DeclarationAudit.lean"


def load_checkpoint():
    """Load this audit's checkpoint helper without source-path import shadowing."""
    spec = importlib.util.spec_from_file_location('_hex_signdet_checkpoint', BASE / 'check_bindings.py')
    checkpoint = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checkpoint)
    return checkpoint


def verify_dependencies():
    """Require installed Git dependencies to match the lock without tracked edits."""
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        require(package['type'] == 'git', 'unhandled dependency kind: ' + package['name'])
        name = package['name'].removeprefix('«').removesuffix('»')
        path = ROOT / manifest.get('packagesDir', '.lake/packages') / name
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        require(head == package['rev'], 'dependency revision differs: ' + name)
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=path, text=True)
        require(not dirty, 'tracked dependency changes: ' + name)


def main():
    checkpoint = load_checkpoint()
    record = json.loads((BASE / 'bindings.json').read_text())
    checkpoint.verify_archive(record)
    verify_dependencies()
    require(checkpoint.inputs() == record['inputs'], 'reproduction source inputs differ from checkpoint')
    for path, expected in record['artifacts'].items():
        require(checkpoint.digest(ROOT / path) == expected, 'reproduction artifact differs: ' + path)
    require(not AUDIT.exists(), "temporary capture source already exists")
    with tempfile.TemporaryDirectory(prefix="signdet-audit-") as directory:
        output = Path(directory)
        AUDIT.write_bytes((BASE / "audit.lean.txt").read_bytes())
        try:
            for subtree in ("lib/lean", "ir"):
                folder = ROOT / ".lake/build" / subtree / "HexSignDetTheory/Diagnostics"
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
            require(checkpoint.inputs() == record['inputs'], 'source inputs changed during reproduction')
            verify_dependencies()
            print(f"Reproduced {len(names)} raw/derived JSON artifacts byte for byte.")
        finally:
            AUDIT.unlink()


if __name__ == "__main__":
    main()
