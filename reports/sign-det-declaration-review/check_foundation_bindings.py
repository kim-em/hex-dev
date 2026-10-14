"""Check the current SignDet foundation and companion reviewed-source bindings."""
import hashlib
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    foundation = json.loads((BASE / "core-foundation-manifest.json").read_text())
    require(set(foundation["file_roles"]) == set(foundation["files"]), "unclassified binding")
    for path, expected in foundation["files"].items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path)
    for stem, expected_count in (("core-replay", 49), ("core-tables", 42), ("core-selected", 19), ("core-descriptors", 45)):
        record = json.loads((BASE / (stem + "-manifest.json")).read_text())
        require(set(record["file_roles"]) == set(record["files"]), "unclassified binding: " + stem)
        names = []
        for path, expected in record["files"].items():
            require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path)
        for path, expected_names in record["declarations"].items():
            actual = re.findall(
                r"(?m)^(?:@\[[^\n]+\]\s*)?(?:private\s+)?(?:theorem|def|structure|inductive)\s+([\w.?!']+)",
                (ROOT / path).read_text())
            require(actual == expected_names, "declaration inventory differs: " + path)
            names.extend(actual)
        require(len(names) == len(set(names)) == expected_count, "unexpected declarations: " + stem)
        entries = re.findall(r"^\| `([^`]+)` \|", (BASE / (stem + ".md")).read_text(), re.MULTILINE)
        require(len(entries) == len(set(entries)) and set(entries) == set(names), "incomplete assessment: " + stem)
    companion = json.loads((BASE / "manifest.json").read_text())
    for module in companion["modules"]:
        path = module["path"]
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == module["reviewed_sha256"], path)
    declarations = []
    for module in ("Matrix", "Support", "Reference", "SignOperands"):
        declarations.extend(re.findall(
            r"(?m)^(?:@\[[^\n]+\]\s*)?(?:private\s+)?(?:theorem|def|structure|inductive)\s+([\w.?!']+)",
            (ROOT / "HexSignDet" / (module + ".lean")).read_text()))
    assessed = re.findall(r"^\| `([^`]+)` \|", (BASE / "core-foundation.md").read_text(), re.MULTILINE)
    require(len(declarations) == len(set(declarations)) == 35, "unexpected foundation declarations")
    require(set(assessed) == set(declarations) | {"System equality instance"}, "incomplete foundation assessment")
    print(f"Checked {len(foundation['files'])} foundation inputs, {len(companion['modules'])} companion modules and 35+49+42+19+45 declaration assessments")


if __name__ == "__main__":
    main()
