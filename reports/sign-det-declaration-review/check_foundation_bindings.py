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
    groups = (("core-replay", 49), ("core-tables", 42), ("core-selected", 19), ("core-descriptors", 45), ("core-completion", 17), ("core-comparison", 27), ("core-dag", 28), ("core-handles", 25))
    for stem, expected_count in groups:
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
            namespace = record.get("namespaces", {}).get(path, "Hex.SignDet")
            if "namespaces" in record:
                require(re.findall(r"(?m)^namespace ([\w.]+)$", (ROOT / path).read_text()) == [namespace],
                        "namespace differs: " + path)
            require(namespace == "Hex.SignDet" or namespace.startswith("Hex.SignDet."),
                    "namespace outside SignDet: " + path)
            prefix = namespace.removeprefix("Hex.SignDet").lstrip(".")
            names.extend((prefix + "." if prefix else "") + name for name in actual)
        require(len(names) == len(set(names)) == expected_count, "unexpected declarations: " + stem)
        entries = re.findall(r"^\| `([^`]+)` \|", (BASE / (stem + ".md")).read_text(), re.MULTILINE)
        require(len(entries) == len(set(entries)) and set(entries) == set(names), "incomplete assessment: " + stem)
    total = 35 + sum(count for _, count in groups)
    summary = re.search(r"assessments below cover (\d+) named declarations",
                        (BASE / "README.md").read_text())
    require(summary is not None and int(summary.group(1)) == total, "README review total differs")
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
    print(f"Checked {len(foundation['files'])} foundation inputs, {len(companion['modules'])} companion modules and {total} declaration assessments")


if __name__ == "__main__":
    main()
