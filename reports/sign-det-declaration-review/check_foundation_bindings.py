"""Check the current SignDet foundation and companion reviewed-source bindings."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
FOUNDATION_COUNT = 35


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    foundation = json.loads((BASE / "core-foundation-manifest.json").read_text())
    require(set(foundation["file_roles"]) == set(foundation["files"]), "unclassified binding")
    for path, expected in foundation["files"].items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path)
    groups = (
        ("core-replay", 49), ("core-tables", 42), ("core-selected", 19),
        ("core-descriptors", 45), ("core-completion", 17), ("core-comparison", 27),
        ("core-dag", 28), ("core-root-list", 40), ("core-handles", 25),
        ("core-dag-support", 69), ("core-graph-codec", 28),
        ("core-codec-coefficients", 18), ("core-dependencies", 34),
        ("core-serialization", 147), ("core-parser", 105),
    )
    for stem, expected_count in groups:
        record = json.loads((BASE / (stem + "-manifest.json")).read_text())
        require(set(record["file_roles"]) == set(record["files"]), "unclassified binding: " + stem)
        names = []
        for path, expected in record["files"].items():
            require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path)
        require(("archive_files" in record) == ("input_revision" in record),
                "incomplete archive binding: " + stem)
        if "input_revision" in record:
            try:
                resolved = subprocess.check_output(
                    ["git", "rev-parse", "--verify", "--end-of-options", "refs/tags/" + record["source_ref"] + "^{commit}"],
                    cwd=ROOT, text=True, stderr=subprocess.PIPE).strip()
            except subprocess.CalledProcessError as error:
                raise ValueError("Missing review checkpoint; fetch " + record["source_ref"] +
                                 " from origin (see the review README)") from error
            require(resolved == record["input_revision"], "review source ref moved: " + stem)
            archive = record["archive_files"]
            expected_archive = set(record["declarations"]) | {
                str((BASE / (stem + ".md")).relative_to(ROOT))}
            require(set(archive) == expected_archive, "archive review scope differs: " + stem)
            for path, expected in archive.items():
                require(record["files"][path] == expected, "reviewed bytes differ: " + path)
                try:
                    archived = subprocess.check_output(["git", "show", resolved + ":" + path],
                                                       cwd=ROOT, stderr=subprocess.PIPE)
                except subprocess.CalledProcessError as error:
                    raise ValueError("Review checkpoint lacks " + path) from error
                require(hashlib.sha256(archived).hexdigest() == expected, "archive differs: " + path)
        qualified = {}
        if "qualified_declarations" in record:
            require(set(record["qualified_declarations"]) == set(record["declarations"]),
                    "unclassified declaration scopes: " + stem)
            program = """
import importlib.util,json,sys
from pathlib import Path
root=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location('sign_det_review_names',root/'reports/sign-det-declaration-review/current/normalize.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
print(json.dumps({path:module.source_names(root/path) for path in sys.argv[2:]}))
"""
            # Shared helpers require assertions: keep extraction in normal,
            # isolated Python even when this binding checker runs with -O.
            qualified = json.loads(subprocess.check_output(
                [sys.executable, "-I", "-B", "-c", program, str(ROOT), *record["declarations"]],
                text=True))
        for path, expected_names in record["declarations"].items():
            if qualified:
                actual = list(qualified[path])
                require(actual == expected_names, "declaration inventory differs: " + path)
                full_names = list(qualified[path].values())
                require(all(name.startswith("Hex.SignDet.") for name in full_names),
                        "declaration outside SignDet: " + path)
                actual_names = [name.removeprefix("Hex.SignDet.") for name in full_names]
                require(actual_names == record["qualified_declarations"][path],
                        "declaration scopes differ: " + path)
                names.extend(actual_names)
                continue
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
        if qualified:
            lines = (BASE / (stem + ".md")).read_text().splitlines()
            rows = [i for i, line in enumerate(lines) if line.startswith("| `")]
            require(rows == list(range(rows[0], rows[-1] + 1)), "disconnected assessment table: " + stem)
            require(all(re.fullmatch(r"\| `[^`]+` \| [^|]+ \|", lines[i]) for i in rows),
                    "malformed assessment row: " + stem)
            require(lines[rows[0] - 2:rows[0]] == ["| Declaration | Assessment |", "| --- | --- |"],
                    "assessment table header differs: " + stem)
    total = FOUNDATION_COUNT + sum(count for _, count in groups)
    summary = re.search(r"assessments below cover (\d+) named declarations",
                        (BASE / "README.md").read_text())
    require(summary is not None and int(summary.group(1)) == total, "README review total differs")
    companion = json.loads((BASE / "manifest.json").read_text())
    for module in companion["modules"]:
        path = module["path"]
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == module["reviewed_sha256"], path)
    companion_count = 0
    for module in companion['modules']:
        actual = re.findall(
            r"(?m)^(?:@\[[^\n]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|def|structure|inductive|opaque|abbrev)\s+([\w.?!']+)",
            (ROOT / module['path']).read_text())
        require(actual == module['handwritten_declarations'], 'companion inventory differs: ' + module['path'])
        companion_count += len(actual)
    require(companion_count == companion['declaration_count'], 'companion count differs')
    declarations = []
    for module in ("Matrix", "Support", "Reference", "SignOperands"):
        declarations.extend(re.findall(
            r"(?m)^(?:@\[[^\n]+\]\s*)?(?:private\s+)?(?:theorem|def|structure|inductive)\s+([\w.?!']+)",
            (ROOT / "HexSignDet" / (module + ".lean")).read_text()))
    assessed = re.findall(r"^\| `([^`]+)` \|", (BASE / "core-foundation.md").read_text(), re.MULTILINE)
    require(len(declarations) == len(set(declarations)) == FOUNDATION_COUNT, "unexpected foundation declarations")
    require(set(assessed) == set(declarations) | {"System equality instance"}, "incomplete foundation assessment")
    print(f"Checked {len(foundation['files'])} foundation inputs, {len(companion['modules'])} companion modules and {total} declaration assessments")


if __name__ == "__main__":
    main()
