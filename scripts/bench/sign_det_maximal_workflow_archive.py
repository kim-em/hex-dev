"""Validate retained fixed observations and reconstruct their measured sources."""
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
from scripts.bench.sign_det_maximal_workflow import CASES, TRIALS, ROOT, validate_export
from scripts.bench.sign_det_maximal import validate_inventory


def validate(root):
    root = Path(root)
    manifest = json.loads((root / "archive.json").read_text())
    present = {p.name for p in root.iterdir() if p.is_file() and p.name != "archive.json"}
    if present != set(manifest):
        raise ValueError("missing or extra retained files")
    for name, digest in manifest.items():
        if Path(name).name != name or hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError("retained bytes changed")
    meta = json.loads((root / "metadata.json").read_text())
    if (meta["state"], meta["trials"], meta["cases"], meta["schedule"]) != (
            "complete", TRIALS, list(CASES), "trial-major"):
        raise ValueError("wrong completed collection")
    inputs = validate_inventory(root / "inventory.jsonl")
    bindings = [json.loads(s) for s in (root / "hashes.jsonl").read_text().splitlines()]
    if [b["queries"] for b in bindings] != [1, 2, 3] or any(
            b["inputHash"] != i["inputHash"] for b, i in zip(bindings, inputs, strict=True)):
        raise ValueError("wrong input bindings")
    commands = [json.loads(s) for s in (root / "commands.jsonl").read_text().splitlines()]
    if [(r["trial"], r["case"]) for r in commands] != [
            (t, c) for t in range(TRIALS) for c in CASES]:
        raise ValueError("missing or reordered observations")
    observations = {case: [] for case in CASES}
    for r in commands:
        if r["exit_code"] != 0 or r["export"] != f'{r["trial"]}-{r["case"]}.json':
            raise ValueError("wrong retained export")
        binding = bindings[CASES.index(r["case"])]
        observations[r["case"]].append(validate_export(
            root / r["export"], r["case"], binding["expectedHash"], meta["revision"]))
    if observations != meta["observations"] or meta["median_nanos"] != {
            k: statistics.median(v) for k, v in observations.items()}:
        raise ValueError("summary disagrees with raw exports")
    source = meta["source_archive"]
    base = source["base_revision"]
    if len(base) != 40 or any(c not in "0123456789abcdef" for c in base):
        raise ValueError("invalid source base")
    subprocess.run(["git", "merge-base", "--is-ancestor", base, "origin/main"], cwd=ROOT, check=True)
    patch = (root / "committed-source.patch").read_bytes()
    if hashlib.sha256(patch).hexdigest() != source["sha256"]:
        raise ValueError("source patch hash mismatch")
    with tempfile.TemporaryDirectory() as temporary:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary) / "index"))
        subprocess.run(["git", "read-tree", base], cwd=ROOT, env=env, check=True)
        subprocess.run(["git", "apply", "--cached", "--unidiff-zero"], input=patch, cwd=ROOT, env=env, check=True)
        for name, digest in meta["source_sha256"].items():
            blob = subprocess.check_output(["git", "show", ":" + name], cwd=ROOT, env=env)
            if hashlib.sha256(blob).hexdigest() != digest:
                raise ValueError("measured source does not reconstruct: " + name)
    return meta["median_nanos"]


if __name__ == "__main__":
    print(validate(ROOT / "reports/data/sign-det-maximal/workflow-9c6565e68e"))
