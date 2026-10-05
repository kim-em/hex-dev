"""Validate the frozen larger-range nested-table collection."""
from pathlib import Path
import gzip
import hashlib
import json
import os
import statistics
import subprocess
import tempfile
import types


ROOT = Path(__file__).resolve().parents[2]


def validate(directory, *, reconstruct=False):
    directory = Path(directory).resolve()
    manifest = json.loads((directory / "archive.json").read_text())
    digest = lambda data: hashlib.sha256(data).hexdigest()
    if manifest["unchanged_reruns"] != 0:
        raise ValueError("wrong wide collection rerun count")
    present = {str(p.relative_to(directory)) for p in directory.rglob("*") if p.is_file()}
    listed = {r["file"] for r in manifest["files"].values()}
    if present != listed | {"archive.json", "whole-source.patch", "collector.py"}:
        raise ValueError("missing or unlisted archive file")
    raw = {}
    for name, record in manifest["files"].items():
        path = Path(record["file"])
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("archive path escapes directory")
        stored = (directory / path).read_bytes()
        value = gzip.decompress(stored) if path.suffix == ".gz" else stored
        if digest(stored) != record["stored_sha256"] or digest(value) != record["sha256"]:
            raise ValueError("archive bytes changed: " + name)
        raw[name] = value
    meta = json.loads(raw["metadata.json"])
    if (meta["state"] != "complete" or meta["scientific_samples"] != 120 or
            meta["source_unchanged"] is not True or meta["git_status_after"] != "" or
            meta["revision"] != manifest["source_revision"] or
            meta["revision_after"] != meta["revision"] or
            meta["source_sha256_after"] != meta["source_sha256"] or
            meta["binary_sha256_after"] != meta["binary_sha256"] or
            meta["harness_binding_after"] != meta["harness_binding"] or
            meta["source_archive"]["base_revision"] != manifest["source_base"]):
        raise ValueError("incomplete or changed source, binary or harness")
    if set(raw) - {"metadata.json"} != set(meta["file_sha256"]):
        raise ValueError("missing original collection file")
    for name, expected in meta["file_sha256"].items():
        if digest(raw[name]) != expected:
            raise ValueError("original collection hash disagreement")
    patch = (directory / "whole-source.patch").read_bytes()
    if digest(patch) != manifest["whole_source_patch_sha256"]:
        raise ValueError("changed reconstruction patch")
    protocol = (directory / "collector.py").read_bytes()
    if (digest(protocol) != manifest["collector_sha256"] or
            digest(protocol) != meta["source_sha256"]["scripts/bench/sign_det_nested_tables.py"]):
        raise ValueError("historical collector hash disagreement")
    # Use the hash-bound declaration without writing bytecode into the archive.
    historical = types.ModuleType("nested_wide_capture_protocol")
    historical.__file__ = str(directory / "collector.py")
    exec(compile(protocol, historical.__file__, "exec"), historical.__dict__)
    observations = {}
    with tempfile.TemporaryDirectory() as temporary:
        temporary = Path(temporary)
        inputs = temporary / "inputs.stdout"
        inputs.write_bytes(raw["inputs.stdout"])
        expected = historical.validate_inputs(inputs)
        for depth in historical.DEPTHS:
            for operation in ("runProduce", "runTree"):
                name = operation + str(depth)
                path = temporary / (name + ".json")
                path.write_bytes(raw[name + ".json"])
                result = historical.validate_result(path, name, expected, meta["revision"])
                export = json.loads(raw[name + ".json"])["results"][0]
                observations[name] = dict(result)
                for key, field, scale in (("medians_ms", "per_call_nanos", 1e6),
                                          ("median_peak_rss_kb", "peak_rss_kb", 1)):
                    observations[name][key] = {str(size): statistics.median(
                        p[field] / scale for p in export["points"] if p["param"] == size)
                        for size in historical.SIZES}
    stated = json.loads(raw["summary.json"])
    if (stated["validation_errors"] != [] or
            stated["observations"] != {name: {k: row[k] for k in
                ("verdict", "slope", "complexity_formula", "advisories")}
                for name, row in observations.items()} or
            manifest["observations"] != observations):
        raise ValueError("summary disagrees with original points")
    if reconstruct:
        with tempfile.TemporaryDirectory() as temporary:
            objects = Path(temporary) / "objects"
            objects.mkdir()
            original = subprocess.check_output(
                ["git", "rev-parse", "--git-path", "objects"], cwd=ROOT, text=True).strip()
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary) / "index"),
                       GIT_OBJECT_DIRECTORY=str(objects),
                       GIT_ALTERNATE_OBJECT_DIRECTORIES=str((ROOT / original).resolve()))
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=ROOT, env=env)
            git("read-tree", manifest["source_base"])
            git("apply", "--cached", str(directory / "whole-source.patch"))
            tree = git("write-tree").decode().strip()
            if tree != manifest["source_tree"]:
                raise ValueError("reconstructed source tree mismatch")
            for name, expected in meta["source_sha256"].items():
                if digest(git("show", tree + ":" + name)) != expected:
                    raise ValueError("reconstructed source hash mismatch: " + name)
    return observations


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--reconstruct-source", action="store_true")
    args = parser.parse_args()
    print(json.dumps(validate(args.directory, reconstruct=args.reconstruct_source), indent=2))
