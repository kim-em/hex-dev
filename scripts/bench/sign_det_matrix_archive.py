"""Validate both frozen-source wide matrix collections and the overlap record."""
from pathlib import Path
import hashlib
import types
import json
import os
import statistics
import subprocess
import tempfile
from scripts.bench import sign_det_matrix_wide as bench


def validate(directory, *, reconstruct=False):
    directory = Path(directory).resolve()
    manifest = json.loads((directory/"archive.json").read_text())
    digest = lambda data: hashlib.sha256(data).hexdigest()
    if manifest["unchanged_reruns"] != 1:
        raise ValueError("wrong matrix rerun count")
    present = {str(p.relative_to(directory)) for p in directory.rglob("*")
               if p.is_file() and p != directory/"archive.json"}
    if present != set(manifest["files_sha256"]):
        raise ValueError("missing or unlisted matrix archive file")
    for name, expected_hash in manifest["files_sha256"].items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("matrix archive path escapes directory")
        if digest((directory/relative).read_bytes()) != expected_hash:
            raise ValueError("matrix archive bytes changed: "+name)
    # The hash-bound historical declaration governs these frozen records.
    protocol_path = directory/"collectors/scripts/bench/sign_det_matrix_wide.py"
    historical = types.ModuleType("matrix_capture_protocol")
    historical.__file__ = str(protocol_path)
    # Execute the already hash-checked source without creating cache files
    # inside the immutable archive.
    exec(compile(protocol_path.read_bytes(), str(protocol_path), "exec"), historical.__dict__)
    identities, sources, summaries = [], [], []
    for label, summary_file in (("timing", "derived-summary.json"),
                                ("unchanged-rerun", "derived-rerun-summary.json")):
        capture = directory/label
        meta = json.loads((capture/"metadata.json").read_text())
        if (meta["state"] != "complete" or meta["scientific_samples"] != 24 or
                meta["revision"] != manifest["source_revision"] or
                meta["source_sha256"] != meta["source_sha256_after"] or
                meta["source_archive"]["base_revision"] != manifest["source_base"]):
            raise ValueError("matrix collection incomplete or changed source")
        for name, expected_hash in meta["file_sha256"].items():
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("matrix capture path escapes directory")
            if digest((capture/relative).read_bytes()) != expected_hash:
                raise ValueError("matrix capture hash disagreement")
        expected = historical.validate_inputs(capture/"inputs.stdout")
        verdict = historical.validate_result(capture/"timings.json", expected, meta["revision"])
        result = json.loads((capture/"timings.json").read_text())["results"][0]
        inventory = {row["matrixSize"]: row for row in map(json.loads,
                     (capture/"inputs.stdout").read_text().splitlines())}
        summary = {"verdict": verdict["verdict"], "slope": verdict["slope"], "rows": [
            {"dimension": size, "inverse_bits": inventory[size]["inverseBits"],
             "denominator_bits": inventory[size]["denominatorBits"],
             "median_seconds": statistics.median(point["per_call_nanos"]/1e9
                 for point in result["points"] if point["param"] == size),
             "median_peak_rss_kb": statistics.median(point["peak_rss_kb"]
                 for point in result["points"] if point["param"] == size)}
            for size in historical.PARAMS]}
        if json.loads((directory/summary_file).read_text()) != summary:
            raise ValueError("matrix summary disagrees with raw points")
        identities.append((meta["revision"], meta["binary_sha256"], meta["harness_binding"],
                           meta["source_sha256"]))
        sources.append(meta["source_sha256"])
        summaries.append(summary)
    if identities[0] != identities[1]:
        raise ValueError("matrix rerun changed source, binary or harness")
    overlap = directory/"overlap"
    meta = json.loads((overlap/"metadata.json").read_text())
    if (meta["state"] != "complete" or meta["scientific_samples"] != 0 or
            meta["revision"] != manifest["source_revision"] or
            meta["revision_after"] != meta["revision"] or
            meta["tree"] != manifest["source_tree"] or
            meta["base"] != manifest["source_base"] or
            meta["source_clean_before"] is not True or meta["source_clean_after"] is not True or
            meta["binary_sha256"]["hexsigndet_bench"] != identities[0][1] or
            meta["binary_sha256_after"] != meta["binary_sha256"]):
        raise ValueError("matrix overlap does not bind the measured binary")
    for name, expected_hash in meta["file_sha256"].items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("overlap capture path escapes directory")
        if digest((overlap/relative).read_bytes()) != expected_hash:
            raise ValueError("matrix overlap hash disagreement")
    overlap_lines = [f"tensor matrix {3**s}: complete witness matches ordinary solve"
                     for s in range(7)]
    if (overlap/"overlap.stdout").read_text().splitlines() != overlap_lines:
        raise ValueError("missing or changed tensor/ordinary-solver comparison")
    for name in ("scripts/bench/sign_det_matrix_wide.py", "scripts/bench/test_sign_det_matrix_wide.py"):
        if digest((directory/"collectors"/name).read_bytes()) != sources[0][name]:
            raise ValueError("archived matrix collector hash disagreement")
    if reconstruct:
        with tempfile.TemporaryDirectory() as temporary:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary)/"index"))
            def git(*arguments):
                return subprocess.check_output(["git", *arguments], cwd=bench.ROOT, env=env)
            git("read-tree", manifest["source_base"])
            git("apply", "--cached", "--unidiff-zero", str(directory/"whole-source.patch"))
            tree = git("write-tree").decode().strip()
            if tree != manifest["source_tree"]:
                raise ValueError("matrix reconstructed tree mismatch")
            for name, expected_hash in sources[0].items():
                if digest(git("show", tree+":"+name)) != expected_hash:
                    raise ValueError("matrix reconstructed source mismatch: "+name)
    return summaries


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--reconstruct-source", action="store_true")
    args = parser.parse_args()
    print(json.dumps(validate(args.directory, reconstruct=args.reconstruct_source), indent=2))
