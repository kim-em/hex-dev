"""Recheck operation-window leaf attribution without executing archived code."""
from pathlib import Path
import gzip
import hashlib
import json
import re
from collections import Counter

DENSE = "lp_Hex_Fin_foldl_loop___at___00Vector_dotProductImpl___at___00Hex_Matrix_mulImpl___at___00Hex_SignDet_System_check_spec__3_spec__3_spec__6"
HEADER = re.compile(r"\s*(\d+)/(\d+)\s+(\d+)\.(\d{9}):\s+([0-9a-f]+)\s+(.*?)\s+\((.*)\)$")


def validate(directory, *, matrix_directory=None):
    directory = Path(directory)
    archive = json.loads((directory/"archive.json").read_text())
    if archive["schema"] != "hex-matrix-check-attribution-archive-v1":
        raise ValueError("unknown attribution archive")
    listed = {binding["stored"] for binding in archive["files"].values()} | {"archive.json"}
    if {str(p.relative_to(directory)) for p in directory.rglob("*") if p.is_file()} != listed:
        raise ValueError("missing or unlisted attribution file")
    raw = {}
    for name, binding in archive["files"].items():
        for path in (name, binding["stored"]):
            if Path(path).is_absolute() or ".." in Path(path).parts:
                raise ValueError("attribution path escapes archive")
        payload = (directory/binding["stored"]).read_bytes()
        if hashlib.sha256(payload).hexdigest() != binding["stored_sha256"]:
            raise ValueError("attribution stored bytes changed")
        data = gzip.decompress(payload) if binding["stored"].endswith(".gz") else payload
        if hashlib.sha256(data).hexdigest() != binding["sha256"]:
            raise ValueError("attribution raw bytes changed")
        raw[name] = data
    meta = json.loads(raw["metadata.json"])
    matrix = Path(matrix_directory) if matrix_directory is not None else directory.parents[1]/"sign-det-matrix-wide/6b977999bc-first"
    original = json.loads((matrix/"timing/metadata.json").read_text())
    if (meta["state"] != "complete" or meta["provenance_unchanged"] is not True or
            meta["revision"] != original["revision"] or
            any(original["source_sha256"].get(name) != digest
                for name, digest in meta["source_sha256"].items()) or
            set(meta["source_sha256"]) != set(original["source_sha256"]) - {
                "scripts/bench/test_sign_det_matrix_wide.py", "reports/sign-det-matrix-wide.md",
                "scripts/bench/sign_det_matrix_wide.py", "scripts/bench/sign_det_joint_timing.py",
                "scripts/bench/sign_det_compare.py"} or
            meta["binary_sha256"] != original["binary_sha256"] or
            hashlib.sha256(raw["collector.py"]).hexdigest() != meta["collector_sha256"] or
            [capture["parameter"] for capture in meta["captures"]] != [243, 729]):
        raise ValueError("profile source differs from retained checker")
    if DENSE not in raw["symbols.txt"].decode().split():
        raise ValueError("dense loop absent from measured symbol table")
    summaries = {}
    for capture in meta["captures"]:
        size = capture["parameter"]
        row = capture["profile_row"]
        region = capture["region"]
        if (row["status"] != "ok" or row["result_hash"] != "0xb" or
                row["profile_kernel"] is not True or row["param"] != size or
                row["inner_repeats"] != 1 or row["env"]["git_commit"] != meta["revision"] or
                row["env"]["git_dirty"] is not False or
                row["function"] != "Hex.SignDetBench.MaximalMatrix.runTensorCheck"):
            raise ValueError("wrong profile operation or answer")
        records = [json.loads(line) for line in raw[f"{size}/profile.log"].decode().splitlines()
                   if line.startswith("{")]
        if records != [row]:
            raise ValueError("profile metadata disagrees with raw result")
        sidecars = [name for name in raw if name.startswith(f"{size}/regions-")]
        if len(sidecars) != 1:
            raise ValueError("wrong operation-window count")
        header, window = map(json.loads, raw[sidecars[0]].decode().splitlines())
        if (window != region or window["count"] != 1 or window["label"] != "kernel" or
                header["clock_source"] != "CLOCK_MONOTONIC" or
                window["mono_t1_ns"]-window["mono_t0_ns"] != row["total_nanos"]):
            raise ValueError("wrong monotonic operation window")
        leaves = Counter()
        threads = Counter()
        for line in raw[f"{size}/perf-leaves.txt"].decode().splitlines():
            match = HEADER.fullmatch(line)
            if match is None:
                raise ValueError("unrecognized leaf sample")
            stamp = int(match[3])*10**9+int(match[4])
            if int(match[1]) == header["pid"] and region["mono_t0_ns"] <= stamp <= region["mono_t1_ns"]:
                leaves[match[6]] += 1
                threads[match[2]] += 1
        if not leaves or len(threads) != 1:
            raise ValueError("missing or multithreaded operation samples")
        summaries[str(size)] = {"samples": sum(leaves.values()), "dense_loop": leaves[DENSE],
                                "leaf_counts": dict(sorted(leaves.items()))}
    expected = json.loads(raw["summary.json"])
    if summaries != expected:
        raise ValueError("leaf summary disagrees with retained samples")
    return summaries


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    print(json.dumps(validate(args.directory), indent=2))
