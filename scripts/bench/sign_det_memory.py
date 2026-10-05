#!/usr/bin/env python3
"""Retain whole-child memory profiles; these are not scientific timing samples."""
from __future__ import annotations

import argparse
import hashlib
import gzip
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_joint_timing import harness_binding
from scripts.bench.sign_det_sparse import inventory_hashes
from scripts.bench.sign_det_joint import validate as validate_joint
from scripts.bench.sign_det_maximal_matrix import validate_inventory as validate_matrix
from scripts.bench.sign_det_height import validate_phases as validate_height

# Fixed before collection; all are parameters of the existing registrations.
GROUPS = {
    "sparse": ([64, 256, 1024], ["runProduce", "runTree", "runGraph"]),
    "joint": ([3, 7, 15], ["Joint.runComparison", "Joint.runCheckReduced"]),
    "matrix": ([9, 27, 81], ["MaximalMatrix.runSolveDimension", "MaximalMatrix.runCheckDimension"]),
    "height": ([8192, 65536, 524288], ["Height.runReduce", "Height.runCheck"]),
}
TRIALS = 3
SCOPE = ("whole child, including preparation, runtime initialization and result consumption; "
         "native VmHWM is peak resident memory; Massif page mode includes allocator reserves "
         "and executable/stack mappings; neither is live Lean-object memory")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def child_record(text, function, parameter, revision):
    rows = [json.loads(line) for line in text.splitlines() if line.startswith("{")]
    if len(rows) != 1:
        raise ValueError("missing or multiple child records")
    row = rows[0]
    expected = {"schema_version": 1, "kind": "parametric", "function": function,
                "param": parameter, "inner_repeats": 1, "cache_mode": "cold",
                "status": "ok", "error": None, "profile_kernel": True}
    if any(row.get(key) != value for key, value in expected.items()):
        raise ValueError("profile is not the requested successful single cold invocation")
    if (row.get("env", {}).get("git_commit") != revision or
            row.get("env", {}).get("git_dirty") is not False):
        raise ValueError("child source binding differs")
    if type(row.get("peak_rss_kb")) is not int or row["peak_rss_kb"] <= 0:
        raise ValueError("missing native process memory observation")
    result = row.get("result_hash")
    if not isinstance(result, str) or not result.startswith("0x"):
        raise ValueError("missing result identity")
    int(result, 16)
    return row


def page_peak(text):
    if "--pages-as-heap=yes" not in text or "time_unit: B" not in text:
        raise ValueError("wrong Massif memory mode")
    snapshots = []
    for block in text.split("snapshot=")[1:]:
        row = {}
        for line in block.splitlines():
            key, separator, value = line.partition("=")
            if separator and key in {"time", "mem_heap_B", "mem_heap_extra_B", "mem_stacks_B"}:
                if key in row or not value.isdecimal():
                    raise ValueError("malformed memory snapshot")
                row[key] = int(value)
        if set(row) != {"time", "mem_heap_B", "mem_heap_extra_B", "mem_stacks_B"}:
            raise ValueError("incomplete memory snapshot")
        if row["mem_heap_extra_B"] != 0 or row["mem_stacks_B"] != 0:
            raise ValueError("page mode unexpectedly has separate stack/admin counts")
        snapshots.append(row)
    if not snapshots or max(row["mem_heap_B"] for row in snapshots) <= 0:
        raise ValueError("missing memory snapshots")
    return {"mapped_page_peak_bytes": max(row["mem_heap_B"] for row in snapshots),
            "snapshots": len(snapshots)}


def validate_retained(directory):
    """Check every retained raw file and the complete fixed capture schedule."""
    directory = Path(directory)
    archive = json.loads((directory / "archive.json").read_text())
    if archive.get("schema") != "hex-memory-archive-v1":
        raise ValueError("unknown memory archive")
    raw = {}
    for name, binding in archive["files"].items():
        stored = binding["stored"]
        if Path(name).name != name or Path(stored).name != stored:
            raise ValueError("archive filenames must stay in the directory")
        data = (directory / stored).read_bytes()
        if hashlib.sha256(data).hexdigest() != binding["stored_sha256"]:
            raise ValueError("stored memory artifact hash differs")
        data = gzip.decompress(data) if stored.endswith(".gz") else data
        if hashlib.sha256(data).hexdigest() != binding["raw_sha256"]:
            raise ValueError("raw memory artifact hash differs")
        raw[name] = data
    metadata = json.loads(raw["metadata.json"])
    if (metadata.get("schema") != "hex-sign-det-process-memory-v1" or
            metadata.get("state") != "complete" or metadata.get("scope") != SCOPE or
            metadata.get("trials") != TRIALS):
        raise ValueError("incomplete or different memory collection")
    if set(raw) != set(metadata["file_sha256"]) | {"metadata.json"}:
        raise ValueError("missing or additional retained artifacts")
    for name, expected in metadata["file_sha256"].items():
        if hashlib.sha256(raw[name]).hexdigest() != expected:
            raise ValueError("original capture hash differs")
    source = metadata["source_archive"]
    if hashlib.sha256(raw[source["file"]]).hexdigest() != source["sha256"]:
        raise ValueError("source archive differs")
    schedule = []
    for trial in range(TRIALS):
        for name, group in metadata["groups"].items():
            parameters, functions = GROUPS[name]
            if group != [parameters, functions]:
                raise ValueError("different registered memory schedule")
            for parameter in parameters:
                for function in functions:
                    modes = ["native", "massif"] if trial % 2 == 0 else ["massif", "native"]
                    schedule.extend(("Hex.SignDetBench." + function, parameter, trial, mode) for mode in modes)
    if len(schedule) != len(metadata["runs"]):
        raise ValueError("incomplete memory schedule")
    for record, expected in zip(metadata["runs"], schedule, strict=True):
        subject = (record["function"], record["parameter"], record["trial"], record["mode"])
        if subject != expected or record["state"] != "complete" or record["exit_code"] != 0:
            raise ValueError("wrong memory capture subject or failed point")
        label = record["label"]
        row = child_record(raw[label + ".stdout"].decode(), subject[0], subject[1], metadata["revision"])
        answer = metadata["expected_result_hashes"][f"{subject[0]}:{subject[1]}"]
        if row["result_hash"] != answer or record["result_hash"] != answer:
            raise ValueError("retained callback answer differs")
        if record["process_peak_rss_kib"] != row["peak_rss_kb"]:
            raise ValueError("retained process memory differs")
        if subject[3] == "massif":
            peak = page_peak(raw[label + ".massif"].decode())
            if any(record.get(key) != value for key, value in peak.items()):
                raise ValueError("retained page peak differs")
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--valgrind", required=True, type=Path)
    parser.add_argument("--groups", nargs="+", choices=GROUPS, default=list(GROUPS))
    args = parser.parse_args()
    if len(args.groups) != len(set(args.groups)):
        parser.error("each group must occur once")
    out = args.output.resolve()
    if out.is_relative_to(ROOT) or out.exists():
        parser.error("use a new output directory outside the source tree")
    vg = args.valgrind.resolve()
    if any(character.isspace() for character in str(vg) + str(out)):
        parser.error("the profiler prefix does not support whitespace paths")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True):
        raise ValueError("commit the measurement sources first")
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    harness = harness_binding(ROOT)
    sources = source_hashes()
    for name in ("sign_det_memory", "test_sign_det_memory", "sign_det_compare", "sign_det_joint",
                 "sign_det_joint_timing", "sign_det_maximal_matrix", "sign_det_height"):
        path = "scripts/bench/" + name + ".py"
        sources[path] = digest(ROOT / path)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    out.mkdir(parents=True)
    metadata = {"schema": "hex-sign-det-process-memory-v1", "scope": SCOPE,
                "revision": revision, "source_sha256": sources,
                "binary_sha256": digest(executable), "harness_binding": harness,
                "valgrind": str(vg), "valgrind_sha256": digest(vg),
                "valgrind_version": subprocess.check_output([str(vg), "--version"], text=True).strip(),
                "groups": {name: GROUPS[name] for name in args.groups}, "trials": TRIALS,
                "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
                "host": platform.node(), "platform": platform.platform(), "load_before": os.getloadavg(),
                "runs": [], "state": "running"}

    def save():
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")

    def inventory(label, arguments):
        path = out / (label + ".stdout")
        record = {"label": label, "command": [str(executable), *arguments], "state": "running"}
        metadata.setdefault("inventories", []).append(record)
        save()
        with path.open("w") as stdout, (out / (label + ".stderr")).open("w") as stderr:
            result = subprocess.run(record["command"], cwd=ROOT, stdout=stdout, stderr=stderr)
        record.update(state="complete", exit_code=result.returncode)
        save()
        if result.returncode:
            raise ValueError("input/callback verification failed: " + label)
        return path

    expected = {}

    def capture(function, parameter, trial, mode):
        label = f'{function}-{parameter}-{trial}-{mode}'
        prefix = "/usr/bin/env MIMALLOC_SHOW_STATS=1"
        if mode == "massif":
            prefix += (f" {vg} --tool=massif --pages-as-heap=yes --time-unit=B"
                       f" --massif-out-file={out / (label + '.massif')}")
        command = [str(executable), "profile", function, "--param", str(parameter),
                   "--cache-mode", "cold", "--profiler", prefix]
        record = {"label": label, "function": function, "parameter": parameter,
                  "trial": trial, "mode": mode, "command": command, "state": "running"}
        metadata["runs"].append(record)
        save()
        start = time.monotonic()
        with (out / (label + ".stdout")).open("w") as stdout, (out / (label + ".stderr")).open("w") as stderr:
            process = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr,
                                       start_new_session=True)
            try:
                process.wait()
            except BaseException:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                raise
        record.update(state="complete", exit_code=process.returncode,
                      instrumented_wall_seconds=time.monotonic() - start, load_after=os.getloadavg())
        save()
        if process.returncode:
            raise ValueError(f"profile failed: {label}; output is retained")
        row = child_record((out / (label + ".stdout")).read_text(), function, parameter, revision)
        if row["result_hash"] != expected[(function, parameter)]:
            raise ValueError("callback differs from the validated input answer")
        record.update(result_hash=row["result_hash"], process_peak_rss_kib=row["peak_rss_kb"])
        if mode == "massif":
            record.update(page_peak((out / (label + ".massif")).read_text()))
        save()
        print(label, "retained", flush=True)
        return row["result_hash"]

    try:
        archive_sources(out, metadata)
        save()
        for group in args.groups:
            parameters, functions = GROUPS[group]
            if group == "sparse":
                path = inventory("inputs-sparse", ["inspect"])
                rows = inventory_hashes(path)
                keys = ["productionResultHash", "replayResultHash", "replayResultHash"]
            elif group == "matrix":
                path = inventory("inputs-matrix", ["inspect-maximal-matrix-dimensions"])
                rows = validate_matrix(path, by_dimension=True)
                keys = ["solveResultHash", "checkResultHash"]
            elif group == "height":
                path = inventory("inputs-height", ["inspect-height-phases"])
                validate_height(path, height_sensitive=True)
                rows = {r["height"]: r for r in map(json.loads, path.read_text().splitlines())}
                keys = ["productionResultHash", "replayResultHash"]
            else:
                rows = {}
                for parameter in parameters:
                    path = inventory(f"inputs-joint-{parameter}", ["inspect-joint", str(parameter)])
                    validate_joint(path, degrees=[parameter])
                    path = inventory(f"answers-joint-{parameter}", ["inspect-joint-timings", str(parameter)])
                    record = [json.loads(line) for line in path.read_text().splitlines()]
                    if len(record) != 1 or record[0]["degree"] != parameter:
                        raise ValueError("missing joint callback verification")
                    rows[parameter] = record[0]
                keys = ["comparisonResultHash", "replayResultHash"]
            for parameter in parameters:
                for name, key in zip(functions, keys, strict=True):
                    value = rows[parameter][key]
                    if type(value) is not int or not 0 <= value < 2**64:
                        raise ValueError("invalid expected callback result")
                    expected[("Hex.SignDetBench." + name, parameter)] = hex(value)
        metadata["expected_result_hashes"] = {f"{name}:{parameter}": value
                                               for (name, parameter), value in expected.items()}
        save()
        for trial in range(TRIALS):
            for group in args.groups:
                parameters, functions = GROUPS[group]
                for parameter in parameters:
                    for name in functions:
                        function = "Hex.SignDetBench." + name
                        modes = ["native", "massif"] if trial % 2 == 0 else ["massif", "native"]
                        answers = [capture(function, parameter, trial, mode) for mode in modes]
                        if answers[0] != answers[1]:
                            raise ValueError("profiling changed the computed answer")
        if (digest(executable) != metadata["binary_sha256"] or harness_binding(ROOT) != harness or
                any(digest(ROOT / path) != value for path, value in sources.items()) or
                subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != revision or
                subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)):
            raise ValueError("source, harness or executable changed during measurement")
        metadata["state"] = "complete"
    except BaseException as error:
        metadata.update(state="failed", error=str(error), exception=type(error).__name__)
        raise
    finally:
        metadata["load_after"] = os.getloadavg()
        metadata["file_sha256"] = {p.name: digest(p) for p in sorted(out.iterdir())
                                    if p.is_file() and p.name != "metadata.json"}
        save()
        lease.close()


if __name__ == "__main__":
    main()
