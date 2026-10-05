"""Recheck operation-window leaf attribution without executing archived code."""
from pathlib import Path
import gzip
import hashlib
import json
import re
from collections import Counter

DENSE = "lp_Hex_Fin_foldl_loop___at___00Vector_dotProductImpl___at___00Hex_Matrix_mulImpl___at___00Hex_SignDet_System_check_spec__3_spec__3_spec__6"
HEADER = re.compile(r"\s*(\d+)/(\d+)\s+(\d+)\.(\d{9}):\s+([0-9a-f]+)\s+(.*?)\s+\((.*)\)$")


def read_archive(directory, schema):
    directory = Path(directory)
    archive = json.loads((directory/"archive.json").read_text())
    if archive["schema"] != schema:
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
    return raw


def validate(directory, *, matrix_directory=None):
    directory = Path(directory)
    raw = read_archive(directory, "hex-matrix-check-attribution-archive-v1")
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
    # The profile hashes the computational closure (275 files). The timing
    # collector additionally hashes five documentation/collector files.
    symbols = {}
    for line in raw["symbols.txt"].decode().splitlines():
        fields = line.split()
        if len(fields) == 4 and fields[2] in ("t", "T", "w", "W"):
            symbols.setdefault(fields[3], []).append((int(fields[0], 16), int(fields[1], 16)))
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
        executable = capture["command"][0]
        mappings = []
        mapping_pattern = re.compile(r".*PERF_RECORD_MMAP2 \d+/\d+: \[0x([0-9a-f]+)\(0x([0-9a-f]+)\) @ (?:0x)?([0-9a-f]+) .*\]: ([rwxp-]+) (.*)")
        for line in raw[f"{size}/perf-mappings.txt"].decode().splitlines():
            mapping = mapping_pattern.fullmatch(line)
            if mapping and mapping[5] == executable:
                mappings.append((int(mapping[1], 16), int(mapping[2], 16),
                                 int(mapping[3], 16), mapping[4]))
        bases = [start for start, length, offset, mode in mappings if offset == 0]
        if len(bases) != 1:
            raise ValueError("missing executable load base")
        base = bases[0]  # This PIE's first ELF LOAD has virtual address zero.
        leaves = Counter()
        threads = Counter()
        for line in raw[f"{size}/perf-leaves.txt"].decode().splitlines():
            match = HEADER.fullmatch(line)
            if match is None:
                raise ValueError("unrecognized leaf sample")
            stamp = int(match[3])*10**9+int(match[4])
            if int(match[1]) == header["pid"] and region["mono_t0_ns"] <= stamp <= region["mono_t1_ns"]:
                if match[7] == executable:
                    address = int(match[5], 16)
                    if not any(start <= address < start+length and "x" in mode
                               for start, length, offset, mode in mappings):
                        raise ValueError("leaf address outside executable mapping")
                    # PLT trampolines have no ordinary nm text interval; they
                    # remain non-dense leaves and are checked only by mapping.
                    if not match[6].endswith("@plt") and not any(
                            start <= address-base < start+length
                            for start, length in symbols.get(match[6], [])):
                        raise ValueError(f"leaf symbol disagrees with address interval: {match[6]} at {address-base:x}")
                elif match[6] == DENSE:
                    raise ValueError("dense loop attributed to another binary")
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


def validate_comparison(directory):
    import statistics
    import math
    raw = read_archive(directory, "hex-matrix-power-archive-v1")
    meta = json.loads(raw["metadata.json"])
    if (meta["state"] != "complete" or meta["provenance_unchanged"] is not True or
            meta["sizes"] != [243, 729] or meta["trials"] != 6 or
            set(meta["arms"]) != {"before", "after"}):
        raise ValueError("wrong paired comparison plan or provenance")
    for arm in ("before", "after"):
        if hashlib.sha256(raw[arm+"-Matrix.lean"]).hexdigest() != meta["arms"][arm]["matrix_sha256"]:
            raise ValueError("paired source module mismatch")
    schedule = [(trial, size, arm) for trial in range(6) for size in [243, 729]
                for arm in (["before", "after"] if trial % 2 == 0 else ["after", "before"])]
    if [(r["trial"], r["size"], r["arm"]) for r in meta["samples"]] != schedule:
        raise ValueError("incomplete or reordered paired comparison")
    single = meta.get("schema_version") == 2
    if single:
        before = meta["arms"]["before"]["source_sha256"]
        after = meta["arms"]["after"]["source_sha256"]
        changed = {name for name in before.keys() | after.keys()
                   if before.get(name) != after.get(name)}
        if changed != {"HexSignDet/Matrix.lean"} or meta["regime"] != "single cold call":
            raise ValueError("paired computational closures differ outside the optimization")
        for arm in ("before", "after"):
            if meta["arms"][arm]["matrix_sha256"] != meta["arms"][arm]["source_sha256"]["HexSignDet/Matrix.lean"]:
                raise ValueError("paired module differs from source closure")
    else:
        # Historical exploratory data used two bases and asymmetric tuning.
        # Their raw values validate, but they do not isolate the optimization.
        original = json.loads((Path(directory).parents[1]/"sign-det-matrix-wide/6b977999bc-first/timing/metadata.json").read_text())
        if meta["arms"]["before"]["binary_sha256"] != original["binary_sha256"]:
            raise ValueError("exploratory baseline differs from original checker")
    times = {}
    for sample in meta["samples"]:
        trial, size, arm = sample["trial"], sample["size"], sample["arm"]
        label = f"{trial}-{size}-{arm}"
        rows = [json.loads(line) for line in raw[label+".stdout"].decode().splitlines()
                if line.startswith("{")]
        row = sample["row"]
        if rows != [row] or sample["capture"] != label:
            raise ValueError("paired row disagrees with raw output")
        duration = row["per_call_nanos"]
        if (row["status"] != "ok" or row["result_hash"] != "0xb" or row["param"] != size or
                row["cache_mode"] != ("cold" if single else "warm") or
                (single and row["inner_repeats"] != 1) or row["env"]["git_commit"] != meta["arms"][arm]["revision"] or
                row["env"]["git_dirty"] is not False or type(duration) not in (int, float) or
                not math.isfinite(duration) or duration <= 0 or
                type(row["inner_repeats"]) is not int or row["inner_repeats"] <= 0 or
                row["function"] != "Hex.SignDetBench.MaximalMatrix.runTensorCheck"):
            raise ValueError("failed or substituted paired result")
        times[trial, size, arm] = duration
    summary = {str(size): {"median_before_after_ratio": statistics.median(
        times[trial, size, "before"]/times[trial, size, "after"] for trial in range(6))}
        for size in [243, 729]}
    if summary != meta["summary"]:
        raise ValueError("paired ratios disagree with raw samples")
    return summary


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--comparison", action="store_true", help="validate a before/after comparison")
    args = parser.parse_args()
    check = validate_comparison if args.comparison else validate
    print(json.dumps(check(args.directory), indent=2))
