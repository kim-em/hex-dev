#!/usr/bin/env python3
"""Capture operation-scoped allocation requests using the existing benchmark.

Run a fixed trial-major schedule and retain every completed instrumented sample.
These captures count requested bytes; they make no running-time complexity claim.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.structural_tactic_sweep import acquire_cpu


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def callback_type(function):
    symbol = "lp_Hex_" + function.replace(".", "_")
    pattern = re.compile(r"LEAN_EXPORT (lean_object\*|uint8_t|uint64_t) " +
                         re.escape(symbol) + r"\(lean_object\*[^,)]*\)\{")
    matches = [(path, m[1]) for path in (ROOT / ".lake/build/ir/HexSignDet").glob("*.c")
               for m in pattern.finditer(path.read_text())]
    if len(matches) != 1:
        raise ValueError("callback must have one object argument and a supported scalar/object result")
    path, result = matches[0]
    return symbol, "void*" if result == "lean_object*" else result, path


def counters(output):
    records = [json.loads(line.removeprefix("SIGN_DET_ALLOCATIONS "))
               for line in output.splitlines() if line.startswith("SIGN_DET_ALLOCATIONS ")]
    if len(records) != 1 or records[0]["callbacks"] != 1 or records[0]["overflow"]:
        raise ValueError("expected exactly one checked, nonoverflowing callback counter record")
    return records[0]


def validate_sample(output, dhat, function, parameter):
    counts = counters(output)
    rows = [json.loads(line) for line in output.splitlines() if line.startswith('{"schema_version"')]
    if len(rows) != 1:
        raise ValueError("missing benchmark result")
    row = rows[0]
    if (row["function"] != function or row["param"] != parameter or
            row["status"] != "ok" or row["inner_repeats"] != 1 or row["cache_mode"] != "cold"):
        raise ValueError("incorrect operation, result or repetition count")
    if dhat["mode"] != "ad-hoc":
        raise ValueError("wrong allocation capture mode")
    total = sum(counts[k + "_bytes"] for k in ("lean", "mimalloc", "gmp"))
    events = sum(counts[k + "_requests"] for k in ("lean", "mimalloc", "gmp"))
    if (sum(p["tb"] for p in dhat["pps"]) != total or
            sum(p["tbk"] for p in dhat["pps"]) != events or events == 0):
        raise ValueError("DHAT events do not match independent callback counters")
    return {"function": function, "parameter": parameter, "result_hash": row["result_hash"],
            "counters": counts, "instrumented_peak_rss_kb": row["peak_rss_kb"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--functions", nargs="+", required=True)
    parser.add_argument("--parameters", nargs="+", type=int, required=True)
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--valgrind", type=Path, required=True)
    parser.add_argument("--include", type=Path, required=True)
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64" or args.trials < 1 or any(n < 1 for n in args.parameters):
        parser.error("this profiler requires Linux x86_64 and positive parameters/trials")
    os.chdir(ROOT)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    sources = source_hashes()
    for name in ("scripts/bench/sign_det_allocations.c", "scripts/bench/sign_det_allocations.py"):
        sources[name] = digest(ROOT / name)
    exe = ROOT / ".lake/build/bin/hexsigndet_bench"
    metadata = {"schema": "hex-sign-det-allocation-v1", "cpu": cpu, "host": platform.node(),
                "load_before": os.getloadavg(), "source_sha256": sources,
                "binary_sha256": digest(exe), "functions": args.functions,
                "parameters": args.parameters, "trials": args.trials, "state": "running",
                "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                "git_status": subprocess.check_output(["git", "status", "--porcelain"], text=True),
                "valgrind_version": subprocess.check_output([str(args.valgrind), "--version"], text=True).strip()}
    samples = []
    try:
        wrappers = {}
        for i, function in enumerate(args.functions):
            symbol, result, generated = callback_type(function)
            wrapper = out / f"wrapper-{i}.so"
            subprocess.run(["cc", "-shared", "-fPIC", "-O2", "-Wall", "-Wextra",
                            "-I" + str(args.include), "-DSIGN_DET_CALLBACK=" + symbol,
                            "-DSIGN_DET_RESULT=" + result,
                            str(ROOT / "scripts/bench/sign_det_allocations.c"), "-o", str(wrapper)], check=True)
            wrappers[function] = wrapper
            metadata.setdefault("callbacks", {})[function] = {
                "symbol": symbol, "result_type": result, "generated_c_sha256": digest(generated),
                "wrapper_sha256": digest(wrapper)}
        for trial in range(1, args.trials + 1):
            for parameter in args.parameters:
                for function in args.functions:
                    stem = f"{len(samples):03d}"
                    raw = out / (stem + ".dhat.json")
                    profiler = shlex.join(["env", "LD_PRELOAD=" + str(wrappers[function]),
                                          str(args.valgrind), "--tool=dhat", "--mode=ad-hoc",
                                          "--dhat-out-file=" + str(raw), "--"])
                    native_command = [str(exe), "_child", "--bench", function, "--param", str(parameter),
                                      "--target-nanos", "1", "--cache-mode", "cold"]
                    native = subprocess.run(native_command, capture_output=True, text=True)
                    (out / (stem + ".native.log")).write_text(native.stdout + native.stderr)
                    native.check_returncode()
                    native_rows = [json.loads(line) for line in native.stdout.splitlines()
                                   if line.startswith('{"schema_version"')]
                    if len(native_rows) != 1 or native_rows[0]["status"] != "ok":
                        raise ValueError("missing successful uninstrumented result")
                    command = [str(exe), "profile", function, "--param", str(parameter),
                               "--cache-mode", "cold", "--profiler", profiler]
                    log = out / (stem + ".log")
                    with log.open("w") as stream:
                        run = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
                    sample = {"trial": trial, "function": function, "parameter": parameter,
                              "command": command, "exit_code": run.returncode, "log_sha256": digest(log)}
                    samples.append(sample)
                    if run.returncode:
                        raise RuntimeError("allocation capture failed; output retained")
                    sample.update(validate_sample(log.read_text(), json.loads(raw.read_text()), function, parameter))
                    if sample["result_hash"] != native_rows[0]["result_hash"]:
                        raise ValueError("instrumentation changed the operation result")
                    sample["native_log_sha256"] = digest(out / (stem + ".native.log"))
                    sample["dhat_sha256"] = digest(raw)
                    with (out / "samples.jsonl").open("a") as stream:
                        stream.write(json.dumps(sample) + "\n")
        metadata["state"] = "complete"
    except BaseException as error:
        metadata.update(state="failed", error=str(error))
        raise
    finally:
        metadata.update(samples=samples, load_after=os.getloadavg(), binary_sha256_after=digest(exe),
                        source_sha256_after={name: digest(ROOT / name) for name in sources})
        if metadata["binary_sha256_after"] != metadata["binary_sha256"] or metadata["source_sha256_after"] != sources:
            metadata["state"] = "source-changed"
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()
    if metadata["state"] != "complete":
        raise RuntimeError("source changed; capture retained without release-quality claim")


if __name__ == "__main__":
    main()
