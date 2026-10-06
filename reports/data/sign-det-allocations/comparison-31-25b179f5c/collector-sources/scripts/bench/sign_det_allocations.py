#!/usr/bin/env python3
"""Capture operation-scoped client allocation requests with Valgrind.

Use existing benchmark callbacks, a fixed trial-major schedule and retained
instrumented output. Requested-byte counts make no running-time complexity claim.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.structural_tactic_sweep import acquire_cpu

ALLOCATORS = {
    "lean_alloc_small_object_core": "lean", "lean_alloc_object": "lean",
    "mi_malloc": "mimalloc", "mi_malloc_small": "mimalloc", "mi_new_n": "mimalloc",
    "__gmp_default_allocate": "gmp", "__gmp_default_reallocate": "gmp",
}
KINDS = ("lean", "mimalloc", "gmp")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def callback_type(function):
    if not re.fullmatch(r"Hex\.SignDetBench(?:\.[A-Za-z][A-Za-z0-9]*)+", function):
        raise ValueError("callback names must have plain alphanumeric components")
    symbol = "lp_Hex_" + function.replace(".", "_")
    pattern = re.compile(r"LEAN_EXPORT (lean_object\*|uint8_t|uint64_t) " +
                         re.escape(symbol) + r"\(lean_object\*[^,)]*\)\{")
    matches = [(path, m[1]) for path in (ROOT / ".lake/build/ir/HexSignDet").glob("*.c")
               for m in pattern.finditer(path.read_text())]
    if len(matches) != 1:
        raise ValueError("callback must have one object argument and a supported result ABI")
    path, result = matches[0]
    return symbol, "void*" if result == "lean_object*" else result, path


def counters(output):
    records = [json.loads(line.removeprefix("SIGN_DET_ALLOCATIONS "))
               for line in output.splitlines() if line.startswith("SIGN_DET_ALLOCATIONS ")]
    if len(records) != 1 or records[0]["callbacks"] != 1 or records[0]["overflow"]:
        raise ValueError("expected one nonoverflowing callback counter record")
    return records[0]


def check_events(counts, dhat, origin):
    """Check provenance and per-entry-point assignment of the emitted events.

    DHAT records these same requests. It does not independently detect missed
    allocators or prove complete coverage of a callback's allocation paths.
    """
    if dhat["mode"] != "ad-hoc":
        raise ValueError("wrong allocation capture mode")
    totals = {kind: [0, 0] for kind in KINDS}
    for point in dhat["pps"]:
        frame = dhat["ftbl"][point["fs"][0]]
        if "(in " + str(origin) + ")" not in frame:
            raise ValueError("emitting frame is not from the expected wrapper")
        names = [name for name in ALLOCATORS if re.search(r": " + name + r"(?:\s|\()", frame)]
        if len(names) != 1:
            raise ValueError("unclassified emitting wrapper frame: " + frame)
        group = totals[ALLOCATORS[names[0]]]
        group[0] += point["tb"]
        group[1] += point["tbk"]
    for kind in KINDS:
        if totals[kind] != [counts[kind + "_bytes"], counts[kind + "_requests"]]:
            raise ValueError("DHAT entry-point assignment disagrees with callback counters")
    if sum(counts[kind + "_requests"] for kind in KINDS) == 0:
        raise ValueError("no allocation events")


def benchmark_row(output, function, parameter):
    rows = [json.loads(line) for line in output.splitlines() if line.startswith('{"schema_version"')]
    if len(rows) != 1:
        raise ValueError("missing benchmark result")
    row = rows[0]
    if (row["function"] != function or row["param"] != parameter or row["status"] != "ok" or
            row["inner_repeats"] != 1 or row["cache_mode"] != "cold" or row["result_hash"] is None):
        raise ValueError("wrong operation, failed result, missing hash or repeated invocation")
    return row


def allocator_inventory(exe, out):
    symbols = subprocess.check_output(["nm", "--defined-only", str(exe)], text=True)
    inventory = [line for line in symbols.splitlines() if re.search(
        r"\b(?:lean_alloc_\w+|mi_\w+|__gmp_\w+|malloc|calloc|realloc)$", line)]
    (out / "allocator-symbols.txt").write_text("\n".join(inventory) + "\n")
    names = {line.split()[-1] for line in inventory}
    missing = set(ALLOCATORS) - names
    if missing:
        raise ValueError("wrapped allocators absent from executable: " + ", ".join(sorted(missing)))
    return {"defined_symbols": inventory, "sha256": digest(out / "allocator-symbols.txt")}


def direct_allocator_calls(exe, out):
    """Audit direct mimalloc client calls; this does not cover indirect calls."""
    proc = subprocess.Popen(["objdump", "-d", "--demangle", "--no-show-raw-insn", str(exe)],
                            stdout=subprocess.PIPE, text=True)
    caller = ""
    calls = set()
    for line in proc.stdout:
        label = re.match(r"^[0-9a-f]+ <(.+)>:", line)
        if label:
            caller = label[1]
        target = re.search(r"\b(?:call|jmp)\s+[0-9a-f]+ <(mi_[^>]+)>", line)
        if target and not caller.startswith(("mi_", "_mi_")):
            calls.add(target[1])
    if proc.wait():
        raise RuntimeError("allocator call disassembly failed")
    (out / "direct-mimalloc-calls.json").write_text(json.dumps(sorted(calls), indent=2) + "\n")
    # Freeing and option/thread setup are not client object allocation requests.
    allowed = {"mi_malloc", "mi_malloc_small", "mi_new_n", "mi_free", "mi_free_size",
               "mi_option_init(mi_option_desc_s*)", "mi_thread_init"}
    unexpected = calls - allowed
    if unexpected:
        raise ValueError("uncovered direct mimalloc calls: " + ", ".join(sorted(unexpected)))
    return {"targets": sorted(calls), "sha256": digest(out / "direct-mimalloc-calls.json"),
            "scope": "direct symbol calls outside mi_/_mi_ routines; indirect/inlined alternatives require audit"}


def compile_wrapper(command, path, metadata):
    metadata.setdefault("compile_commands", []).append(command)
    run = subprocess.run(command, capture_output=True, text=True)
    path.with_suffix(".compile.log").write_text(run.stdout + run.stderr)
    run.check_returncode()


def self_check(out, args, metadata):
    cases = (("void*", "0x12345678u"), ("uint8_t", "0xabu"), ("uint64_t", "0xfedcba9876543210ULL"))
    checks = []
    for i, (result, value) in enumerate(cases):
        exe = out / f"self-check-{i}"
        command = ["cc", "-O2", "-Wall", "-Wextra", "-I" + str(args.include),
                   "-DSIGN_DET_CHECK", "-DSIGN_DET_RESULT=" + result, "-DSIGN_DET_CHECK_VALUE=" + value,
                   str(ROOT / "scripts/bench/sign_det_allocations.c"), "-o", str(exe)]
        compile_wrapper(command, exe, metadata)
        raw = out / f"self-check-{i}.dhat.json"
        run = subprocess.run([str(args.valgrind), "--tool=dhat", "--mode=ad-hoc",
                              "--dhat-out-file=" + str(raw), str(exe)], capture_output=True, text=True)
        log = out / f"self-check-{i}.log"
        log.write_text(run.stdout + run.stderr)
        run.check_returncode()
        counts = counters(log.read_text())
        expected = {"callbacks": 1, "overflow": 0, "lean_requests": 2, "lean_bytes": 64,
                    "mimalloc_requests": 2, "mimalloc_bytes": 56, "gmp_requests": 2, "gmp_bytes": 160}
        if counts != expected:
            raise ValueError("controlled allocator/nesting fixture failed")
        check_events(counts, json.loads(raw.read_text()), exe)
        checks.append({"result_type": result, "returned_value": value, "counters": counts,
                       "log_sha256": digest(log), "dhat_sha256": digest(raw)})
    metadata["self_checks"] = checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--functions", nargs="+", default=[])
    parser.add_argument("--parameters", nargs="+", type=int, default=[])
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--self-check", action="store_true", help="run only the controlled ABI/allocation fixtures")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--valgrind", type=Path, required=True)
    parser.add_argument("--include", type=Path, required=True)
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64" or args.trials < 1:
        parser.error("this profiler requires Linux x86_64 and positive trials")
    if not args.self_check and (not args.functions or not args.parameters or any(n < 1 for n in args.parameters)):
        parser.error("capture requires functions and positive parameters")
    os.chdir(ROOT)
    out = args.output.resolve()
    for path in (str(out), str(args.valgrind), str(ROOT / ".lake/build/bin/hexsigndet_bench")):
        if re.search(r"[\s\"']", path):
            parser.error("lean-bench profiler commands do not support quoted or whitespace-containing paths")
    out.mkdir(parents=True, exist_ok=False)
    metadata = {"schema": "hex-sign-det-allocation-v1", "host": platform.node(), "state": "initializing"}
    samples = []
    lease = None
    sources = {}
    exe = ROOT / ".lake/build/bin/hexsigndet_bench"
    try:
        cpu, lease = acquire_cpu()
        os.sched_setaffinity(0, {cpu})
        metadata.update(cpu=cpu, load_before=os.getloadavg(), functions=args.functions,
                        parameters=args.parameters, trials=args.trials,
                        cc_version=subprocess.check_output(["cc", "--version"], text=True),
                        valgrind_version=subprocess.check_output([str(args.valgrind), "--version"], text=True).strip(),
                        headers_sha256={name: digest(args.include / "valgrind" / name)
                                        for name in ("valgrind.h", "dhat.h")})
        collector_names = ("scripts/bench/sign_det_allocations.c", "scripts/bench/sign_det_allocations.py")
        collector_hashes = {name: digest(ROOT / name) for name in collector_names}
        metadata["collector_sha256"] = collector_hashes
        for name in collector_names:
            target = out / "collector-sources" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / name).read_bytes())
        self_check(out, args, metadata)
        if any(digest(ROOT / name) != expected for name, expected in collector_hashes.items()):
            raise ValueError("collector changed during the self-check")
        if not args.self_check:
            sources_before_build = source_hashes() | collector_hashes
            with (out / "build.log").open("w") as stream:
                build = subprocess.run(["lake", "build", "hexsigndet_bench"], stdout=stream, stderr=subprocess.STDOUT)
            build.check_returncode()
            sources = source_hashes() | {name: digest(ROOT / name) for name in collector_names}
            if sources != sources_before_build:
                raise ValueError("source changed during the Lake build; output retained")
            metadata.update(source_sha256=sources, binary_sha256=digest(exe),
                            revision=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                            git_status=subprocess.check_output(["git", "status", "--porcelain"], text=True),
                            allocator_inventory=allocator_inventory(exe, out),
                            direct_allocator_calls=direct_allocator_calls(exe, out))
            wrappers = {}
            for i, function in enumerate(args.functions):
                symbol, result, generated = callback_type(function)
                wrapper = out / f"wrapper-{i}.so"
                command = ["cc", "-shared", "-fPIC", "-ftls-model=initial-exec", "-O2", "-Wall", "-Wextra", "-I" + str(args.include),
                           "-DSIGN_DET_CALLBACK=" + symbol, "-DSIGN_DET_RESULT=" + result,
                           str(ROOT / "scripts/bench/sign_det_allocations.c"), "-o", str(wrapper)]
                compile_wrapper(command, wrapper, metadata)
                wrappers[function] = wrapper
                metadata.setdefault("callbacks", {})[function] = {
                    "symbol": symbol, "result_type": result, "generated_c_sha256": digest(generated),
                    "wrapper_sha256": digest(wrapper)}
            metadata["state"] = "running"
            for trial in range(1, args.trials + 1):
                for parameter in args.parameters:
                    for function in args.functions:
                        stem = f"{len(samples):03d}"
                        sample = {"trial": trial, "function": function, "parameter": parameter, "state": "running"}
                        samples.append(sample)
                        native_command = [str(exe), "profile", function, "--param", str(parameter),
                                          "--cache-mode", "cold", "--profiler", "env --"]
                        native = subprocess.run(native_command, capture_output=True, text=True)
                        native_log = out / (stem + ".native.log")
                        native_log.write_text(native.stdout + native.stderr)
                        native.check_returncode()
                        original = benchmark_row(native_log.read_text(), function, parameter)
                        raw = out / (stem + ".dhat.json")
                        # lean-bench splits this argument on whitespace, without shell quote handling.
                        profiler = " ".join(["env", "LD_PRELOAD=" + str(wrappers[function]), str(args.valgrind),
                                             "--tool=dhat", "--mode=ad-hoc", "--dhat-out-file=" + str(raw), "--"])
                        command = [str(exe), "profile", function, "--param", str(parameter),
                                   "--cache-mode", "cold", "--profiler", profiler]
                        log = out / (stem + ".log")
                        with log.open("w") as stream:
                            run = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
                        sample.update(command=command, exit_code=run.returncode, log_sha256=digest(log))
                        run.check_returncode()
                        row = benchmark_row(log.read_text(), function, parameter)
                        counts = counters(log.read_text())
                        check_events(counts, json.loads(raw.read_text()), wrappers[function])
                        if row["result_hash"] != original["result_hash"]:
                            raise ValueError("instrumentation changed the operation result")
                        sample.update(state="complete", result_hash=row["result_hash"], counters=counts,
                                      instrumented_peak_rss_kb=row["peak_rss_kb"], native_log_sha256=digest(native_log),
                                      dhat_sha256=digest(raw))
                        with (out / "samples.jsonl").open("a") as stream:
                            stream.write(json.dumps(sample) + "\n")
        metadata["state"] = "complete"
    except BaseException as error:
        metadata.update(state="failed", error=str(error))
        raise
    finally:
        metadata.update(samples=samples, load_after=os.getloadavg())
        try:
            if sources:
                metadata.update(binary_sha256_after=digest(exe),
                                source_sha256_after={name: digest(ROOT / name) for name in sources})
                unchanged = (metadata["binary_sha256_after"] == metadata["binary_sha256"] and
                             metadata["source_sha256_after"] == sources)
                metadata["source_unchanged"] = unchanged
                if not unchanged and metadata["state"] == "complete":
                    metadata["state"] = "source-changed"
        except OSError as error:
            metadata["final_identity_error"] = str(error)
            if metadata["state"] == "complete":
                metadata["state"] = "source-changed"
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        if lease:
            lease.close()
    if metadata["state"] != "complete":
        raise RuntimeError("source changed; capture retained without a final evidence claim")


if __name__ == "__main__":
    main()
