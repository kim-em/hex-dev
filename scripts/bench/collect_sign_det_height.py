#!/usr/bin/env python3
"""Retain the declared coefficient-height schedules and their unmodified verdicts."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_height import FUNCTIONS, validate, validate_phases, validate_export
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.cpu_lease import cpu_lease as acquire_cpu


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def revision():
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def clean():
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True):
        raise ValueError("commit source changes before collecting measurements")



def audit_runtime(executable, out):
    """Record the actual native routes used by the GMP-specific cost model."""
    text = ""
    routes = {
        "lean_nat_gcd": "_ZN4lean3gcdERNS_3mpzERKS0_S3_",
        "lean_nat_log2": "_ZNK4lean3mpz4log2Ev",
        "lean_big_int_to_nat": "_ZN4lean3mpzC1ERKS0_",
        "_ZN4lean3gcdERNS_3mpzERKS0_S3_": "__gmpz_gcd",
        "_ZNK4lean3mpz4log2Ev": "__gmpz_sizeinbase",
    }
    for symbol, target in routes.items():
        result = subprocess.run(["objdump", "-d", "--disassemble=" + symbol, str(executable)],
                                check=True, capture_output=True, text=True)
        text += result.stdout
        if f"<{symbol}>:" not in result.stdout or f"<{target}>" not in result.stdout:
            raise ValueError(f"missing declared runtime call route: {symbol} -> {target}")
    record = out / "runtime-backend.log"
    record.write_text(text)
    return {"implementation": "GMP", "evidence": record.name, "sha256": digest(record),
            "bit_length": "lean_nat_log2 -> lean::mpz::log2 -> mpz_sizeinbase",
            "magnitude_copy": "lean_big_int_to_nat -> lean::mpz copy constructor",
            "version": None,
            "version_note": "Precise GMP version is unrecorded"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    clean()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("write measurement output outside the source worktree")
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    if not executable.resolve().is_relative_to(ROOT):
        raise ValueError("measurement executable must resolve inside the source worktree")
    if not executable.exists():
        raise ValueError("build hexsigndet_bench first")
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    out.mkdir(parents=True, exist_ok=False)
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    sources = source_hashes()
    for relative in ("scripts/bench/collect_sign_det_height.py",
                     "scripts/bench/sign_det_height.py", "scripts/bench/test_sign_det_height.py",
                     "scripts/bench/sign_det_compare.py", "reports/sign-det-height-model.md"):
        sources[relative] = digest(ROOT / relative)
    metadata = {
        "schema": "hex-sign-det-height-measurement-v2", "revision": revision(),
        "source_sha256": sources, "binary_sha256": digest(executable),
        "source_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "bignum_backend": audit_runtime(executable, out),
        "checksum": "coefficient bit lengths included",
        "binary_path": str(executable), "binary_resolved_path": str(executable.resolve()),
        "freshness_check": "lake build --no-build hexsigndet_bench",
        "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
        "affinity": sorted(os.sched_getaffinity(0)), "load_before": os.getloadavg(),
        "cpu_cache": [{name: (entry / name).read_text().strip()
                       for name in ("level", "type", "size")}
                      for entry in sorted(Path(f"/sys/devices/system/cpu/cpu{cpu}/cache").glob("index*"))],
        "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "functions": list(FUNCTIONS), "scientific_timing_samples": 0,
        "state": "running", "commands": [], "results": {},
    }
    record = out / "metadata.json"

    def save():
        record.write_text(json.dumps(metadata, indent=2) + "\n")

    def check_unchanged():
        clean()
        if revision() != metadata["revision"] or digest(executable) != metadata["binary_sha256"]:
            raise ValueError("source revision or executable changed during measurement")
        for relative, expected in sources.items():
            if digest(ROOT / relative) != expected:
                raise ValueError("source changed during measurement: " + relative)

    def run(name, arguments):
        command = [str(executable), *arguments]
        metadata["commands"].append({"name": name, "argv": command})
        save()
        with (out / (name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        metadata["commands"][-1]["exit_code"] = result.returncode
        save()
        check_unchanged()
        return result

    try:
        archive_sources(out, metadata)
        save()
        run("inventory", ["inspect-height"]).check_returncode()
        inventory = out / "inventory.log"
        metadata["inventory_rows"] = validate(inventory)
        run("phases", ["inspect-height-phases"]).check_returncode()
        phase_inventory = out / "phases.log"
        metadata["phase_rows"] = validate_phases(phase_inventory, height_sensitive=True)
        save()
        for name in FUNCTIONS:
            export = out / (name + ".json")
            result = run(name, ["run", "Hex.SignDetBench." + name,
                                "--export-file", str(export)])
            # An inconclusive verdict can return nonzero. Validate the complete
            # export before interpreting the exit code; never discard its samples.
            summary = validate_export(export, name, phase_inventory, metadata["revision"],
                                      metadata["source_toolchain"])
            if result.returncode not in (0, 1) or (
                    result.returncode == 1 and summary["verdict"] != "inconclusive"):
                result.check_returncode()
            metadata["results"][name] = summary
            metadata["scientific_timing_samples"] += 42
            save()
        metadata["state"] = "complete"
    except BaseException as error:
        metadata["state"] = "failed"
        metadata["error"] = str(error)
        raise
    finally:
        metadata["finished"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        metadata["load_after"] = os.getloadavg()
        metadata["binary_sha256_after"] = digest(executable)
        metadata["revision_after"] = revision()
        metadata["unchanged"] = (metadata["binary_sha256_after"] == metadata["binary_sha256"]
                                 and metadata["revision_after"] == metadata["revision"])
        if not metadata["unchanged"]:
            metadata["state"] = "failed"
            metadata["error"] = "source revision or executable changed at collection end"
        metadata["output_sha256"] = {
            path.name: digest(path) for path in sorted(out.iterdir()) if path.is_file()
            and path.name != "metadata.json"}
        save()
        lease.close()
    print(out, metadata["state"], metadata["scientific_timing_samples"], "samples", flush=True)
    return int(metadata["state"] != "complete" or
               any(r["verdict"] == "inconclusive" for r in metadata["results"].values()))


if __name__ == "__main__":
    raise SystemExit(main())
