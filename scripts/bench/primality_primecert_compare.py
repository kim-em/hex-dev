#!/usr/bin/env python3
"""Compare fresh Hex and PrimeCert certificate-replay modules."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shutil
import socket
import statistics
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TEMPLATES = ROOT / "scripts" / "bench" / "primecert"
PRIMECERT_REV = "924f63d9"
BITS = (31, 61, 123, 256, 511, 512)


def run(directory: Path, command: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(command, cwd=directory, text=True, capture_output=True)
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"{' '.join(command)} failed in {directory}:\n{proc.stdout}{proc.stderr}"
        )
    return proc


def git(directory: Path, *args: str) -> str:
    return run(directory, ["git", *args]).stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_outputs(directory: Path, module: str) -> list[Path]:
    relative = Path(*module.split("."))
    paths: list[Path] = []
    for base in (directory / ".lake/build/lib/lean", directory / ".lake/build/ir"):
        prefix = base / relative
        if prefix.parent.is_dir():
            paths.extend(path for path in prefix.parent.glob(prefix.name + ".*") if path.is_file())
    return paths


def host_snapshot() -> dict[str, object]:
    processes = subprocess.run(
        ["ps", "-eo", "args="], text=True, capture_output=True, check=False
    ).stdout.splitlines()
    return {
        "load_average": list(os.getloadavg()),
        "lake_lean_processes": sum(
            " lake " in f" {line} " or "/bin/lean " in line for line in processes
        ),
    }


def fresh_build(directory: Path, module: str, cpu: int) -> dict[str, object]:
    removed = module_outputs(directory, module)
    for path in removed:
        path.unlink()
    command = ["taskset", "-c", str(cpu), "lake", "build", f"+{module}:olean"]
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    host_before = host_snapshot()
    start = time.perf_counter_ns()
    proc = subprocess.run(command, cwd=directory, env=env, text=True, capture_output=True)
    elapsed = time.perf_counter_ns() - start
    host_after = host_snapshot()
    if proc.returncode != 0:
        raise RuntimeError(
            f"{' '.join(command)} failed in {directory}:\n{proc.stdout}{proc.stderr}"
        )
    olean = directory / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
    return {
        "module": module,
        "command": command,
        "wall_nanos": elapsed,
        "olean_bytes": olean.stat().st_size,
        "host_before": host_before,
        "host_after": host_after,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def install_primecert_sources(checkout: Path) -> dict[str, str]:
    destination = checkout / "PrimeCert" / "Comparator"
    destination.mkdir(parents=True, exist_ok=True)
    hashes: dict[str, str] = {}
    for template in sorted(TEMPLATES.glob("*.lean.in")):
        target = destination / template.name.removesuffix(".in")
        shutil.copyfile(template, target)
        hashes[str(target.relative_to(checkout))] = sha256(target)
    return hashes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primecert-checkout", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=6)
    parser.add_argument("--cpu", type=int, default=23)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checkout = args.primecert_checkout.resolve()
    if args.samples < 1:
        parser.error("--samples must be positive")
    if git(ROOT, "status", "--porcelain"):
        raise RuntimeError("hex checkout must be clean before comparison")
    if git(checkout, "status", "--porcelain"):
        raise RuntimeError("PrimeCert checkout must be clean before source installation")
    base = git(checkout, "rev-parse", "HEAD")
    if not base.startswith(PRIMECERT_REV):
        raise RuntimeError(f"PrimeCert checkout is {base}, expected {PRIMECERT_REV}")

    primecert_hashes = install_primecert_sources(checkout)
    hex_head = git(ROOT, "rev-parse", "HEAD")
    source_hashes = {
        str(path.relative_to(ROOT)): sha256(path)
        for path in sorted(TEMPLATES.glob("*.lean.in"))
    }

    hex_modules = ["HexPrimality.ProofProbe.CoreBaseline"] + [
        f"HexPrimality.ProofProbe.Bit{bits}.Replay" for bits in BITS
    ]
    primecert_modules = ["PrimeCert.Comparator.Baseline"] + [
        f"PrimeCert.Comparator.Bit{bits}" for bits in BITS
    ]
    run(ROOT, ["lake", "build", *[f"+{module}:deps" for module in hex_modules]])
    run(checkout, ["lake", "build", *[f"+{module}:deps" for module in primecert_modules]])

    rows: list[dict[str, object]] = []
    for round_index in range(args.samples):
        for bits in BITS:
            tools = ["hex", "primecert"]
            if (round_index + BITS.index(bits)) % 2:
                tools.reverse()
            row: dict[str, object] = {"round": round_index + 1, "bits": bits, "tool_order": tools}
            for tool in tools:
                directory = ROOT if tool == "hex" else checkout
                baseline = (
                    "HexPrimality.ProofProbe.CoreBaseline"
                    if tool == "hex"
                    else "PrimeCert.Comparator.Baseline"
                )
                candidate = (
                    f"HexPrimality.ProofProbe.Bit{bits}.Replay"
                    if tool == "hex"
                    else f"PrimeCert.Comparator.Bit{bits}"
                )
                arms = [("baseline", baseline), ("replay", candidate)]
                if round_index % 2:
                    arms.reverse()
                built: dict[str, object] = {}
                for role, module in arms:
                    built[role] = fresh_build(directory, module, args.cpu)
                row[tool] = built
            rows.append(row)

    summary: dict[str, object] = {}
    for bits in BITS:
        selected = [row for row in rows if row["bits"] == bits]
        hex_replay = [int(row["hex"]["replay"]["wall_nanos"]) for row in selected]  # type: ignore[index]
        pc_replay = [int(row["primecert"]["replay"]["wall_nanos"]) for row in selected]  # type: ignore[index]
        hex_base = [int(row["hex"]["baseline"]["wall_nanos"]) for row in selected]  # type: ignore[index]
        pc_base = [int(row["primecert"]["baseline"]["wall_nanos"]) for row in selected]  # type: ignore[index]
        median_hex = statistics.median(hex_replay)
        median_pc = statistics.median(pc_replay)
        summary[str(bits)] = {
            "median_hex_replay_wall_nanos": median_hex,
            "median_primecert_replay_wall_nanos": median_pc,
            "hex_over_primecert_replay_ratio": median_hex / median_pc,
            "median_hex_baseline_wall_nanos": statistics.median(hex_base),
            "median_primecert_baseline_wall_nanos": statistics.median(pc_base),
        }

    document = {
        "schema": "hexprimality-primecert-comparison-v1",
        "measurement": "rotated-fresh-module-olean-wall-v1",
        "samples": args.samples,
        "cpu": args.cpu,
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "hex_commit": hex_head,
        "hex_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "hex_git_dirty_before_output": False,
        "primecert_commit": base,
        "primecert_toolchain": (checkout / "lean-toolchain").read_text().strip(),
        "primecert_source_sha256": primecert_hashes,
        "template_source_sha256": source_hashes,
        "rows": rows,
        "summary": summary,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
