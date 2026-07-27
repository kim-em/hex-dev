#!/usr/bin/env python3
"""Measure end-to-end ``isolate_roots`` elaboration and certificate replay.

Each sample removes only one committed probe module's generated artifacts and
rebuilds its ``olean`` through Lake.  The measured wall time includes source
elaboration, compiled certificate search run by the term elaborator, emitted
literal elaboration, and ordinary kernel checking.  It is not a kernel-only
measurement and it is not a ``lean-bench`` executable.

The import-only arm measures the same production import closure without an
``isolate_roots`` invocation.  Arm order rotates between rounds, and every
non-baseline result records its paired signed margin over that round's
baseline.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import os
import platform
import re
import signal
import shutil
import socket
import statistics
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / ".lake" / "build"
RSS_MARKER = "__HEX_MAX_RSS_KB__="
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

CASES: dict[str, dict[str, object]] = {
    "baseline": {
        "module": "HexRealRootsMathlib.Baseline",
        "family": "import-only",
        "degree": None,
        "width_bits": None,
    },
    "natural-6": {
        "module": "HexRealRootsMathlib.Natural6",
        "family": "natural-width",
        "degree": 6,
        "width_bits": None,
    },
    "natural-8": {
        "module": "HexRealRootsMathlib.Natural8",
        "family": "natural-width",
        "degree": 8,
        "width_bits": None,
    },
    "natural-10": {
        "module": "HexRealRootsMathlib.Natural10",
        "family": "natural-width",
        "degree": 10,
        "width_bits": None,
    },
    "refined-2": {
        "module": "HexRealRootsMathlib.Refined2",
        "family": "width-2^-20",
        "degree": 2,
        "width_bits": 20,
    },
    "refined-4": {
        "module": "HexRealRootsMathlib.Refined4",
        "family": "width-2^-20",
        "degree": 4,
        "width_bits": 20,
    },
    "refined-6": {
        "module": "HexRealRootsMathlib.Refined6",
        "family": "width-2^-20",
        "degree": 6,
        "width_bits": 20,
    },
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.samples < 1:
        parser.error("--samples must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    return args


def git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
    )
    return proc.stdout.strip()


def cpu_model() -> str | None:
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        for line in cpuinfo.read_text(encoding="utf-8").splitlines():
            if line.startswith("model name") and ":" in line:
                return line.split(":", 1)[1].strip()
    model = platform.processor().strip()
    return model or None


@functools.cache
def time_binary() -> str | None:
    candidates = [shutil.which("time"), "/usr/bin/time"]
    seen: set[str] = set()
    for candidate in candidates:
        if candidate is None or candidate in seen or not Path(candidate).is_file():
            continue
        seen.add(candidate)
        probe = subprocess.run(
            [candidate, "-f", RSS_MARKER + "%M", "true"],
            capture_output=True,
            text=True,
            check=False,
        )
        if probe.returncode == 0 and RSS_MARKER in probe.stderr:
            return candidate
    return None


def environment() -> dict[str, object]:
    return {
        "git_commit": git("rev-parse", "HEAD") or None,
        "git_dirty": bool(git("status", "--porcelain", "--untracked-files=no")),
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "architecture": platform.machine(),
        "cpu_model": cpu_model(),
        "python": platform.python_version(),
        "gnu_time": time_binary(),
    }


def probe_source(module: str) -> Path:
    return ROOT / "bench" / Path(*module.split(".")).with_suffix(".lean")


def provenance_sources() -> list[Path]:
    roots = [
        ROOT / "HexRealRoots",
        ROOT / "HexRealRootsMathlib",
        ROOT / "HexPolyZ",
        ROOT / "HexPolyZMathlib",
        ROOT / "bench" / "HexRealRootsMathlib",
    ]
    files = [
        ROOT / "HexRealRoots.lean",
        ROOT / "HexRealRootsMathlib.lean",
        ROOT / "HexPolyZ.lean",
        ROOT / "HexPolyZMathlib.lean",
        ROOT / "lakefile.lean",
        ROOT / "lake-manifest.json",
        ROOT / "lean-toolchain",
        Path(__file__).resolve(),
    ]
    for directory in roots:
        files.extend(directory.rglob("*.lean"))
    return sorted(set(path for path in files if path.is_file()))


def source_hashes() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in provenance_sources()
    }


def rotate(items: list[str], offset: int) -> list[str]:
    pivot = offset % len(items)
    return items[pivot:] + items[:pivot]


def module_prefixes(module: str) -> list[Path]:
    rel = Path(*module.split("."))
    return [BUILD / "lib" / "lean" / rel, BUILD / "ir" / rel]


def remove_module_outputs(module: str) -> None:
    for prefix in module_prefixes(module):
        if not prefix.parent.is_dir():
            continue
        for path in prefix.parent.glob(prefix.name + ".*"):
            if path.is_file():
                path.unlink()


def run_timed(
    command: list[str], timeout: float
) -> tuple[subprocess.CompletedProcess[str], int, int | None]:
    timer = time_binary()
    wrapped = command if timer is None else [
        timer, "-f", RSS_MARKER + "%M", *command
    ]
    start = time.perf_counter_ns()
    child = subprocess.Popen(
        wrapped,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGTERM)
        try:
            child.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.communicate()
        raise
    elapsed = time.perf_counter_ns() - start
    proc = subprocess.CompletedProcess(
        wrapped, child.returncode, stdout=stdout, stderr=stderr
    )
    rss = None
    if timer is not None:
        match = re.search(rf"{re.escape(RSS_MARKER)}(\d+)", proc.stderr)
        if match:
            rss = int(match.group(1))
    return proc, elapsed, rss


def parse_axioms(output: str) -> list[str] | None:
    match = re.search(r"depends on axioms: \[([^]]*)\]", output)
    if match:
        return [item.strip() for item in match.group(1).split(",") if item.strip()]
    if "does not depend on any axioms" in output:
        return []
    return None


def build_sample(module: str, timeout: float) -> dict[str, object]:
    remove_module_outputs(module)
    command = ["lake", "build", f"+{module}:olean"]
    try:
        proc, elapsed, rss = run_timed(command, timeout)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            f"probe timed out after {timeout:g}s: {' '.join(command)}"
        ) from exc
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        sys.stderr.write(output)
        raise RuntimeError(
            f"probe failed ({proc.returncode}): {' '.join(command)}"
        )
    return {
        "wall_nanos": elapsed,
        "peak_rss_kb": rss,
        "axioms": parse_axioms(output),
    }


def median(samples: list[dict[str, object]], key: str) -> int | None:
    values = [int(sample[key]) for sample in samples if sample.get(key) is not None]
    return int(statistics.median(values)) if values else None


def artifact_sizes(module: str) -> dict[str, int | None]:
    rel = Path(*module.split("."))
    paths = {
        "source": probe_source(module),
        "olean": BUILD / "lib" / "lean" / rel.with_suffix(".olean"),
        "olean_private":
            BUILD / "lib" / "lean" / rel.with_suffix(".olean.private"),
        "olean_server":
            BUILD / "lib" / "lean" / rel.with_suffix(".olean.server"),
        "ilean": BUILD / "lib" / "lean" / rel.with_suffix(".ilean"),
    }
    return {
        kind + "_bytes": path.stat().st_size if path.is_file() else None
        for kind, path in paths.items()
    }


def validate_axioms(rows: dict[str, list[dict[str, object]]]) -> None:
    for key, samples in rows.items():
        observed = [sample["axioms"] for sample in samples]
        if key == "baseline":
            if any(axioms is not None for axioms in observed):
                raise RuntimeError("the import-only baseline unexpectedly printed axioms")
            continue
        if any(axioms != EXPECTED_AXIOMS for axioms in observed):
            raise RuntimeError(
                f"{key} axiom set mismatch: expected {EXPECTED_AXIOMS}, got {observed}"
            )


def summarize(
    rows: dict[str, list[dict[str, object]]]
) -> dict[str, dict[str, object]]:
    baseline = rows["baseline"]
    summary: dict[str, dict[str, object]] = {}
    for key, case in CASES.items():
        samples = rows[key]
        result: dict[str, object] = {
            **case,
            "samples": samples,
            "median_wall_nanos": median(samples, "wall_nanos"),
            "median_peak_rss_kb": median(samples, "peak_rss_kb"),
            "artifacts": artifact_sizes(str(case["module"])),
        }
        if key != "baseline":
            margins = [
                int(sample["wall_nanos"]) - int(baseline[index]["wall_nanos"])
                for index, sample in enumerate(samples)
            ]
            result["signed_baseline_wall_margin_nanos"] = margins
            result["median_signed_baseline_wall_margin_nanos"] = int(
                statistics.median(margins)
            )
            result["axioms"] = EXPECTED_AXIOMS
        summary[key] = result
    return summary


def default_output(env: dict[str, object]) -> Path:
    commit = str(env["git_commit"] or "unknown")[:12]
    host = re.sub(r"[^A-Za-z0-9_.-]+", "-", str(env["hostname"]))
    return (
        ROOT / "reports" / "bench-results" /
        f"hex-real-roots-mathlib-{commit}-{host}.json"
    )


def main() -> int:
    args = parse_args()
    env = environment()
    before = source_hashes()
    keys = list(CASES)
    rows: dict[str, list[dict[str, object]]] = {key: [] for key in keys}

    for round_index in range(args.samples):
        for key in rotate(keys, round_index):
            module = str(CASES[key]["module"])
            print(
                f"[{round_index + 1}/{args.samples}] {key} ({module})",
                flush=True,
            )
            rows[key].append(build_sample(module, args.timeout))

    after = source_hashes()
    if after != before:
        raise RuntimeError("measurement sources changed during the sweep")
    validate_axioms(rows)

    record = {
        "schema": "hex-real-roots-mathlib-proof-probe-v1",
        "measurement": (
            "fresh-module end-to-end elaboration, compiled certificate search, "
            "literal elaboration, and ordinary kernel checking"
        ),
        "environment": env,
        "config": {
            "samples": args.samples,
            "timeout_seconds": args.timeout,
            "command_template": "lake build +<module>:olean",
            "order": keys,
            "rotation": "left by round index",
        },
        "results": summarize(rows),
        "source_sha256": before,
    }
    output = args.output or default_output(env)
    if not output.is_absolute():
        output = ROOT / output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(output.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main())
