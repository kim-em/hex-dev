#!/usr/bin/env python3
"""Measure the D2 bundled-versus-checked interval representation spike.

The compiled half runs one candidate per process through the dedicated spike
executable.  The replay half removes only the exact artifacts for one committed
probe module and rebuilds that module with ``lake build``.  This gives a fresh
ordinary-kernel replay while keeping its already-built imports warm, and avoids
calling ``lean`` directly or relying on ``native_decide``.

The output is diagnostic evidence, not a Phase-4 LeanBench result.  Kernel
reduction is explicitly outside LeanBench's measurement contract.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import os
import platform
import re
import shutil
import socket
import statistics
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / ".lake" / "build"
SPIKE = BUILD / "bin" / "hex_interval_representation_spike"
RSS_MARKER = "__HEX_MAX_RSS_KB__="

REPLAY_MODULES = {
    "baseline": "HexInterval.ReplayBaseline",
    "bundled": "HexInterval.ReplayBundled",
    "checked": "HexInterval.ReplayChecked",
    "import_bundled": "HexInterval.ImportBundled",
    "import_checked": "HexInterval.ImportChecked",
    "whnf_bundled": "HexInterval.WhnfBundled",
    "whnf_checked": "HexInterval.WhnfChecked",
    "whnf_baseline": "HexInterval.WhnfBaseline",
    "rational_baseline": "HexInterval.ReplayRationalBaseline",
    "rational_direct": "HexInterval.ReplayRationalDirect",
    "rational_checked": "HexInterval.ReplayRationalChecked",
    "rational_ops": "HexInterval.ReplayRational",
    "whnf_rational_direct": "HexInterval.WhnfRationalDirect",
    "whnf_rational_checked": "HexInterval.WhnfRationalChecked",
    "whnf_rational_baseline": "HexInterval.WhnfRationalBaseline",
}

MODULE_SOURCES = {
    "HexInterval.ReplayBaseline": ROOT / "bench" / "HexInterval" / "ReplayBaseline.lean",
    "HexInterval.ReplayBundled": ROOT / "bench" / "HexInterval" / "ReplayBundled.lean",
    "HexInterval.ReplayChecked": ROOT / "bench" / "HexInterval" / "ReplayChecked.lean",
    "HexInterval.ImportBundled": ROOT / "bench" / "HexInterval" / "ImportBundled.lean",
    "HexInterval.ImportChecked": ROOT / "bench" / "HexInterval" / "ImportChecked.lean",
    "HexInterval.WhnfBundled": ROOT / "bench" / "HexInterval" / "WhnfBundled.lean",
    "HexInterval.WhnfChecked": ROOT / "bench" / "HexInterval" / "WhnfChecked.lean",
    "HexInterval.WhnfBaseline": ROOT / "bench" / "HexInterval" / "WhnfBaseline.lean",
    "HexInterval.ReplayRationalBaseline":
        ROOT / "bench" / "HexInterval" / "ReplayRationalBaseline.lean",
    "HexInterval.ReplayRationalDirect":
        ROOT / "bench" / "HexInterval" / "ReplayRationalDirect.lean",
    "HexInterval.ReplayRationalChecked":
        ROOT / "bench" / "HexInterval" / "ReplayRationalChecked.lean",
    "HexInterval.ReplayRational":
        ROOT / "bench" / "HexInterval" / "ReplayRational.lean",
    "HexInterval.WhnfRationalDirect":
        ROOT / "bench" / "HexInterval" / "WhnfRationalDirect.lean",
    "HexInterval.WhnfRationalChecked":
        ROOT / "bench" / "HexInterval" / "WhnfRationalChecked.lean",
    "HexInterval.WhnfRationalBaseline":
        ROOT / "bench" / "HexInterval" / "WhnfRationalBaseline.lean",
}

PROVENANCE_SOURCES = [
    ROOT / "HexInterval.lean",
    ROOT / "HexInterval" / "Basic.lean",
    ROOT / "HexInterval" / "Experiment" / "Representation.lean",
    ROOT / "HexInterval" / "Experiment" / "Rational.lean",
    ROOT / "bench" / "HexBench" / "IntervalRepresentationSpike.lean",
    ROOT / "lakefile.lean",
    ROOT / "lake-manifest.json",
    ROOT / "lean-toolchain",
    Path(__file__).resolve(),
    *MODULE_SOURCES.values(),
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--sizes", type=int, nargs="+", default=[433, 4096])
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "reports" / "bench-results" /
        "hex-interval-d2-representation.json",
    )
    return parser.parse_args()


def git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
    )
    return proc.stdout.strip()


def environment() -> dict[str, object]:
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    return {
        "git_commit": git("rev-parse", "HEAD") or None,
        "git_dirty": bool(git("status", "--porcelain")),
        "toolchain": toolchain,
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "python": platform.python_version(),
    }


def source_hashes() -> dict[str, str]:
    """Hash every source that can affect a recorded measurement."""
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(set(PROVENANCE_SOURCES))
    }


@functools.cache
def time_binary() -> str | None:
    """Find a `time` implementation that actually accepts GNU's `-f`."""
    candidates = [
        shutil.which("time"),
        "/usr/bin/time",
        "/run/current-system/sw/bin/time",
    ]
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


def run_timed(command: list[str]) -> tuple[subprocess.CompletedProcess[str], int, int | None]:
    timer = time_binary()
    wrapped = command
    if timer is not None:
        wrapped = [timer, "-f", RSS_MARKER + "%M", *command]
    start = time.perf_counter_ns()
    proc = subprocess.run(wrapped, cwd=ROOT, capture_output=True, text=True)
    elapsed = time.perf_counter_ns() - start
    rss = None
    if timer is not None:
        match = re.search(rf"{re.escape(RSS_MARKER)}(\d+)", proc.stderr)
        if match:
            rss = int(match.group(1))
    return proc, elapsed, rss


def require_success(proc: subprocess.CompletedProcess[str], command: list[str]) -> None:
    if proc.returncode == 0:
        return
    sys.stderr.write(proc.stdout)
    sys.stderr.write(proc.stderr)
    raise SystemExit(f"command failed ({proc.returncode}): {' '.join(command)}")


def compiled_sample(variant: str, n: int, repeats: int) -> dict[str, int | None]:
    command = [str(SPIKE), variant, str(n), str(repeats)]
    proc, elapsed, rss = run_timed(command)
    require_success(proc, command)
    fields = proc.stdout.strip().splitlines()[-1].split()
    if len(fields) != 5 or fields[0] != variant:
        raise SystemExit(f"unexpected spike output: {proc.stdout!r}")
    return {
        "outer_wall_nanos": elapsed,
        "inner_total_nanos": int(fields[3]),
        "per_call_nanos": int(fields[3]) // repeats,
        "checksum": int(fields[4]),
        "peak_rss_kb": rss,
    }


def module_prefixes(module: str) -> list[Path]:
    rel = Path(*module.split("."))
    return [BUILD / "lib" / "lean" / rel, BUILD / "ir" / rel]


def remove_module_outputs(module: str) -> None:
    """Remove only artifacts whose basename is exactly this module's stem."""
    for prefix in module_prefixes(module):
        parent = prefix.parent
        if not parent.is_dir():
            continue
        for path in parent.glob(prefix.name + ".*"):
            if path.is_file():
                path.unlink()


def build_module(module: str, facet: str = "olean") -> tuple[int, int | None, str]:
    command = ["lake", "build", f"+{module}:{facet}"]
    proc, elapsed, rss = run_timed(command)
    require_success(proc, command)
    return elapsed, rss, proc.stdout + proc.stderr


def replay_sample(module: str) -> dict[str, object]:
    remove_module_outputs(module)
    elapsed, rss, output = build_module(module)
    axioms: list[str] = []
    match = re.search(r"depends on axioms: \[([^]]*)\]", output)
    if match:
        axioms = [item.strip() for item in match.group(1).split(",") if item.strip()]
    whnf_match = re.search(r"__HEX_WHNF_NANOS__=(\d+)", output)
    whnf_nanos = int(whnf_match.group(1)) if whnf_match else None
    return {
        "wall_nanos": elapsed,
        "peak_rss_kb": rss,
        "axioms": axioms,
        "whnf_nanos": whnf_nanos,
    }


def artifact_sizes(module: str) -> dict[str, int | None]:
    rel = Path(*module.split("."))
    object_path = BUILD / "ir" / rel.with_suffix(".c.o.export")
    if not object_path.is_file():
        object_path = BUILD / "ir" / rel.with_suffix(".c.o")
    paths = {
        "source": MODULE_SOURCES[module],
        "olean": BUILD / "lib" / "lean" / rel.with_suffix(".olean"),
        "ilean": BUILD / "lib" / "lean" / rel.with_suffix(".ilean"),
        "c": BUILD / "ir" / rel.with_suffix(".c"),
        "object": object_path,
    }
    return {
        kind + "_bytes": path.stat().st_size if path.is_file() else None
        for kind, path in paths.items()
    }


def summarize(samples: list[dict[str, object]], key: str) -> int | None:
    values = [sample[key] for sample in samples if sample.get(key) is not None]
    return int(statistics.median(values)) if values else None


def rotate(items: list[str], offset: int) -> list[str]:
    pivot = offset % len(items)
    return items[pivot:] + items[:pivot]


def replay_samples(keys: list[str], samples: int) -> dict[str, list[dict[str, object]]]:
    """Interleave modules so machine-load drift is not confounded with encoding."""
    rows: dict[str, list[dict[str, object]]] = {key: [] for key in keys}
    for sample_index in range(samples):
        for key in rotate(keys, sample_index):
            rows[key].append(replay_sample(REPLAY_MODULES[key]))
    return rows


def main() -> int:
    args = parse_args()
    if args.samples < 1:
        raise SystemExit("--samples must be positive")

    build = [
        "lake", "build", "HexInterval", "hex_interval_representation_spike",
        "+HexInterval.ReplayBaseline:olean",
        "+HexInterval.ReplayRationalBaseline:olean",
    ]
    proc = subprocess.run(build, cwd=ROOT, capture_output=True, text=True)
    require_success(proc, build)

    compiled: dict[str, object] = {}
    variants = ["bundled", "checked", "bundled-boundary", "checked-boundary"]
    for n in args.sizes:
        repeats = max(25, 2_000_000 // max(1, n))
        variant_rows: dict[str, list[dict[str, int | None]]] = {
            variant: [] for variant in variants
        }
        for sample_index in range(args.samples):
            for variant in rotate(variants, sample_index):
                variant_rows[variant].append(compiled_sample(variant, n, repeats))
        for variant in variants:
            key = f"{variant}:{n}"
            rows = variant_rows[variant]
            compiled[key] = {
                "variant": variant,
                "n": n,
                "repeats": repeats,
                "samples": rows,
                "median_per_call_nanos": summarize(rows, "per_call_nanos"),
                "median_peak_rss_kb": summarize(rows, "peak_rss_kb"),
            }

    replay: dict[str, object] = {}
    representation_keys = [
        "baseline", "bundled", "checked", "import_bundled", "import_checked",
        "whnf_bundled", "whnf_checked", "whnf_baseline",
    ]
    representation_rows = replay_samples(representation_keys, args.samples)
    baseline_rows = representation_rows["baseline"]
    replay["baseline"] = {
        "module": REPLAY_MODULES["baseline"],
        "samples": baseline_rows,
        "median_wall_nanos": summarize(baseline_rows, "wall_nanos"),
        "median_peak_rss_kb": summarize(baseline_rows, "peak_rss_kb"),
    }

    for variant in ("bundled", "checked"):
        module = REPLAY_MODULES[variant]
        rows = representation_rows[variant]
        median = summarize(rows, "wall_nanos")
        baseline = summarize(baseline_rows, "wall_nanos")
        replay[variant] = {
            "module": module,
            "samples": rows,
            "median_wall_nanos": median,
            "median_import_baseline_subtracted_nanos":
                median - baseline if median is not None and baseline is not None else None,
            "median_peak_rss_kb": summarize(rows, "peak_rss_kb"),
        }

        import_key = "import_" + variant
        import_module = REPLAY_MODULES[import_key]
        import_rows = representation_rows[import_key]
        replay[import_key] = {
            "module": import_module,
            "samples": import_rows,
            "median_wall_nanos": summarize(import_rows, "wall_nanos"),
            "median_import_baseline_subtracted_nanos":
                summarize(import_rows, "wall_nanos") - baseline
            if summarize(import_rows, "wall_nanos") is not None
                 and baseline is not None else None,
            "median_peak_rss_kb": summarize(import_rows, "peak_rss_kb"),
        }

        whnf_key = "whnf_" + variant
        whnf_module = REPLAY_MODULES[whnf_key]
        whnf_rows = representation_rows[whnf_key]
        whnf_median = summarize(whnf_rows, "wall_nanos")
        whnf_baseline = summarize(
            representation_rows["whnf_baseline"], "wall_nanos"
        )
        replay[whnf_key] = {
            "module": whnf_module,
            "samples": whnf_rows,
            "median_wall_nanos": whnf_median,
            "median_import_baseline_subtracted_nanos":
                whnf_median - whnf_baseline
                if whnf_median is not None and whnf_baseline is not None else None,
            "median_peak_rss_kb": summarize(whnf_rows, "peak_rss_kb"),
            "median_whnf_nanos": summarize(whnf_rows, "whnf_nanos"),
        }

    whnf_baseline_rows = representation_rows["whnf_baseline"]
    replay["whnf_baseline"] = {
        "module": REPLAY_MODULES["whnf_baseline"],
        "samples": whnf_baseline_rows,
        "median_wall_nanos": summarize(whnf_baseline_rows, "wall_nanos"),
        "median_peak_rss_kb": summarize(whnf_baseline_rows, "peak_rss_kb"),
    }

    rational_keys = [
        "rational_baseline", "rational_direct", "rational_checked",
        "rational_ops", "whnf_rational_direct", "whnf_rational_checked",
        "whnf_rational_baseline",
    ]
    rational_rows = replay_samples(rational_keys, args.samples)
    rational_baseline_rows = rational_rows["rational_baseline"]
    rational_baseline = summarize(rational_baseline_rows, "wall_nanos")
    replay["rational_baseline"] = {
        "module": REPLAY_MODULES["rational_baseline"],
        "samples": rational_baseline_rows,
        "median_wall_nanos": rational_baseline,
        "median_peak_rss_kb": summarize(rational_baseline_rows, "peak_rss_kb"),
    }

    for variant in ("rational_direct", "rational_checked", "rational_ops"):
        module = REPLAY_MODULES[variant]
        rows = rational_rows[variant]
        median = summarize(rows, "wall_nanos")
        replay[variant] = {
            "module": module,
            "samples": rows,
            "median_wall_nanos": median,
            "median_import_baseline_subtracted_nanos":
                median - rational_baseline
                if median is not None and rational_baseline is not None else None,
            "median_peak_rss_kb": summarize(rows, "peak_rss_kb"),
        }

    for variant in ("whnf_rational_direct", "whnf_rational_checked"):
        module = REPLAY_MODULES[variant]
        rows = rational_rows[variant]
        median = summarize(rows, "wall_nanos")
        whnf_rational_baseline = summarize(
            rational_rows["whnf_rational_baseline"], "wall_nanos"
        )
        replay[variant] = {
            "module": module,
            "samples": rows,
            "median_wall_nanos": median,
            "median_import_baseline_subtracted_nanos":
                median - whnf_rational_baseline
                if median is not None and whnf_rational_baseline is not None else None,
            "median_peak_rss_kb": summarize(rows, "peak_rss_kb"),
            "median_whnf_nanos": summarize(rows, "whnf_nanos"),
        }

    whnf_rational_baseline_rows = rational_rows["whnf_rational_baseline"]
    replay["whnf_rational_baseline"] = {
        "module": REPLAY_MODULES["whnf_rational_baseline"],
        "samples": whnf_rational_baseline_rows,
        "median_wall_nanos": summarize(
            whnf_rational_baseline_rows, "wall_nanos"
        ),
        "median_peak_rss_kb": summarize(
            whnf_rational_baseline_rows, "peak_rss_kb"
        ),
    }

    for module in REPLAY_MODULES.values():
        build_module(module, "c.o")

    artifacts = {
        name: artifact_sizes(module) for name, module in REPLAY_MODULES.items()
    }
    report = {
        "schema": "hex-interval-d2-representation-v2",
        "environment": environment(),
        "config": {
            "samples": args.samples,
            "sizes": args.sizes,
            "source_sha256": source_hashes(),
            "compiled_driver": str(SPIKE.relative_to(ROOT)),
            "kernel_proof": "ordinary decide +kernel; native_decide forbidden",
        },
        "compiled": compiled,
        "replay": replay,
        "artifacts": artifacts,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    shown = args.output.relative_to(ROOT) if args.output.is_relative_to(ROOT) else args.output
    print(shown)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
