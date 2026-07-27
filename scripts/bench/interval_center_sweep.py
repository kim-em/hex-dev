#!/usr/bin/env python3
"""Measure the D2 centered-product checker spike.

Compiled samples run one checker variant per process. Replay samples remove
only the exact outputs of one committed probe module and rebuild it through
Lake, keeping imports warm while forcing ordinary kernel replay. This harness
never calls Lean directly and never uses ``native_decide``.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
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
SPIKE = BUILD / "bin" / "hex_interval_center_spike"
RSS_MARKER = "__HEX_MAX_RSS_KB__="

COMPILED_VARIANTS = [
    "accepted",
    "lookup-budget",
    "missing-edge",
    "unused-literal",
]

REPLAY_MODULES = {
    "baseline": "HexInterval.ReplayCenterBaseline",
    "checked": "HexInterval.ReplayCenterChecked",
    "whnf_baseline": "HexInterval.WhnfCenterBaseline",
    "whnf_checked": "HexInterval.WhnfCenterChecked",
    "semantic_baseline": "HexIntervalMathlib.CenterBaseline",
    "semantic_reflected": "HexIntervalMathlib.CenterReflected",
    "semantic_direct": "HexIntervalMathlib.CenterDirect",
}

MODULE_SOURCES = {
    "HexInterval.ReplayCenterBaseline":
        ROOT / "bench" / "HexInterval" / "ReplayCenterBaseline.lean",
    "HexInterval.ReplayCenterChecked":
        ROOT / "bench" / "HexInterval" / "ReplayCenterChecked.lean",
    "HexInterval.WhnfCenterBaseline":
        ROOT / "bench" / "HexInterval" / "WhnfCenterBaseline.lean",
    "HexInterval.WhnfCenterChecked":
        ROOT / "bench" / "HexInterval" / "WhnfCenterChecked.lean",
    "HexIntervalMathlib.CenterBaseline":
        ROOT / "bench" / "HexIntervalMathlib" / "CenterBaseline.lean",
    "HexIntervalMathlib.CenterReflected":
        ROOT / "bench" / "HexIntervalMathlib" / "CenterReflected.lean",
    "HexIntervalMathlib.CenterDirect":
        ROOT / "bench" / "HexIntervalMathlib" / "CenterDirect.lean",
}

PROVENANCE_SOURCES = [
    ROOT / "HexInterval.lean",
    ROOT / "HexInterval" / "Basic.lean",
    ROOT / "HexInterval" / "Experiment" / "Center.lean",
    ROOT / "HexIntervalMathlib" / "Experiment" / "Center.lean",
    ROOT / "bench" / "HexBench" / "IntervalCenterSpike.lean",
    ROOT / "lakefile.lean",
    ROOT / "lake-manifest.json",
    ROOT / "lean-toolchain",
    Path(__file__).resolve(),
    *MODULE_SOURCES.values(),
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--repeats", type=int, default=100_000)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "reports" / "bench-results" /
        "hex-interval-d2-center.json",
    )
    return parser.parse_args()


def git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
    )
    return proc.stdout.strip()


def environment() -> dict[str, object]:
    return {
        "git_commit": git("rev-parse", "HEAD") or None,
        "git_dirty": bool(
            git("status", "--porcelain", "--untracked-files=no")
        ),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "gnu_time": time_binary(),
    }


def source_hashes() -> dict[str, str]:
    """Hash every repository input that can influence this measurement."""
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(set(PROVENANCE_SOURCES))
    }


@functools.cache
def time_binary() -> str | None:
    """Find a `time` implementation that demonstrably supports GNU `-f`."""
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


def run_timed(
    command: list[str],
) -> tuple[subprocess.CompletedProcess[str], int, int | None]:
    timer = time_binary()
    wrapped = command if timer is None else [
        timer, "-f", RSS_MARKER + "%M", *command
    ]
    start = time.perf_counter_ns()
    proc = subprocess.run(wrapped, cwd=ROOT, capture_output=True, text=True)
    elapsed = time.perf_counter_ns() - start
    rss = None
    if timer is not None:
        match = re.search(rf"{re.escape(RSS_MARKER)}(\d+)", proc.stderr)
        if match:
            rss = int(match.group(1))
    return proc, elapsed, rss


def require_success(
    proc: subprocess.CompletedProcess[str], command: list[str]
) -> None:
    if proc.returncode == 0:
        return
    sys.stderr.write(proc.stdout)
    sys.stderr.write(proc.stderr)
    raise SystemExit(
        f"command failed ({proc.returncode}): {' '.join(command)}"
    )


def rotate(items: list[str], offset: int) -> list[str]:
    pivot = offset % len(items)
    return items[pivot:] + items[:pivot]


def median(
    samples: list[dict[str, object]], key: str
) -> int | None:
    values = [sample[key] for sample in samples if sample.get(key) is not None]
    return int(statistics.median(values)) if values else None


def compiled_sample(variant: str, repeats: int) -> dict[str, int | None]:
    command = [str(SPIKE), variant, str(repeats)]
    proc, elapsed, rss = run_timed(command)
    require_success(proc, command)
    fields = proc.stdout.strip().splitlines()[-1].split()
    if len(fields) != 4 or fields[0] != variant:
        raise SystemExit(f"unexpected spike output: {proc.stdout!r}")
    observed_repeats = int(fields[1])
    if observed_repeats != repeats:
        raise SystemExit(f"spike repeat mismatch: {proc.stdout!r}")
    inner = int(fields[2])
    return {
        "outer_wall_nanos": elapsed,
        "inner_total_nanos": inner,
        "per_call_nanos": inner // repeats,
        "checksum": int(fields[3]),
        "peak_rss_kb": rss,
    }


def module_prefixes(module: str) -> list[Path]:
    rel = Path(*module.split("."))
    return [BUILD / "lib" / "lean" / rel, BUILD / "ir" / rel]


def remove_module_outputs(module: str) -> None:
    """Remove artifacts whose basename is exactly the selected module stem."""
    for prefix in module_prefixes(module):
        if not prefix.parent.is_dir():
            continue
        for path in prefix.parent.glob(prefix.name + ".*"):
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
    return {
        "wall_nanos": elapsed,
        "peak_rss_kb": rss,
        "axioms": axioms,
        "whnf_nanos": int(whnf_match.group(1)) if whnf_match else None,
    }


def replay_samples(
    keys: list[str], sample_count: int
) -> dict[str, list[dict[str, object]]]:
    rows: dict[str, list[dict[str, object]]] = {key: [] for key in keys}
    for sample_index in range(sample_count):
        for key in rotate(keys, sample_index):
            rows[key].append(replay_sample(REPLAY_MODULES[key]))
    return rows


def signed_margins(
    candidate: list[dict[str, object]], baseline: list[dict[str, object]]
) -> list[int]:
    return [
        int(candidate[index]["wall_nanos"]) -
        int(baseline[index]["wall_nanos"])
        for index in range(len(candidate))
    ]


def artifact_sizes(module: str) -> dict[str, int | None]:
    rel = Path(*module.split("."))
    exported_object = BUILD / "ir" / rel.with_suffix(".c.o.export")
    plain_object = BUILD / "ir" / rel.with_suffix(".c.o")
    object_path = exported_object if exported_object.is_file() else plain_object
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


def replay_summary(
    rows: dict[str, list[dict[str, object]]]
) -> dict[str, object]:
    baseline = rows["baseline"]
    checked = rows["checked"]
    whnf_baseline = rows["whnf_baseline"]
    whnf_checked = rows["whnf_checked"]
    replay_margin = signed_margins(checked, baseline)
    whnf_margin = signed_margins(whnf_checked, whnf_baseline)
    return {
        "baseline": {
            "module": REPLAY_MODULES["baseline"],
            "samples": baseline,
            "median_wall_nanos": median(baseline, "wall_nanos"),
            "median_peak_rss_kb": median(baseline, "peak_rss_kb"),
        },
        "checked": {
            "module": REPLAY_MODULES["checked"],
            "samples": checked,
            "median_wall_nanos": median(checked, "wall_nanos"),
            "signed_import_baseline_wall_margin_nanos": replay_margin,
            "median_signed_import_baseline_wall_margin_nanos":
                int(statistics.median(replay_margin)),
            "median_peak_rss_kb": median(checked, "peak_rss_kb"),
        },
        "whnf_baseline": {
            "module": REPLAY_MODULES["whnf_baseline"],
            "samples": whnf_baseline,
            "median_wall_nanos": median(whnf_baseline, "wall_nanos"),
            "median_peak_rss_kb": median(whnf_baseline, "peak_rss_kb"),
        },
        "whnf_checked": {
            "module": REPLAY_MODULES["whnf_checked"],
            "samples": whnf_checked,
            "median_wall_nanos": median(whnf_checked, "wall_nanos"),
            "signed_import_baseline_wall_margin_nanos": whnf_margin,
            "median_signed_import_baseline_wall_margin_nanos":
                int(statistics.median(whnf_margin)),
            "median_whnf_nanos": median(whnf_checked, "whnf_nanos"),
            "median_peak_rss_kb": median(whnf_checked, "peak_rss_kb"),
        },
    }


def semantic_summary(
    rows: dict[str, list[dict[str, object]]]
) -> dict[str, object]:
    """Compare both semantic proofs to the same import-matched baseline."""
    baseline = rows["semantic_baseline"]
    result: dict[str, object] = {
        "baseline": {
            "module": REPLAY_MODULES["semantic_baseline"],
            "samples": baseline,
            "median_wall_nanos": median(baseline, "wall_nanos"),
            "median_peak_rss_kb": median(baseline, "peak_rss_kb"),
        }
    }
    for variant in ("reflected", "direct"):
        key = "semantic_" + variant
        candidate = rows[key]
        margins = signed_margins(candidate, baseline)
        result[variant] = {
            "module": REPLAY_MODULES[key],
            "samples": candidate,
            "median_wall_nanos": median(candidate, "wall_nanos"),
            "signed_import_baseline_wall_margin_nanos": margins,
            "median_signed_import_baseline_wall_margin_nanos":
                int(statistics.median(margins)),
            "median_peak_rss_kb": median(candidate, "peak_rss_kb"),
        }
    return result


def main() -> int:
    args = parse_args()
    if args.samples < 1:
        raise SystemExit("--samples must be positive")
    if args.repeats < 1:
        raise SystemExit("--repeats must be positive")

    input_hashes = source_hashes()

    build = [
        "lake", "build", "HexIntervalExperiment",
        "HexIntervalMathlibExperiment",
        "hex_interval_center_spike",
        "+HexInterval.ReplayCenterBaseline:olean",
        "+HexInterval.WhnfCenterBaseline:olean",
        "+HexIntervalMathlib.CenterBaseline:olean",
        "+HexIntervalMathlib.CenterReflected:olean",
        "+HexIntervalMathlib.CenterDirect:olean",
    ]
    proc = subprocess.run(build, cwd=ROOT, capture_output=True, text=True)
    require_success(proc, build)

    compiled_rows: dict[str, list[dict[str, int | None]]] = {
        variant: [] for variant in COMPILED_VARIANTS
    }
    for sample_index in range(args.samples):
        for variant in rotate(COMPILED_VARIANTS, sample_index):
            compiled_rows[variant].append(compiled_sample(variant, args.repeats))

    compiled: dict[str, object] = {}
    for variant, rows in compiled_rows.items():
        checksums = {row["checksum"] for row in rows}
        if len(checksums) != 1:
            raise SystemExit(f"unstable checksum for {variant}: {checksums}")
        compiled[variant] = {
            "variant": variant,
            "repeats": args.repeats,
            "samples": rows,
            "median_per_call_nanos": median(rows, "per_call_nanos"),
            "median_peak_rss_kb": median(rows, "peak_rss_kb"),
        }

    replay_keys = ["baseline", "checked", "whnf_baseline", "whnf_checked"]
    replay_rows = replay_samples(replay_keys, args.samples)
    semantic_keys = [
        "semantic_baseline", "semantic_reflected", "semantic_direct",
    ]
    semantic_rows = replay_samples(semantic_keys, args.samples)

    for module in REPLAY_MODULES.values():
        build_module(module, "c.o")

    if source_hashes() != input_hashes:
        raise SystemExit("measurement inputs changed during the sweep")

    report = {
        "schema": "hex-interval-d2-center-v2",
        "environment": environment(),
        "config": {
            "samples": args.samples,
            "compiled_repeats": args.repeats,
            "compiled_driver": str(SPIKE.relative_to(ROOT)),
            "kernel_proof": "ordinary decide +kernel; native_decide forbidden",
            "source_sha256": input_hashes,
        },
        "compiled": compiled,
        "replay": replay_summary(replay_rows),
        "semantic": semantic_summary(semantic_rows),
        "artifacts": {
            key: artifact_sizes(module) for key, module in REPLAY_MODULES.items()
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    shown = (
        args.output.relative_to(ROOT)
        if args.output.is_relative_to(ROOT)
        else args.output
    )
    print(shown)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
