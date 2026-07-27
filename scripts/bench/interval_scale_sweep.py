#!/usr/bin/env python3
"""Measure compiled construction and replay of interval scaling workloads.

Each timed driver invocation contains exactly one workload family, size, and
mode. Every mode is calibrated independently, and deterministic coprime-stride
orders spread each case across the full sample run. The harness calls Lean only
through Lake and never uses ``native_decide``.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import math
import os
import platform
import re
import shutil
import socket
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / ".lake" / "build"
SPIKE = BUILD / "bin" / "hex_interval_scale_spike"
RSS_MARKER = "__HEX_MAX_RSS_KB__="

LADDERS: dict[str, list[int]] = {
    "dead-nodes": [9, 20, 50, 100, 500, 2000],
    "adjacent": [1, 11, 41, 91, 491],
    "far": [1, 11, 41, 91, 491],
    "source-pad": [0, 10, 40, 90, 490],
}
MODES = ["build", "accept", "below", "bad-tail", "early"]

PROBE_MODULES = {
    "replay_baseline": "HexInterval.ReplayScaleBaseline",
    "replay_checked": "HexInterval.ReplayScaleChecked",
    "whnf_baseline": "HexInterval.WhnfScaleBaseline",
    "whnf_checked": "HexInterval.WhnfScaleChecked",
}
PROBE_SOURCES = {
    "HexInterval.ReplayScaleBaseline":
        ROOT / "bench" / "HexInterval" / "ReplayScaleBaseline.lean",
    "HexInterval.ReplayScaleChecked":
        ROOT / "bench" / "HexInterval" / "ReplayScaleChecked.lean",
    "HexInterval.WhnfScaleBaseline":
        ROOT / "bench" / "HexInterval" / "WhnfScaleBaseline.lean",
    "HexInterval.WhnfScaleChecked":
        ROOT / "bench" / "HexInterval" / "WhnfScaleChecked.lean",
}
AXIOM_REPORT_MODULES = {
    "HexInterval.ReplayScaleBaseline",
    "HexInterval.ReplayScaleChecked",
}
WHNF_FAMILY_TO_KIND = {
    "dead": "dead-nodes",
    "adjacent": "adjacent",
    "far": "far",
    "sourcePad": "source-pad",
}
WHNF_MARKER_RE = re.compile(
    r"__HEX_SCALE_WHNF__\s+family=([^\s]+)\s+size=(\d+)\s+nanos=(\d+)"
)

PROVENANCE_SOURCES = [
    ROOT / "HexInterval.lean",
    ROOT / "HexInterval" / "Basic.lean",
    ROOT / "HexInterval" / "Experiment" / "Center.lean",
    ROOT / "HexInterval" / "Experiment" / "Scale.lean",
    ROOT / "bench" / "HexBench" / "IntervalScaleSpike.lean",
    ROOT / "conformance" / "HexInterval" / "ScaleConformance.lean",
    ROOT / "lakefile.lean",
    ROOT / "lake-manifest.json",
    ROOT / "lean-toolchain",
    *PROBE_SOURCES.values(),
    Path(__file__).resolve(),
]


@dataclass(frozen=True)
class Case:
    kind: str
    size: int
    mode: str

    @property
    def key(self) -> str:
        return f"{self.kind}/{self.size}/{self.mode}"


@dataclass(frozen=True)
class Point:
    kind: str
    size: int

    @property
    def key(self) -> str:
        return f"{self.kind}/{self.size}"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument(
        "--target-ms",
        type=float,
        default=250.0,
        help="target inner duration for adaptive repeat calibration",
    )
    parser.add_argument(
        "--calibration-tolerance",
        type=float,
        default=0.20,
        help="accepted relative error around --target-ms",
    )
    parser.add_argument("--max-calibration-rounds", type=int, default=8)
    parser.add_argument("--max-repeats", type=int, default=100_000_000)
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="use an already-built scale executable",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "reports" / "bench-results" /
        "hex-interval-scale.json",
    )
    return parser.parse_args()


def git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
    )
    return proc.stdout.strip()


def relevant_git_status() -> list[str]:
    """Return dirty entries, ignoring only the worktree-local build link."""
    lines = git("status", "--porcelain", "--untracked-files=all").splitlines()
    return [
        line for line in lines
        if line[3:] != ".lake" and not line[3:].startswith(".lake/")
    ]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_hashes() -> dict[str, str]:
    missing = [path for path in PROVENANCE_SOURCES if not path.is_file()]
    if missing:
        raise SystemExit(
            "missing provenance input(s): " + ", ".join(map(str, missing))
        )
    return {
        str(path.relative_to(ROOT)): sha256(path)
        for path in sorted(set(PROVENANCE_SOURCES))
    }


@functools.cache
def time_binary() -> str | None:
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
        matches = re.findall(rf"{re.escape(RSS_MARKER)}(\d+)", proc.stderr)
        if matches:
            rss = int(matches[-1])
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


def module_prefixes(module: str) -> list[Path]:
    rel = Path(*module.split("."))
    return [BUILD / "lib" / "lean" / rel, BUILD / "ir" / rel]


def remove_module_outputs(module: str) -> None:
    """Remove only artifacts whose basename is exactly this module stem."""
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


def parse_axioms(module: str, output: str) -> list[str] | None:
    reports: list[list[str]] = []
    for match in re.finditer(r"depends on axioms: \[([^]]*)\]", output):
        reports.append([
            item.strip() for item in match.group(1).split(",") if item.strip()
        ])
    if re.search(r"does not depend on any axioms", output):
        reports.append([])
    if not reports:
        if module in AXIOM_REPORT_MODULES:
            raise SystemExit(f"missing required axiom report for {module}")
        return None
    canonical = reports[0]
    if any(report != canonical for report in reports[1:]):
        raise SystemExit(f"inconsistent axiom reports for {module}: {reports}")
    return canonical


def expected_whnf_points() -> set[tuple[str, int]]:
    return {
        (kind, size)
        for kind, ladder in LADDERS.items()
        for size in ladder
    }


def parse_whnf_cases(module: str, output: str) -> list[dict[str, object]]:
    cases: list[dict[str, object]] = []
    seen: set[tuple[str, int]] = set()
    for family, size_text, nanos_text in WHNF_MARKER_RE.findall(output):
        kind = WHNF_FAMILY_TO_KIND.get(family)
        if kind is None:
            raise SystemExit(f"unknown WHNF family from {module}: {family}")
        size = int(size_text)
        point = (kind, size)
        if point in seen:
            raise SystemExit(f"duplicate WHNF point from {module}: {point}")
        seen.add(point)
        cases.append({
            "family": family,
            "kind": kind,
            "size": size,
            "nanos": int(nanos_text),
        })
    expected = expected_whnf_points()
    if module == PROBE_MODULES["whnf_checked"]:
        if seen != expected or len(cases) != len(expected):
            missing = sorted(expected - seen)
            extra = sorted(seen - expected)
            raise SystemExit(
                f"WHNF point mismatch for {module}: expected {len(expected)}, "
                f"got {len(cases)}, missing={missing}, extra={extra}"
            )
    elif cases:
        raise SystemExit(f"unexpected WHNF markers from baseline module {module}")
    return cases


def probe_sample(module: str) -> dict[str, object]:
    remove_module_outputs(module)
    wall, rss, output = build_module(module)
    axioms = parse_axioms(module, output)
    whnf_cases = parse_whnf_cases(module, output)
    if module in AXIOM_REPORT_MODULES and axioms is None:
        raise SystemExit(f"required axiom field is null for {module}")
    if module not in AXIOM_REPORT_MODULES and axioms is not None:
        raise SystemExit(f"unexpected axiom report from WHNF command module {module}")
    return {
        "wall_nanos": wall,
        "peak_rss_kb": rss,
        "axioms": axioms,
        "whnf_cases": whnf_cases,
    }


def paired_probe_samples(
    baseline_module: str, checked_module: str, sample_count: int
) -> dict[str, list[dict[str, object]]]:
    modules = [baseline_module, checked_module]
    rows: dict[str, list[dict[str, object]]] = {
        baseline_module: [],
        checked_module: [],
    }
    for sample_index in range(sample_count):
        pivot = sample_index % len(modules)
        order = modules[pivot:] + modules[:pivot]
        for module in order:
            rows[module].append(probe_sample(module))
    return rows


def signed_wall_margins(
    candidate: list[dict[str, object]], baseline: list[dict[str, object]]
) -> list[int]:
    if len(candidate) != len(baseline):
        raise SystemExit("paired probe sample counts differ")
    return [
        int(candidate[index]["wall_nanos"]) -
        int(baseline[index]["wall_nanos"])
        for index in range(len(candidate))
    ]


def stable_axioms(module: str, samples: list[dict[str, object]]) -> list[str] | None:
    values = [sample["axioms"] for sample in samples]
    if any(value != values[0] for value in values[1:]):
        raise SystemExit(f"unstable axiom set for {module}: {values}")
    return values[0]


def probe_pair_summary(
    baseline_module: str,
    checked_module: str,
    rows: dict[str, list[dict[str, object]]],
) -> dict[str, object]:
    baseline = rows[baseline_module]
    checked = rows[checked_module]
    margins = signed_wall_margins(checked, baseline)
    return {
        "baseline": {
            "module": baseline_module,
            "samples": baseline,
            "axioms": stable_axioms(baseline_module, baseline),
            "median_wall_nanos": median(baseline, "wall_nanos"),
            "median_peak_rss_kb": median(baseline, "peak_rss_kb"),
        },
        "checked": {
            "module": checked_module,
            "samples": checked,
            "axioms": stable_axioms(checked_module, checked),
            "median_wall_nanos": median(checked, "wall_nanos"),
            "median_peak_rss_kb": median(checked, "peak_rss_kb"),
            "signed_baseline_wall_margin_nanos": margins,
            "median_signed_baseline_wall_margin_nanos":
                statistics.median(margins),
        },
    }


def whnf_case_summary(
    checked_samples: list[dict[str, object]],
) -> list[dict[str, object]]:
    by_point: dict[tuple[str, int], list[int]] = {
        point: [] for point in expected_whnf_points()
    }
    for sample in checked_samples:
        cases = sample["whnf_cases"]
        if not isinstance(cases, list):
            raise SystemExit("malformed WHNF sample cases")
        for case in cases:
            point = (str(case["kind"]), int(case["size"]))
            by_point[point].append(int(case["nanos"]))
    result: list[dict[str, object]] = []
    for kind, ladder in LADDERS.items():
        for size in ladder:
            samples = by_point[(kind, size)]
            if len(samples) != len(checked_samples):
                raise SystemExit(
                    f"incomplete WHNF samples for {kind}/{size}: {samples}"
                )
            result.append({
                "kind": kind,
                "size": size,
                "samples_nanos": samples,
                "median_nanos": statistics.median(samples),
            })
    return result


def artifact_record(path: Path) -> dict[str, object]:
    if not path.is_file():
        return {"path": str(path.relative_to(ROOT)), "bytes": None, "sha256": None}
    return {
        "path": str(path.relative_to(ROOT)),
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def module_artifacts(module: str) -> dict[str, object]:
    rel = Path(*module.split("."))
    exported_object = BUILD / "ir" / rel.with_suffix(".c.o.export")
    plain_object = BUILD / "ir" / rel.with_suffix(".c.o")
    object_path = exported_object if exported_object.is_file() else plain_object
    return {
        "module": module,
        "source": artifact_record(PROBE_SOURCES[module]),
        "olean": artifact_record(BUILD / "lib" / "lean" / rel.with_suffix(".olean")),
        "olean_private": artifact_record(
            BUILD / "lib" / "lean" / rel.with_suffix(".olean.private")
        ),
        "olean_server": artifact_record(
            BUILD / "lib" / "lean" / rel.with_suffix(".olean.server")
        ),
        "ilean": artifact_record(BUILD / "lib" / "lean" / rel.with_suffix(".ilean")),
        "c": artifact_record(BUILD / "ir" / rel.with_suffix(".c")),
        "object": artifact_record(object_path),
    }


def expected_counters(kind: str, size: int, mode: str) -> dict[str, object]:
    if kind == "dead-nodes":
        if size < 9:
            raise ValueError("dead-nodes size must be at least 9")
        result = {
            "nodes": size,
            "facts": 10,
            "lookup_steps": 74,
            "lookup_counts": {
                "program": 44,
                "source": 1,
                "edge": 1,
                "prior": 18,
                "result": 10,
            },
        }
    elif kind == "adjacent":
        if size < 1 or size % 2 != 1:
            raise ValueError("adjacent size must be a positive odd number")
        result = {
            "nodes": 9,
            "facts": 9 + size,
            "lookup_steps": 71 + 3 * size,
            "lookup_counts": {
                "program": 44,
                "source": 1,
                "edge": size,
                "prior": 17 + size,
                "result": 9 + size,
            },
        }
    elif kind == "far":
        if size < 1:
            raise ValueError("far size must be positive")
        result = {
            "nodes": 9,
            "facts": 9 + size,
            "lookup_steps": 71 + size * (size + 5) // 2,
            "lookup_counts": {
                "program": 44,
                "source": 1,
                "edge": size,
                "prior": 17 + size * (size + 1) // 2,
                "result": 9 + size,
            },
        }
    elif kind == "source-pad":
        result = {
            "nodes": 9,
            "facts": 10 + size,
            "lookup_steps": 74 + size,
            "lookup_counts": {
                "program": 44,
                "source": 1 + size,
                "edge": 1,
                "prior": 18,
                "result": 10,
            },
        }
    else:
        raise ValueError(f"unknown workload kind: {kind}")
    if mode == "early" and kind != "dead-nodes":
        result["facts"] = int(result["facts"]) + 1
        result["lookup_steps"] = int(result["lookup_steps"]) + 1
        counts = dict(result["lookup_counts"])
        counts["source"] += 1
        result["lookup_counts"] = counts
    return result


def parse_driver_output(
    case: Case, repeats: int, stdout: str
) -> dict[str, object]:
    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if not lines:
        raise SystemExit(f"missing spike output for {case.key}")
    fields = lines[-1].split()
    if len(fields) != 15:
        raise SystemExit(
            f"unexpected spike output for {case.key}: {lines[-1]!r}"
        )
    expected_tag = "build" if case.mode == "build" else "check"
    if fields[0] != expected_tag or fields[1] != case.kind:
        raise SystemExit(
            f"spike identity mismatch for {case.key}: {lines[-1]!r}"
        )
    try:
        observed_size = int(fields[2])
        observed_mode = fields[3]
        nodes = int(fields[4])
        facts = int(fields[5])
        lookup_steps = int(fields[6])
        observed_repeats = int(fields[7])
        inner_nanos = int(fields[8])
        checksum = int(fields[9])
        lookup_counts = {
            "program": int(fields[10]),
            "source": int(fields[11]),
            "edge": int(fields[12]),
            "prior": int(fields[13]),
            "result": int(fields[14]),
        }
    except ValueError as error:
        raise SystemExit(
            f"non-integer spike output for {case.key}: {lines[-1]!r}"
        ) from error
    if observed_size != case.size or observed_mode != case.mode:
        raise SystemExit(
            f"spike point mismatch for {case.key}: {lines[-1]!r}"
        )
    if observed_repeats != repeats:
        raise SystemExit(
            f"spike repeat mismatch for {case.key}: "
            f"expected {repeats}, got {observed_repeats}"
        )
    expected = expected_counters(case.kind, case.size, case.mode)
    actual = {
        "nodes": nodes,
        "facts": facts,
        "lookup_steps": lookup_steps,
        "lookup_counts": lookup_counts,
    }
    if actual != expected:
        raise SystemExit(
            f"counter mismatch for {case.key}: expected {expected}, got {actual}"
        )
    lookup_sum = sum(lookup_counts.values())
    if lookup_sum != lookup_steps:
        raise SystemExit(
            f"lookup-count mismatch for {case.key}: components sum to "
            f"{lookup_sum}, total is {lookup_steps}"
        )
    return {
        **actual,
        "inner_total_nanos": inner_nanos,
        "per_call_nanos": inner_nanos / repeats,
        "checksum": checksum,
        "driver_output": lines[-1],
    }


def driver_sample(case: Case, repeats: int) -> dict[str, object]:
    command = [str(SPIKE), case.kind, str(case.size), case.mode, str(repeats)]
    proc, outer, rss = run_timed(command)
    require_success(proc, command)
    parsed = parse_driver_output(case, repeats, proc.stdout)
    return {
        **parsed,
        "outer_wall_nanos": outer,
        "peak_rss_kb": rss,
    }


def counters_of(sample: dict[str, object]) -> dict[str, object]:
    return {
        "nodes": sample["nodes"],
        "facts": sample["facts"],
        "lookup_steps": sample["lookup_steps"],
        "lookup_counts": sample["lookup_counts"],
    }


def assert_case_counters(
    case_counters: dict[str, dict[str, object]],
    case: Case,
    sample: dict[str, object],
) -> None:
    observed = counters_of(sample)
    previous = case_counters.setdefault(case.key, observed)
    if previous != observed:
        raise SystemExit(
            f"unstable counters for {case.key}: {previous} != {observed}"
        )


def proposed_repeats(
    repeats: int, inner_nanos: int, target_nanos: int, max_repeats: int
) -> int:
    if inner_nanos <= 0:
        return min(max_repeats, max(repeats + 1, repeats * 10))
    estimate = max(1, round(repeats * target_nanos / inner_nanos))
    lower = max(1, repeats // 10)
    upper = min(max_repeats, max(repeats + 1, repeats * 100))
    return min(upper, max(lower, estimate))


def calibrate(
    case: Case,
    target_nanos: int,
    tolerance: float,
    rounds: int,
    max_repeats: int,
    case_counters: dict[str, dict[str, object]],
) -> tuple[int, list[dict[str, object]], str]:
    repeats = 1
    measured_repeats = repeats
    trials: list[dict[str, object]] = []
    status = "round-limit"
    for _ in range(rounds):
        sample = driver_sample(case, repeats)
        measured_repeats = repeats
        assert_case_counters(case_counters, case, sample)
        trials.append({"repeats": repeats, **sample})
        inner = int(sample["inner_total_nanos"])
        if target_nanos == 0 or abs(inner - target_nanos) <= target_nanos * tolerance:
            status = "within-tolerance"
            break
        if repeats == 1 and inner > target_nanos:
            status = "single-call-over-target"
            break
        next_repeats = proposed_repeats(
            repeats, inner, target_nanos, max_repeats
        )
        if next_repeats == repeats:
            status = "repeat-limit"
            break
        repeats = next_repeats
    return measured_repeats, trials, status


def balanced_order(
    items: list[Case], sample_index: int, sample_count: int
) -> list[Case]:
    """Deterministically spread every case across the run and mix neighbors."""
    count = len(items)
    stride = max(1, count // 2)
    while math.gcd(stride, count) != 1:
        stride -= 1
    offset = sample_index * count // sample_count
    return [items[(offset + position * stride) % count] for position in range(count)]


def median(samples: list[dict[str, object]], key: str) -> int | float | None:
    values = [sample[key] for sample in samples if sample.get(key) is not None]
    return statistics.median(values) if values else None


def cpu_model() -> str | None:
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        for line in cpuinfo.read_text(errors="replace").splitlines():
            if line.startswith("model name") and ":" in line:
                return line.split(":", 1)[1].strip()
    return platform.processor() or None


def memory_total_kb() -> int | None:
    meminfo = Path("/proc/meminfo")
    if meminfo.is_file():
        match = re.search(r"^MemTotal:\s+(\d+)\s+kB$", meminfo.read_text(), re.M)
        if match:
            return int(match.group(1))
    return None


def command_version(command: list[str]) -> str | None:
    proc = subprocess.run(
        command, cwd=ROOT, capture_output=True, text=True, check=False
    )
    if proc.returncode != 0:
        return None
    output = (proc.stdout or proc.stderr).strip()
    return output.splitlines()[0] if output else None


def environment() -> dict[str, object]:
    dirty = relevant_git_status()
    return {
        "git_commit": git("rev-parse", "HEAD") or None,
        "git_branch": git("branch", "--show-current") or None,
        "git_dirty": bool(dirty),
        "git_status": dirty,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lake_version": command_version(["lake", "--version"]),
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "cpu_model": cpu_model(),
        "logical_cpus": os.cpu_count(),
        "memory_total_kb": memory_total_kb(),
        "python": platform.python_version(),
        "gnu_time": time_binary(),
        "lake_no_cache": os.environ.get("LAKE_NO_CACHE"),
        "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
    }


def main() -> int:
    args = parse_args()
    if args.samples < 1:
        raise SystemExit("--samples must be positive")
    if args.target_ms <= 0:
        raise SystemExit("--target-ms must be positive")
    if not 0 <= args.calibration_tolerance < 1:
        raise SystemExit("--calibration-tolerance must lie in [0, 1)")
    if args.max_calibration_rounds < 1:
        raise SystemExit("--max-calibration-rounds must be positive")
    if args.max_repeats < 1:
        raise SystemExit("--max-repeats must be positive")

    input_hashes = source_hashes()
    if not args.skip_build:
        build = [
            "lake", "build", "HexIntervalExperiment",
            "hex_interval_scale_spike",
            "+HexInterval.ReplayScaleBaseline:olean",
            "+HexInterval.WhnfScaleBaseline:olean",
        ]
        proc = subprocess.run(build, cwd=ROOT, capture_output=True, text=True)
        require_success(proc, build)
    if source_hashes() != input_hashes:
        raise SystemExit("measurement inputs changed during the initial build")
    if not SPIKE.is_file():
        raise SystemExit(f"missing scale executable: {SPIKE}")
    initial_binary = {
        "path": str(SPIKE.relative_to(ROOT)),
        "bytes": SPIKE.stat().st_size,
        "sha256": sha256(SPIKE),
    }
    initial_environment = environment()

    target_nanos = round(args.target_ms * 1_000_000)
    points = [
        Point(kind, size)
        for kind, ladder in LADDERS.items()
        for size in ladder
    ]
    case_counters: dict[str, dict[str, object]] = {}
    calibration: dict[str, dict[str, object]] = {}
    repeats_by_case: dict[str, int] = {}

    # Each mode calibrates independently so fast rejection controls retain the
    # same timing signal as full construction and replay.
    for point in points:
        calibration[point.key] = {}
        for mode in MODES:
            case = Case(point.kind, point.size, mode)
            repeats, trials, status = calibrate(
                case,
                target_nanos,
                args.calibration_tolerance,
                args.max_calibration_rounds,
                args.max_repeats,
                case_counters,
            )
            calibration[point.key][mode] = {
                "selected_repeats": repeats,
                "status": status,
                "trials": trials,
            }
            repeats_by_case[case.key] = repeats

    cases = [
        Case(point.kind, point.size, mode)
        for point in points
        for mode in MODES
    ]
    raw: dict[str, list[dict[str, object]]] = {case.key: [] for case in cases}
    sample_order: list[list[str]] = []
    for sample_index in range(args.samples):
        order = balanced_order(cases, sample_index, args.samples)
        sample_order.append([case.key for case in order])
        for case in order:
            sample = driver_sample(case, repeats_by_case[case.key])
            assert_case_counters(case_counters, case, sample)
            raw[case.key].append(sample)

    measurements: list[dict[str, object]] = []
    for case in cases:
        samples = raw[case.key]
        checksums = {sample["checksum"] for sample in samples}
        if len(checksums) != 1:
            raise SystemExit(
                f"unstable checksum for {case.key}: {sorted(checksums)}"
            )
        measurements.append({
            "kind": case.kind,
            "size": case.size,
            "mode": case.mode,
            "repeats": repeats_by_case[case.key],
            "counters": case_counters[case.key],
            "samples": samples,
            "median_inner_total_nanos": median(samples, "inner_total_nanos"),
            "median_per_call_nanos": median(samples, "per_call_nanos"),
            "median_outer_wall_nanos": median(samples, "outer_wall_nanos"),
            "median_peak_rss_kb": median(samples, "peak_rss_kb"),
            "checksum": next(iter(checksums)),
        })

    replay_rows = paired_probe_samples(
        PROBE_MODULES["replay_baseline"],
        PROBE_MODULES["replay_checked"],
        args.samples,
    )
    replay = probe_pair_summary(
        PROBE_MODULES["replay_baseline"],
        PROBE_MODULES["replay_checked"],
        replay_rows,
    )
    whnf_rows = paired_probe_samples(
        PROBE_MODULES["whnf_baseline"],
        PROBE_MODULES["whnf_checked"],
        args.samples,
    )
    whnf = probe_pair_summary(
        PROBE_MODULES["whnf_baseline"],
        PROBE_MODULES["whnf_checked"],
        whnf_rows,
    )
    whnf["cases"] = whnf_case_summary(
        whnf_rows[PROBE_MODULES["whnf_checked"]]
    )

    # Materialize the code-generation facets only after fresh-module timing;
    # artifact generation must not make a timed probe appear up to date.
    for module in PROBE_MODULES.values():
        build_module(module, "c.o")
    probe_artifacts = {
        key: module_artifacts(module)
        for key, module in PROBE_MODULES.items()
    }

    final_hashes = source_hashes()
    if final_hashes != input_hashes:
        raise SystemExit("measurement inputs changed during the sweep")
    final_binary = {
        "path": str(SPIKE.relative_to(ROOT)),
        "bytes": SPIKE.stat().st_size,
        "sha256": sha256(SPIKE),
    }
    if final_binary != initial_binary:
        raise SystemExit("scale executable changed during the sweep")

    report = {
        "schema": "hex-interval-scale-v3",
        "environment": initial_environment,
        "config": {
            "samples": args.samples,
            "target_inner_nanos": target_nanos,
            "calibration_tolerance": args.calibration_tolerance,
            "max_calibration_rounds": args.max_calibration_rounds,
            "max_repeats": args.max_repeats,
            "ladders": LADDERS,
            "modes": MODES,
            "independent_repeats_per_mode": True,
            "one_point_per_process": True,
            "checker_limits_precomputed": True,
            "both_parity_outcomes_asserted": True,
            "sample_order": "balanced deterministic coprime stride",
            "early_fact_control":
                "append one valid irrelevant fact, then cap at the base length",
            "compiled_driver": str(SPIKE.relative_to(ROOT)),
            "kernel_proof":
                "ordinary decide +kernel and forced Lean.Kernel.whnf; "
                "native_decide forbidden",
            "source_sha256": input_hashes,
            "source_sha256_after": final_hashes,
            "source_hashes_unchanged": True,
            "initial_build_skipped": args.skip_build,
        },
        "binary": initial_binary,
        "case_counters": case_counters,
        "calibration": calibration,
        "sample_order": sample_order,
        "measurements": measurements,
        "ordinary_kernel_replay": replay,
        "forced_kernel_whnf": whnf,
        "probe_artifacts": probe_artifacts,
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
