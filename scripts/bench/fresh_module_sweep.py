#!/usr/bin/env python3
"""Reusable external harness for matched fresh-module proof probes.

Each sample removes only one committed module's generated artifacts and
rebuilds its ``olean`` through Lake. A configured reference and candidate are
rebuilt adjacently, pair order rotates, and pair orientation alternates between
rounds. The harness records the raw pair as well as its signed wall-time
margin; it never embeds a clock in a Lean proof probe or turns elaboration into
a ``lean-bench`` registration.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import os
import platform
import re
import resource
import signal
import shutil
import socket
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence, TypeVar


ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / ".lake" / "build"
RSS_MARKER = "__HEX_MAX_RSS_KB__="
USER_MARKER = "__HEX_USER_SECONDS__="
SYSTEM_MARKER = "__HEX_SYSTEM_SECONDS__="
CPU_PERCENT_MARKER = "__HEX_CPU_PERCENT__="
INVOLUNTARY_CONTEXT_MARKER = "__HEX_INVOLUNTARY_CONTEXT__="
VOLUNTARY_CONTEXT_MARKER = "__HEX_VOLUNTARY_CONTEXT__="
DEFAULT_MAX_LOAD_PER_CPU = 0.5
DEFAULT_MAX_CORE_INTERFERENCE_RATIO = 0.002
DEFAULT_MAX_FREQUENCY_SPREAD_RATIO = 0.15
DEFAULT_MAX_PAIR_RETRIES = 8
MAX_PAIR_RETRIES = 8
DEFAULT_PREFLIGHT_WINDOW_SECONDS = 2.0
DEFAULT_PREFLIGHT_TIMEOUT_SECONDS = 300.0
PREFLIGHT_MAX_BUSY_TICKS = 2
NULL_MAGNITUDE_FACTOR = 3.0
MIN_CONTROL_MAGNITUDE_RATIO = 2.0
ACCOUNTING_QUANTIZATION_TICKS = 3
T = TypeVar("T")

sys.path.insert(0, str(ROOT))
from scripts.ci.check_benches_mathlib_free import (  # noqa: E402
    _ExeTarget,
    _parse_imports,
    _resolve_module,
)


@dataclass(frozen=True)
class ProbeModule:
    """One fresh module and the axiom output expected from its build."""

    module: str
    expected_axioms: tuple[str, ...] | None = None


@dataclass(frozen=True)
class ProbePair:
    """One adjacent reference/candidate comparison and its report metadata."""

    name: str
    reference: ProbeModule
    candidate: ProbeModule
    metadata: dict[str, object]
    null_control: bool = False


@dataclass(frozen=True)
class SweepSpec:
    """Declarative inputs that distinguish one proof-probe suite."""

    description: str
    pairs: tuple[ProbePair, ...]
    probe_target: str
    schema: str
    measurement: str
    output_stem: str
    src_dir: Path = Path("bench")
    extra_sources: tuple[Path, ...] = ()
    required_samples: int | None = None


def parse_args(
    description: str,
    argv: Sequence[str] | None = None,
    *,
    default_samples: int = 4,
) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--samples", type=int, default=default_samples)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--warm-timeout", type=float, default=600.0)
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--allow-dirty",
        action="store_true",
        help="permit dirty repository/package checkouts for diagnostic runs",
    )
    parser.add_argument(
        "--allow-busy",
        action="store_true",
        help="permit concurrent Lake/Lean work or a saturated host for diagnostics",
    )
    parser.add_argument(
        "--shared-host",
        action="store_true",
        help=(
            "use the release-quality designated-shared-host protocol; requires "
            "single-CPU affinity, at least two null controls, and at least "
            "six balanced samples"
        ),
    )
    parser.add_argument(
        "--expected-host",
        help="required hostname for the designated-shared-host protocol",
    )
    parser.add_argument(
        "--cpu",
        type=int,
        help="logical CPU to which the shared-host runner and children are pinned",
    )
    parser.add_argument(
        "--max-load-per-cpu",
        type=float,
        default=DEFAULT_MAX_LOAD_PER_CPU,
        help="maximum one-minute load average divided by logical CPU count",
    )
    parser.add_argument(
        "--max-core-interference-ratio",
        type=float,
        default=DEFAULT_MAX_CORE_INTERFERENCE_RATIO,
        help=(
            "maximum aggregate foreign busy-time fraction across the "
            "measurement CPU and its SMT siblings"
        ),
    )
    parser.add_argument(
        "--max-frequency-spread-ratio",
        type=float,
        default=DEFAULT_MAX_FREQUENCY_SPREAD_RATIO,
        help="maximum observed pinned-CPU frequency spread for shared-host evidence",
    )
    parser.add_argument(
        "--max-pair-retries",
        "--max-arm-retries",
        dest="max_pair_retries",
        type=int,
        default=DEFAULT_MAX_PAIR_RETRIES,
        help=(
            "maximum contaminated-pair retries under the shared-host "
            "protocol (default 8)"
        ),
    )
    parser.add_argument(
        "--preflight-window-seconds",
        type=float,
        default=DEFAULT_PREFLIGHT_WINDOW_SECONDS,
        help=(
            "quiet-core observation duration before each shared-host "
            "pair attempt"
        ),
    )
    parser.add_argument(
        "--preflight-timeout-seconds",
        type=float,
        default=DEFAULT_PREFLIGHT_TIMEOUT_SECONDS,
        help="maximum wait for a quiet physical-core window",
    )
    args = parser.parse_args(argv)
    if args.samples < 1:
        parser.error("--samples must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.warm_timeout <= 0:
        parser.error("--warm-timeout must be positive")
    if args.max_load_per_cpu <= 0:
        parser.error("--max-load-per-cpu must be positive")
    if not 0 < args.max_core_interference_ratio < 1:
        parser.error("--max-core-interference-ratio must be between 0 and 1")
    if not 0 < args.max_frequency_spread_ratio < 1:
        parser.error("--max-frequency-spread-ratio must be between 0 and 1")
    if not 0 <= args.max_pair_retries <= MAX_PAIR_RETRIES:
        parser.error(
            "--max-pair-retries/--max-arm-retries must be between "
            f"0 and {MAX_PAIR_RETRIES}"
        )
    if args.preflight_window_seconds <= 0:
        parser.error("--preflight-window-seconds must be positive")
    if args.preflight_timeout_seconds < args.preflight_window_seconds:
        parser.error(
            "--preflight-timeout-seconds must be at least one "
            "preflight window"
        )
    if args.allow_busy and args.shared_host:
        parser.error("--allow-busy and --shared-host are mutually exclusive")
    if args.cpu is not None and args.cpu < 0:
        parser.error("--cpu must be nonnegative")
    if args.shared_host and (
        args.expected_host is None or args.cpu is None
    ):
        parser.error("--shared-host requires both --expected-host and --cpu")
    if not args.shared_host and (
        args.expected_host is not None or args.cpu is not None
    ):
        parser.error("--expected-host/--cpu require --shared-host")
    return args


def _git_bytes(directory: Path, *args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", *args], cwd=directory, capture_output=True, check=False
    )


def _require_git(directory: Path, *args: str) -> bytes:
    proc = _git_bytes(directory, *args)
    if proc.returncode != 0:
        detail = proc.stderr.decode(errors="replace").strip()
        raise RuntimeError(
            f"git {' '.join(args)} failed in {directory}: {detail or 'no stderr'}"
        )
    return proc.stdout


def checkout_state(directory: Path) -> dict[str, object]:
    """Describe one actual Git checkout, including dirty worktree content."""
    head = _require_git(directory, "rev-parse", "HEAD").decode().strip()
    tree = _require_git(directory, "rev-parse", "HEAD^{tree}").decode().strip()
    status_bytes = _require_git(
        directory, "status", "--porcelain=v1", "-z", "--untracked-files=all"
    )
    digest = hashlib.sha256()
    digest.update(head.encode())
    digest.update(b"\0")
    digest.update(tree.encode())
    digest.update(b"\0")
    digest.update(status_bytes)
    for args in (("diff", "--binary", "HEAD"), ("diff", "--binary", "--cached")):
        digest.update(_require_git(directory, *args))
    untracked = _require_git(
        directory, "ls-files", "--others", "--exclude-standard", "-z"
    ).split(b"\0")
    for raw in sorted(path for path in untracked if path):
        path = directory / os.fsdecode(raw)
        digest.update(raw)
        digest.update(b"\0")
        if path.is_file():
            digest.update(path.read_bytes())

    return {
        "path": str(directory),
        "head": head,
        "tree": tree,
        "dirty": bool(status_bytes),
        "status": status_bytes.decode(errors="replace").replace("\0", "\n").strip(),
        "state_sha256": digest.hexdigest(),
    }


def dependency_checkouts() -> dict[str, dict[str, object]]:
    packages = ROOT / ".lake" / "packages"
    if not packages.is_dir():
        return {}
    return {
        path.name: checkout_state(path)
        for path in sorted(packages.iterdir())
        if path.is_dir()
    }


def lean_processes() -> list[dict[str, object]]:
    proc = subprocess.run(
        ["ps", "-eo", "pid=,args="], capture_output=True, text=True, check=False
    )
    if proc.returncode != 0:
        return []
    pattern = re.compile(r"(?:^|\s)(?:\S*/)?(?:lake|lean)(?:\s|$)")
    processes: list[dict[str, object]] = []
    for line in proc.stdout.splitlines():
        fields = line.strip().split(maxsplit=1)
        if len(fields) != 2 or not fields[0].isdigit():
            continue
        pid, command = int(fields[0]), fields[1]
        if pid != os.getpid() and pattern.search(command):
            processes.append({"pid": pid, "command": command})
    return processes


def cpu_affinity() -> list[int] | None:
    """Return the logical CPUs available to this runner, when supported."""
    get_affinity = getattr(os, "sched_getaffinity", None)
    if get_affinity is None:
        return None
    return sorted(get_affinity(0))


def _read_optional(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return None


def cpu_topology(cpu: int) -> dict[str, object]:
    """Describe the physical-core unit containing one logical CPU."""
    root = Path(f"/sys/devices/system/cpu/cpu{cpu}")
    topology = root / "topology"
    return {
        "logical_cpu": cpu,
        "core_id": _read_optional(topology / "core_id"),
        "physical_package_id": _read_optional(
            topology / "physical_package_id"
        ),
        "thread_siblings_list": _read_optional(
            topology / "thread_siblings_list"
        ),
        "scaling_governor": _read_optional(
            root / "cpufreq" / "scaling_governor"
        ),
        "scaling_cur_freq_khz": _read_optional(
            root / "cpufreq" / "scaling_cur_freq"
        ),
    }


def configure_shared_host(args: argparse.Namespace) -> None:
    """Pin this runner before warmup and verify the named release machine."""
    if not args.shared_host:
        return
    assert args.expected_host is not None
    assert args.cpu is not None
    actual_host = socket.gethostname()
    if actual_host != args.expected_host:
        raise RuntimeError(
            f"expected host {args.expected_host!r}, got {actual_host!r}"
        )
    set_affinity = getattr(os, "sched_setaffinity", None)
    if set_affinity is None:
        raise RuntimeError("CPU affinity is unavailable")
    try:
        set_affinity(0, {args.cpu})
    except OSError as exc:
        raise RuntimeError(f"cannot pin runner to CPU {args.cpu}: {exc}") from exc
    os.environ["LEAN_NUM_THREADS"] = "1"


def parse_cpu_list(text: str | None) -> list[int]:
    """Parse Linux cpulist syntax such as ``0-2,7``."""
    if not text:
        return []
    cpus: list[int] = []
    for part in text.split(","):
        bounds = part.split("-", 1)
        start = int(bounds[0])
        stop = int(bounds[-1])
        cpus.extend(range(start, stop + 1))
    return sorted(set(cpus))


def cpu_ticks(cpus: Sequence[int]) -> dict[int, dict[str, int]]:
    """Read per-logical-CPU scheduler counters from ``/proc/stat``."""
    wanted = set(cpus)
    result: dict[int, dict[str, int]] = {}
    fields = (
        "user", "nice", "system", "idle", "iowait", "irq", "softirq",
        "steal", "guest", "guest_nice",
    )
    try:
        lines = Path("/proc/stat").read_text(encoding="utf-8").splitlines()
    except OSError:
        return result
    for line in lines:
        columns = line.split()
        if not columns or not columns[0].startswith("cpu"):
            continue
        suffix = columns[0][3:]
        if not suffix.isdigit() or int(suffix) not in wanted:
            continue
        values = [int(value) for value in columns[1:]]
        result[int(suffix)] = dict(zip(fields, values, strict=False))
    return result


def frequency_residency(cpu: int | None) -> dict[int, int] | None:
    """Read cumulative cpufreq residency counters for one logical CPU."""
    if cpu is None:
        return None
    text = _read_optional(
        Path(
            f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/stats/time_in_state"
        )
    )
    if text is None:
        return None
    result: dict[int, int] = {}
    try:
        for line in text.splitlines():
            frequency, ticks = line.split()
            result[int(frequency)] = int(ticks)
    except (TypeError, ValueError):
        return None
    return result or None


def frequency_residency_delta(
    before: dict[int, int] | None,
    after: dict[int, int] | None,
) -> dict[int, int] | None:
    """Difference compatible cpufreq residency snapshots fail-closed."""
    if before is None or after is None or set(before) != set(after):
        return None
    delta = {
        frequency: after[frequency] - ticks
        for frequency, ticks in before.items()
    }
    if any(ticks < 0 for ticks in delta.values()):
        return None
    return delta


def mean_residency_frequency(
    delta: dict[int, int] | None,
) -> float | None:
    """Time-weighted mean kHz from a cpufreq residency delta."""
    if delta is None:
        return None
    total = sum(delta.values())
    if total <= 0:
        return None
    return sum(frequency * ticks for frequency, ticks in delta.items()) / total


def runner_cpu_seconds() -> float:
    """CPU consumed by this harness process itself."""
    usage = resource.getrusage(resource.RUSAGE_SELF)
    return float(usage.ru_utime + usage.ru_stime)


def reaped_children_cpu_seconds() -> tuple[float, float]:
    """Cumulative CPU of child processes already reaped by this runner."""
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return float(usage.ru_utime), float(usage.ru_stime)


def cpu_tick_delta(
    before: dict[int, dict[str, int]],
    after: dict[int, dict[str, int]],
    cpu: int,
) -> dict[str, int] | None:
    if cpu not in before or cpu not in after:
        return None
    return {
        field: after[cpu].get(field, 0) - value
        for field, value in before[cpu].items()
    }


def busy_ticks(delta: dict[str, int] | None) -> int | None:
    if delta is None:
        return None
    return sum(
        delta.get(field, 0)
        for field in ("user", "nice", "system", "irq", "softirq", "steal")
    )


def interrupt_ticks(delta: dict[str, int] | None) -> int | None:
    """Kernel interrupt time reported separately from process CPU time."""
    if delta is None:
        return None
    return delta.get("irq", 0) + delta.get("softirq", 0)


def noninterrupt_busy_ticks(delta: dict[str, int] | None) -> int | None:
    """Busy ticks attributable to processes or stolen virtual-CPU time."""
    if delta is None:
        return None
    return sum(
        delta.get(field, 0)
        for field in ("user", "nice", "system", "steal")
    )


def foreign_cpu_accounting(
    target_busy_seconds: float,
    child_cpu_seconds: float,
    runner_cpu_seconds_value: float,
    interrupt_seconds: float,
) -> tuple[float, float, float]:
    """Return raw, signed non-interrupt, and positive foreign CPU time."""
    raw_residual = (
        target_busy_seconds
        - child_cpu_seconds
        - runner_cpu_seconds_value
    )
    noninterrupt_residual = raw_residual - interrupt_seconds
    foreign = max(0.0, noninterrupt_residual)
    return raw_residual, noninterrupt_residual, foreign


def pressure_total_us(text: str | None) -> int | None:
    if text is None:
        return None
    match = re.search(r"^some .*?\btotal=(\d+)", text, flags=re.MULTILINE)
    return int(match.group(1)) if match else None


def host_state() -> dict[str, object]:
    cpus = os.cpu_count() or 1
    try:
        load = list(os.getloadavg())
    except OSError:
        load = []
    affinity = cpu_affinity()
    loadavg = _read_optional(Path("/proc/loadavg"))
    runnable = None
    if loadavg is not None:
        fields = loadavg.split()
        runnable = fields[3] if len(fields) > 3 else None
    pressure = _read_optional(Path("/proc/pressure/cpu"))
    available_cpus = len(affinity) if affinity is not None else None
    return {
        "logical_cpus": cpus,
        "available_logical_cpus": available_cpus,
        "load_average": load,
        "load_1m_per_cpu": load[0] / cpus if load else None,
        "load_1m_per_available_cpu": (
            load[0] / available_cpus
            if load and available_cpus is not None and available_cpus > 0
            else None
        ),
        "runnable_tasks": runnable,
        "cpu_affinity": affinity,
        "cpu_pressure": pressure,
        "cpu_pressure_some_total_us": pressure_total_us(pressure),
        "affinity_cpu_frequency_khz": (
            cpu_topology(affinity[0])["scaling_cur_freq_khz"]
            if affinity is not None and len(affinity) == 1
            else None
        ),
        "concurrent_lake_lean": lean_processes(),
    }


def host_issues(
    state: dict[str, object],
    max_load_per_cpu: float,
    *,
    concurrent_is_issue: bool = True,
    load_is_issue: bool = True,
) -> list[str]:
    issues: list[str] = []
    processes = state["concurrent_lake_lean"]
    if concurrent_is_issue and processes:
        issues.append(f"{len(processes)} concurrent Lake/Lean process(es)")
    load = state["load_1m_per_cpu"]
    if load_is_issue and load is not None and float(load) > max_load_per_cpu:
        issues.append(
            f"one-minute load/CPU {float(load):.3f} exceeds {max_load_per_cpu:.3f}"
        )
    return issues


def shared_host_protocol_issues(
    spec: SweepSpec, args: argparse.Namespace
) -> list[str]:
    """Check the preregistered controls for shared-host release evidence."""
    if not args.shared_host:
        return []
    issues: list[str] = []
    affinity = cpu_affinity()
    if affinity is None:
        issues.append("CPU affinity is unavailable")
    elif len(affinity) != 1:
        issues.append(
            "shared-host evidence requires exactly one affinity CPU, "
            f"got {affinity}"
        )
    elif args.cpu is not None and affinity != [args.cpu]:
        issues.append(
            f"observed affinity {affinity} does not match requested CPU {args.cpu}"
        )
    controls = [pair for pair in spec.pairs if pair.null_control]
    if len(controls) < 2:
        issues.append(
            "shared-host evidence requires at least two same-module null controls"
        )
    elif len({pair.reference.module for pair in controls}) < 2:
        issues.append("null controls must use at least two distinct magnitudes")
    first_substantive = next(
        (
            index for index, pair in enumerate(spec.pairs)
            if not pair.null_control
        ),
        len(spec.pairs),
    )
    if any(pair.null_control for pair in spec.pairs[first_substantive:]):
        issues.append("all null controls must precede substantive pairs")
    if not any(not pair.null_control for pair in spec.pairs):
        issues.append("shared-host evidence requires a substantive pair")
    if args.samples < 6 or args.samples % 2 != 0:
        issues.append(
            "shared-host evidence requires at least six and an even number "
            "of samples"
        )
    return issues


def sampled_host_state(state: dict[str, object]) -> dict[str, object]:
    """Compact host metadata retained around measured pairs and arms."""
    processes = list(state["concurrent_lake_lean"])
    return {
        "logical_cpus": state["logical_cpus"],
        "available_logical_cpus": state["available_logical_cpus"],
        "load_average": state["load_average"],
        "load_1m_per_cpu": state["load_1m_per_cpu"],
        "load_1m_per_available_cpu": state["load_1m_per_available_cpu"],
        "runnable_tasks": state["runnable_tasks"],
        "cpu_affinity": state["cpu_affinity"],
        "cpu_pressure": state["cpu_pressure"],
        "cpu_pressure_some_total_us": state["cpu_pressure_some_total_us"],
        "affinity_cpu_frequency_khz": state["affinity_cpu_frequency_khz"],
        "concurrent_lake_lean_count": len(processes),
    }


def dirty_issues(repository: dict[str, object],
                 dependencies: dict[str, dict[str, object]]) -> list[str]:
    issues: list[str] = []
    if repository.get("dirty"):
        issues.append("repository checkout is dirty")
    dirty_packages = [
        name for name, state in dependencies.items() if state.get("dirty")
    ]
    if dirty_packages:
        issues.append("dirty dependency checkout(s): " + ", ".join(dirty_packages))
    return issues


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
    repository = checkout_state(ROOT)
    dependencies = dependency_checkouts()
    return {
        "git_commit": repository.get("head"),
        "git_dirty": repository.get("dirty", True),
        "repository": repository,
        "dependency_checkouts": dependencies,
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "hostname": socket.gethostname(),
        "machine_id": _read_optional(Path("/etc/machine-id")),
        "platform": platform.platform(),
        "architecture": platform.machine(),
        "cpu_model": cpu_model(),
        "python": platform.python_version(),
        "gnu_time": time_binary(),
        "host_before": host_state(),
    }


def probe_source(module: str, src_dir: Path) -> Path:
    return ROOT / src_dir / Path(*module.split(".")).with_suffix(".lean")


def probe_modules(spec: SweepSpec) -> set[str]:
    return {
        module.module
        for pair in spec.pairs
        for module in (pair.reference, pair.candidate)
    }


def repo_source(
    module: str, target: _ExeTarget, package_root: Path
) -> Path | None:
    path = _resolve_module(module, target, ROOT)
    if path is None:
        return None
    path = path.resolve()
    try:
        path.relative_to(package_root.resolve())
    except ValueError:
        return path
    return None


def validate_spec(spec: SweepSpec) -> None:
    """Reject ambiguous pairs and import paths between measured modules."""
    names = [pair.name for pair in spec.pairs]
    if not names:
        raise RuntimeError("fresh-module sweep has no probe pairs")
    if len(names) != len(set(names)):
        raise RuntimeError("fresh-module sweep pair names must be unique")
    measured = probe_modules(spec)
    for pair in spec.pairs:
        identical = pair.reference == pair.candidate
        if pair.null_control and not identical:
            raise RuntimeError(
                f"{pair.name}: null control modules and axiom policies "
                "must be identical"
            )
        if not pair.null_control and pair.reference.module == pair.candidate.module:
            raise RuntimeError(f"{pair.name}: reference and candidate are identical")
    if spec.required_samples is not None and spec.required_samples < 1:
        raise RuntimeError("fresh-module sweep required_samples must be positive")
    target = _ExeTarget(spec.probe_target, "", spec.src_dir)
    package_root = ROOT / ".lake" / "packages"
    for root_module in measured:
        source = probe_source(root_module, spec.src_dir)
        if not source.is_file():
            raise RuntimeError(f"missing measured probe source: {source}")
        frontier = list(_parse_imports(source))
        visited: set[str] = set()
        while frontier:
            module = frontier.pop()
            if module in visited:
                continue
            visited.add(module)
            if module in measured:
                raise RuntimeError(
                    f"{root_module}: import closure reaches measured probe {module}"
                )
            path = repo_source(module, target, package_root)
            if path is not None:
                frontier.extend(_parse_imports(path))


def local_import_sources(spec: SweepSpec) -> set[Path]:
    """Return the complete repository-local import closure of every probe."""
    target = _ExeTarget(spec.probe_target, "", spec.src_dir)
    package_root = ROOT / ".lake" / "packages"
    frontier = list(probe_modules(spec))
    visited: set[str] = set()
    sources: set[Path] = set()
    while frontier:
        module = frontier.pop()
        if module in visited:
            continue
        visited.add(module)
        path = repo_source(module, target, package_root)
        if path is not None:
            sources.add(path)
            frontier.extend(_parse_imports(path))
    return sources


def provenance_sources(spec: SweepSpec, caller_file: Path) -> list[Path]:
    files = local_import_sources(spec) | {
        ROOT / "lakefile.lean",
        ROOT / "lake-manifest.json",
        ROOT / "lean-toolchain",
        Path(__file__).resolve(),
        caller_file.resolve(),
        ROOT / "scripts" / "ci" / "check_benches_mathlib_free.py",
    }
    extras = [
        path if path.is_absolute() else ROOT / path
        for path in spec.extra_sources
    ]
    missing = [path for path in extras if not path.is_file()]
    if missing:
        raise RuntimeError(
            "missing declared provenance source(s): "
            + ", ".join(str(path) for path in missing)
        )
    files.update(extras)
    return sorted(path for path in files if path.is_file())


def source_hashes(spec: SweepSpec, caller_file: Path) -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in provenance_sources(spec, caller_file)
    }


def rotate(items: list[T], offset: int) -> list[T]:
    pivot = offset % len(items)
    return items[pivot:] + items[:pivot]


def ordered_modules(
    pair: ProbePair, round_index: int
) -> list[tuple[str, ProbeModule]]:
    modules = [
        ("reference", pair.reference),
        ("candidate", pair.candidate),
    ]
    if round_index % 2 == 1:
        modules.reverse()
    return modules


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
) -> tuple[subprocess.CompletedProcess[str], int, dict[str, int | float | None]]:
    timer = time_binary()
    timer_format = "\n".join((
        RSS_MARKER + "%M",
        USER_MARKER + "%U",
        SYSTEM_MARKER + "%S",
        CPU_PERCENT_MARKER + "%P",
        INVOLUNTARY_CONTEXT_MARKER + "%c",
        VOLUNTARY_CONTEXT_MARKER + "%w",
    ))
    wrapped = command if timer is None else [
        timer, "-f", timer_format, *command
    ]
    children_cpu_before = reaped_children_cpu_seconds()
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
        terminate_process_group(child)
        raise
    elapsed = time.perf_counter_ns() - start
    children_cpu_after = reaped_children_cpu_seconds()
    proc = subprocess.CompletedProcess(
        wrapped, child.returncode, stdout=stdout, stderr=stderr
    )
    metrics: dict[str, int | float | None] = {
        "peak_rss_kb": None,
        "user_seconds": None,
        "system_seconds": None,
        "precise_child_user_seconds": (
            children_cpu_after[0] - children_cpu_before[0]
        ),
        "precise_child_system_seconds": (
            children_cpu_after[1] - children_cpu_before[1]
        ),
        "cpu_percent": None,
        "involuntary_context_switches": None,
        "voluntary_context_switches": None,
    }
    if timer is not None:
        integer_metrics = (
            (RSS_MARKER, "peak_rss_kb"),
            (INVOLUNTARY_CONTEXT_MARKER, "involuntary_context_switches"),
            (VOLUNTARY_CONTEXT_MARKER, "voluntary_context_switches"),
        )
        for marker, key in integer_metrics:
            match = re.search(rf"{re.escape(marker)}(\d+)", proc.stderr)
            if match:
                metrics[key] = int(match.group(1))
        float_metrics = (
            (USER_MARKER, "user_seconds"),
            (SYSTEM_MARKER, "system_seconds"),
            (CPU_PERCENT_MARKER, "cpu_percent"),
        )
        for marker, key in float_metrics:
            match = re.search(
                rf"{re.escape(marker)}([0-9]+(?:\.[0-9]+)?)", proc.stderr
            )
            if match:
                metrics[key] = float(match.group(1))
    return proc, elapsed, metrics


def terminate_process_group(child: subprocess.Popen[str], grace: float = 5.0) -> None:
    """Terminate a timed command and every descendant in its process group."""
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        child.communicate(timeout=grace)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    child.communicate()


def parse_axioms(output: str) -> list[str] | None:
    match = re.search(r"depends on axioms: \[([^]]*)\]", output)
    if match:
        return [item.strip() for item in match.group(1).split(",") if item.strip()]
    if "does not depend on any axioms" in output:
        return []
    return None


def build_sample(
    module: str,
    timeout: float,
    measurement_cpu: int | None = None,
    monitored_cpus: Sequence[int] = (),
) -> dict[str, object]:
    remove_module_outputs(module)
    host_before = sampled_host_state(host_state())
    ticks_before = cpu_ticks(monitored_cpus)
    runner_cpu_before = runner_cpu_seconds()
    frequency_before = frequency_residency(measurement_cpu)
    command = ["lake", "build", f"+{module}:olean"]
    try:
        proc, elapsed, metrics = run_timed(command, timeout)
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
    frequency_after = frequency_residency(measurement_cpu)
    runner_cpu_after = runner_cpu_seconds()
    ticks_after = cpu_ticks(monitored_cpus)
    host_after = sampled_host_state(host_state())
    tick_hz = int(os.sysconf("SC_CLK_TCK"))
    per_cpu: dict[str, dict[str, object]] = {}
    for cpu in monitored_cpus:
        delta = cpu_tick_delta(ticks_before, ticks_after, cpu)
        busy = busy_ticks(delta)
        per_cpu[str(cpu)] = {
            "ticks": delta,
            "busy_seconds": (
                float(busy) / tick_hz if busy is not None else None
            ),
        }
    child_cpu_seconds = None
    if (
        metrics["precise_child_user_seconds"] is not None
        and metrics["precise_child_system_seconds"] is not None
    ):
        child_cpu_seconds = (
            float(metrics["precise_child_user_seconds"])
            + float(metrics["precise_child_system_seconds"])
        )
    runner_seconds = runner_cpu_after - runner_cpu_before
    foreign_seconds = None
    residual_seconds = None
    noninterrupt_residual_seconds = None
    interrupt_seconds = None
    if measurement_cpu is not None and str(measurement_cpu) in per_cpu:
        target = per_cpu[str(measurement_cpu)]
        target_busy = target["busy_seconds"]
        target_interrupt_ticks = interrupt_ticks(target["ticks"])
        if target_interrupt_ticks is not None:
            interrupt_seconds = float(target_interrupt_ticks) / tick_hz
        if target_busy is not None and child_cpu_seconds is not None:
            (
                residual_seconds,
                noninterrupt_residual_seconds,
                foreign_seconds,
            ) = foreign_cpu_accounting(
                float(target_busy),
                child_cpu_seconds,
                runner_seconds,
                float(interrupt_seconds or 0.0),
            )
    pressure_before = host_before["cpu_pressure_some_total_us"]
    pressure_after = host_after["cpu_pressure_some_total_us"]
    frequency_delta = frequency_residency_delta(
        frequency_before, frequency_after
    )
    result = {
        "wall_nanos": elapsed,
        **metrics,
        "axioms": parse_axioms(output),
        "host_before": host_before,
        "host_after": host_after,
        "cpu_accounting": {
            "clock_ticks_per_second": tick_hz,
            "per_cpu": per_cpu,
            "child_cpu_seconds": child_cpu_seconds,
            "child_cpu_source": "getrusage-reaped-children",
            "runner_cpu_seconds": runner_seconds,
            "measurement_cpu_residual_seconds": residual_seconds,
            "measurement_cpu_interrupt_seconds": interrupt_seconds,
            "measurement_cpu_noninterrupt_residual_seconds":
                noninterrupt_residual_seconds,
            "measurement_cpu_foreign_seconds": foreign_seconds,
            "frequency_time_in_state_ticks": frequency_delta,
            "mean_frequency_khz": mean_residency_frequency(
                frequency_delta
            ),
            "pressure_some_delta_us": (
                int(pressure_after) - int(pressure_before)
                if pressure_before is not None and pressure_after is not None
                else None
            ),
        },
    }
    return result


def wait_for_shared_host_window(
    measurement_cpu: int,
    monitored_cpus: Sequence[int],
    sibling_cpus: Sequence[int],
    window_seconds: float,
    timeout_seconds: float,
) -> dict[str, object]:
    """Wait boundedly for a quiet physical-core window before a pair."""
    started = time.monotonic()
    rejected_windows: list[dict[str, object]] = []
    while True:
        before = cpu_ticks(monitored_cpus)
        time.sleep(window_seconds)
        after = cpu_ticks(monitored_cpus)
        per_cpu: dict[str, dict[str, object]] = {}
        issues: list[str] = []
        target_delta = cpu_tick_delta(
            before, after, measurement_cpu
        )
        target_busy = noninterrupt_busy_ticks(target_delta)
        per_cpu[str(measurement_cpu)] = {
            "ticks": target_delta,
            "noninterrupt_busy_ticks": target_busy,
        }
        if target_busy is None:
            issues.append("measurement-CPU preflight accounting is incomplete")
        elif target_busy > PREFLIGHT_MAX_BUSY_TICKS:
            issues.append(
                f"measurement CPU {measurement_cpu} had "
                f"{target_busy} non-interrupt busy ticks"
            )
        for sibling in sibling_cpus:
            delta = cpu_tick_delta(before, after, sibling)
            sibling_busy = busy_ticks(delta)
            per_cpu[str(sibling)] = {
                "ticks": delta,
                "busy_ticks": sibling_busy,
            }
            if sibling_busy is None:
                issues.append(
                    f"SMT sibling CPU {sibling} preflight accounting "
                    "is incomplete"
                )
            elif sibling_busy > PREFLIGHT_MAX_BUSY_TICKS:
                issues.append(
                    f"SMT sibling CPU {sibling} had "
                    f"{sibling_busy} busy ticks"
                )
        observation = {
            "window_seconds": window_seconds,
            "max_busy_ticks": PREFLIGHT_MAX_BUSY_TICKS,
            "per_cpu": per_cpu,
            "issues": issues,
        }
        elapsed = time.monotonic() - started
        if not issues:
            return {
                "admitted": True,
                "elapsed_seconds": elapsed,
                "rejected_windows": rejected_windows,
                "accepted_window": observation,
            }
        rejected_windows.append(observation)
        print(
            "[preflight wait] " + "; ".join(issues),
            flush=True,
        )
        if elapsed >= timeout_seconds:
            return {
                "admitted": False,
                "elapsed_seconds": elapsed,
                "rejected_windows": rejected_windows,
                "accepted_window": None,
                "issues": [
                    "shared-host physical core did not become quiet within "
                    f"{timeout_seconds:g}s"
                ],
            }


def shared_host_arm_issues(
    pair_name: str,
    round_index: int,
    role: str,
    arm: dict[str, object],
    measurement_cpu: int,
    sibling_cpus: Sequence[int],
    max_ratio: float,
) -> list[str]:
    """Validate one arm before admitting it to a shared-host pair."""
    prefix = f"{pair_name} round {round_index} {role}: "
    issues: list[str] = []
    wall_seconds = int(arm["wall_nanos"]) / 1_000_000_000
    accounting = dict(arm["cpu_accounting"])
    tick_hz = int(accounting.get("clock_ticks_per_second") or 0)
    if tick_hz <= 0 or wall_seconds <= 0:
        return [prefix + "per-arm CPU accounting is incomplete"]
    quantization_allowance = ACCOUNTING_QUANTIZATION_TICKS / tick_hz
    allowance = max(quantization_allowance, max_ratio * wall_seconds)
    residual = accounting.get(
        "measurement_cpu_noninterrupt_residual_seconds"
    )
    foreign = accounting.get("measurement_cpu_foreign_seconds")
    if residual is None or foreign is None:
        issues.append(prefix + "per-arm CPU accounting is incomplete")
    else:
        if float(residual) < -quantization_allowance:
            issues.append(
                prefix
                + "child CPU time exceeds pinned-CPU busy time by "
                + f"{-float(residual):.3f}s (allowance "
                + f"{quantization_allowance:.3f}s)"
            )
    cpu_percent = arm.get("cpu_percent")
    if (
        cpu_percent is not None
        and float(cpu_percent) > 100 * (1 + max_ratio)
    ):
        issues.append(
            prefix
            + f"child CPU utilisation {float(cpu_percent):.1f}% "
            + "exceeds the single-CPU affinity ceiling"
        )
    per_cpu = dict(accounting.get("per_cpu") or {})
    sibling_busy_seconds = 0.0
    for sibling in sibling_cpus:
        busy = dict(per_cpu.get(str(sibling), {})).get("busy_seconds")
        if busy is None:
            issues.append(
                prefix + f"SMT sibling CPU {sibling} accounting is incomplete"
            )
        else:
            sibling_busy_seconds += float(busy)
    if foreign is not None:
        aggregate_interference = float(foreign) + sibling_busy_seconds
        accounting["aggregate_core_interference_seconds"] = (
            aggregate_interference
        )
        arm["cpu_accounting"] = accounting
        if aggregate_interference > allowance:
            issues.append(
                prefix
                + "aggregate measurement-CPU foreign and SMT-sibling "
                + f"busy time {aggregate_interference:.3f}s exceeds "
                + f"{allowance:.3f}s"
            )
    mean_frequency = accounting.get("mean_frequency_khz")
    if mean_frequency is None or float(mean_frequency) <= 0:
        issues.append(prefix + "pinned-CPU frequency accounting is incomplete")
    return issues


def build_shared_host_pair(
    pair_name: str,
    round_index: int,
    slot_index: int,
    modules: Sequence[tuple[str, ProbeModule]],
    timeout: float,
    measurement_cpu: int,
    monitored_cpus: Sequence[int],
    sibling_cpus: Sequence[int],
    max_ratio: float,
    max_retries: int,
    preflight_window_seconds: float,
    preflight_timeout_seconds: float,
) -> tuple[
    dict[str, object] | None,
    list[dict[str, object]],
    dict[str, object] | None,
]:
    """Retry complete adjacent pairs and admit only wholly clean attempts."""
    rejected: list[dict[str, object]] = []
    for attempt in range(1, max_retries + 2):
        preflight = wait_for_shared_host_window(
            measurement_cpu,
            monitored_cpus,
            sibling_cpus,
            preflight_window_seconds,
            preflight_timeout_seconds,
        )
        if not preflight["admitted"]:
            return None, rejected, {
                "pair": pair_name,
                "round": round_index,
                "slot_index": slot_index,
                "attempt": attempt,
                "preflight": preflight,
                "issues": list(preflight["issues"]),
            }
        attempt_state = sampled_host_state(host_state())
        built: dict[str, dict[str, object]] = {}
        for role, module in modules:
            print(
                f"[pair attempt {attempt}/{max_retries + 1}] "
                f"{pair_name} {role} ({module.module})",
                flush=True,
            )
            built[role] = build_sample(
                module.module,
                timeout,
                measurement_cpu=measurement_cpu,
                monitored_cpus=monitored_cpus,
            )
            if cpu_affinity() != [measurement_cpu]:
                raise RuntimeError(
                    "shared-host CPU affinity changed during the sweep"
                )
        for role, module in modules:
            validate_axioms(pair_name, role, module, built[role])
        issues = [
            issue
            for role, _module in modules
            for issue in shared_host_arm_issues(
                pair_name,
                round_index,
                role,
                built[role],
                measurement_cpu,
                sibling_cpus,
                max_ratio,
            )
        ]
        row: dict[str, object] = {
            "pair": pair_name,
            "round": round_index,
            "slot_index": slot_index,
            "measurement_attempt": attempt,
            "preflight": preflight,
            "build_order": [role for role, _module in modules],
            "host_before_pair": attempt_state,
            "reference": built["reference"],
            "candidate": built["candidate"],
            "signed_wall_delta_nanos": (
                int(built["candidate"]["wall_nanos"])
                - int(built["reference"]["wall_nanos"])
            ),
        }
        if not issues:
            return row, rejected, None
        rejected.append({
            **row,
            "attempt": attempt,
            "issues": issues,
        })
        if attempt <= max_retries:
            print(
                f"[retry {attempt}/{max_retries}] "
                + "; ".join(issues),
                flush=True,
            )
            continue
        return None, rejected, None
    raise AssertionError("unreachable shared-host retry loop")


def warm_imports(spec: SweepSpec, timeout: float) -> None:
    """Build every measured module's imports before recording any pair."""
    modules = sorted(probe_modules(spec))
    command = ["lake", "build", *[f"+{module}:deps" for module in modules]]
    print(f"[warm] {' '.join(command)}", flush=True)
    try:
        proc, _elapsed, _metrics = run_timed(command, timeout)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            f"probe import warmup timed out after {timeout:g}s"
        ) from exc
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise RuntimeError(f"probe import warmup failed ({proc.returncode})")


def artifact_sizes(module: str, src_dir: Path) -> dict[str, int | None]:
    rel = Path(*module.split("."))
    paths = {
        "source": probe_source(module, src_dir),
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


def validate_axioms(
    pair_name: str, role: str, module: ProbeModule, sample: dict[str, object]
) -> None:
    expected = (
        None if module.expected_axioms is None else list(module.expected_axioms)
    )
    if sample["axioms"] != expected:
        raise RuntimeError(
            f"{pair_name} {role} axiom set mismatch: "
            f"expected {expected}, got {sample['axioms']}"
        )


def nested_median(
    samples: list[dict[str, object]], role: str, key: str
) -> int | None:
    values = [
        int(value)
        for sample in samples
        if (value := dict(sample[role]).get(key)) is not None
    ]
    return int(statistics.median(values)) if values else None


def summarize(
    spec: SweepSpec, rows: dict[str, list[dict[str, object]]]
) -> dict[str, dict[str, object]]:
    summary: dict[str, dict[str, object]] = {}
    for pair in spec.pairs:
        samples = rows[pair.name]
        deltas = [int(sample["signed_wall_delta_nanos"]) for sample in samples]
        result: dict[str, object] = {
            **pair.metadata,
            "null_control": pair.null_control,
            "reference": {
                "module": pair.reference.module,
                "expected_axioms": pair.reference.expected_axioms,
                "artifacts": artifact_sizes(
                    pair.reference.module, spec.src_dir
                ),
            },
            "candidate": {
                "module": pair.candidate.module,
                "expected_axioms": pair.candidate.expected_axioms,
                "artifacts": artifact_sizes(
                    pair.candidate.module, spec.src_dir
                ),
            },
            "samples": samples,
            "median_reference_wall_nanos": nested_median(
                samples, "reference", "wall_nanos"
            ),
            "median_candidate_wall_nanos": nested_median(
                samples, "candidate", "wall_nanos"
            ),
            "median_reference_peak_rss_kb": nested_median(
                samples, "reference", "peak_rss_kb"
            ),
            "median_candidate_peak_rss_kb": nested_median(
                samples, "candidate", "peak_rss_kb"
            ),
            "signed_wall_delta_nanos": deltas,
            "median_signed_wall_delta_nanos": int(statistics.median(deltas)),
        }
        result["build_magnitude_wall_nanos"] = max(
            int(result["median_reference_wall_nanos"]),
            int(result["median_candidate_wall_nanos"]),
        )
        summary[pair.name] = result
    controls: list[tuple[str, int, int, int]] = []
    for pair in spec.pairs:
        result = summary[pair.name]
        if not pair.null_control:
            continue
        deltas = list(result["signed_wall_delta_nanos"])
        magnitude = int(result["build_magnitude_wall_nanos"])
        spread = max(deltas) - min(deltas)
        result["null_spread_nanos"] = spread
        result["null_max_absolute_delta_nanos"] = max(
            abs(int(delta)) for delta in deltas
        )
        controls.append(
            (
                pair.name,
                magnitude,
                spread,
                int(result["null_max_absolute_delta_nanos"]),
            )
        )
    for pair in spec.pairs:
        if pair.null_control:
            continue
        result = summary[pair.name]
        magnitude = int(result["build_magnitude_wall_nanos"])
        comparable = [
            (name, control_magnitude, spread, envelope)
            for name, control_magnitude, spread, envelope in controls
            if min(magnitude, control_magnitude) > 0
            and max(magnitude, control_magnitude)
            / min(magnitude, control_magnitude) <= NULL_MAGNITUDE_FACTOR
        ]
        if comparable:
            name, control_magnitude, spread, envelope = min(
                comparable,
                key=lambda item: abs(
                    magnitude - item[1]
                ) / max(magnitude, item[1]),
            )
            result["comparable_control"] = name
            result["control_magnitude_ratio"] = (
                max(magnitude, control_magnitude)
                / min(magnitude, control_magnitude)
            )
            scale_numerator = max(magnitude, control_magnitude)
            scale_denominator = control_magnitude
            applied_spread = (
                spread * scale_numerator + scale_denominator - 1
            ) // scale_denominator
            applied_envelope = (
                envelope * scale_numerator + scale_denominator - 1
            ) // scale_denominator
            result["control_scale_factor"] = (
                scale_numerator / scale_denominator
            )
            result["comparable_null_raw_spread_nanos"] = spread
            result["comparable_null_raw_envelope_nanos"] = envelope
            result["comparable_null_spread_nanos"] = applied_spread
            result["comparable_null_envelope_nanos"] = applied_envelope
            result["resolution"] = (
                "unresolved"
                if abs(int(result["median_signed_wall_delta_nanos"]))
                <= applied_envelope
                else "resolved"
            )
        else:
            result["comparable_control"] = None
            result["control_magnitude_ratio"] = None
            result["control_scale_factor"] = None
            result["comparable_null_raw_spread_nanos"] = None
            result["comparable_null_raw_envelope_nanos"] = None
            result["comparable_null_spread_nanos"] = None
            result["comparable_null_envelope_nanos"] = None
            result["resolution"] = "no-comparable-control"
        budget_ms = pair.metadata.get("tactic_budget_ms")
        if budget_ms is not None:
            budget_nanos = int(budget_ms) * 1_000_000
            median_delta = int(result["median_signed_wall_delta_nanos"])
            envelope_value = result["comparable_null_envelope_nanos"]
            if median_delta >= budget_nanos:
                budget_status = "failed"
            elif envelope_value is None:
                budget_status = "no-comparable-control"
            elif median_delta + int(envelope_value) >= budget_nanos:
                budget_status = "unresolved"
            else:
                budget_status = "passed"
            result["budget_nanos"] = budget_nanos
            result["budget_status"] = budget_status
    return summary


def shared_host_observations(
    rows: dict[str, list[dict[str, object]]],
    measurement_cpu: int,
    sibling_cpus: Sequence[int],
    max_ratio: float,
    max_frequency_spread_ratio: float,
    rejected_pair_attempts: Sequence[dict[str, object]] = (),
    exhausted_pairs: Sequence[dict[str, object]] = (),
    preflight_failures: Sequence[dict[str, object]] = (),
) -> dict[str, object]:
    """Aggregate auditable per-arm contention measurements."""
    max_foreign_ratio = 0.0
    max_interrupt_ratio = 0.0
    max_sibling_ratio = 0.0
    max_aggregate_interference_ratio = 0.0
    max_pressure_delta = 0
    max_concurrent = 0
    max_load = 0.0
    frequencies: list[float] = []
    expected_frequency_observations = 0
    max_effective_interference_ratio = 0.0
    max_interference_allowance_seconds = 0.0
    max_attempts_per_pair = 1
    violations: list[str] = []
    missing_accounting = False
    tick_hz = int(os.sysconf("SC_CLK_TCK"))
    for pair_name, samples in rows.items():
        for sample in samples:
            round_index = int(sample["round"])
            for role in ("reference", "candidate"):
                arm = dict(sample[role])
                wall_seconds = int(arm["wall_nanos"]) / 1_000_000_000
                accounting = dict(arm["cpu_accounting"])
                max_attempts_per_pair = max(
                    max_attempts_per_pair,
                    int(sample.get("measurement_attempt", 1)),
                )
                expected_frequency_observations += 1
                mean_frequency = accounting.get("mean_frequency_khz")
                if (
                    mean_frequency is not None
                    and float(mean_frequency) > 0
                ):
                    frequencies.append(float(mean_frequency))
                for state_key in ("host_before", "host_after"):
                    state = dict(arm[state_key])
                    max_concurrent = max(
                        max_concurrent,
                        int(state["concurrent_lake_lean_count"]),
                    )
                    load = state.get("load_1m_per_cpu")
                    if load is not None:
                        max_load = max(max_load, float(load))
                foreign = accounting["measurement_cpu_foreign_seconds"]
                interrupt = accounting.get(
                    "measurement_cpu_interrupt_seconds"
                )
                residual = accounting.get(
                    "measurement_cpu_noninterrupt_residual_seconds"
                )
                per_cpu = dict(accounting["per_cpu"])
                quantization_allowance = (
                    ACCOUNTING_QUANTIZATION_TICKS / tick_hz
                )
                allowance = max(
                    quantization_allowance,
                    max_ratio * wall_seconds,
                )
                if wall_seconds > 0:
                    max_interference_allowance_seconds = max(
                        max_interference_allowance_seconds, allowance
                    )
                    max_effective_interference_ratio = max(
                        max_effective_interference_ratio,
                        allowance / wall_seconds,
                    )
                    if interrupt is not None:
                        max_interrupt_ratio = max(
                            max_interrupt_ratio,
                            float(interrupt) / wall_seconds,
                        )
                if (
                    foreign is None
                    or residual is None
                    or wall_seconds <= 0
                ):
                    missing_accounting = True
                else:
                    foreign_ratio = float(foreign) / wall_seconds
                    max_foreign_ratio = max(
                        max_foreign_ratio, foreign_ratio
                    )
                    if float(residual) < -quantization_allowance:
                        violations.append(
                            f"{pair_name} round {round_index} {role}: "
                            "child CPU time exceeds pinned-CPU busy time by "
                            f"{-float(residual):.3f}s (allowance "
                            f"{quantization_allowance:.3f}s)"
                        )
                    cpu_percent = arm.get("cpu_percent")
                    if (
                        cpu_percent is not None
                        and float(cpu_percent) > 100 * (1 + max_ratio)
                    ):
                        violations.append(
                            f"{pair_name} round {round_index} {role}: "
                            f"child CPU utilisation {float(cpu_percent):.1f}% "
                            "exceeds the single-CPU affinity ceiling"
                        )
                sibling_busy_seconds = 0.0
                for sibling in sibling_cpus:
                    busy = dict(per_cpu.get(str(sibling), {})).get(
                        "busy_seconds"
                    )
                    if busy is None or wall_seconds <= 0:
                        missing_accounting = True
                        continue
                    sibling_ratio = float(busy) / wall_seconds
                    max_sibling_ratio = max(
                        max_sibling_ratio, sibling_ratio
                    )
                    sibling_busy_seconds += float(busy)
                if foreign is not None and wall_seconds > 0:
                    aggregate_interference = (
                        float(foreign) + sibling_busy_seconds
                    )
                    aggregate_ratio = aggregate_interference / wall_seconds
                    max_aggregate_interference_ratio = max(
                        max_aggregate_interference_ratio,
                        aggregate_ratio,
                    )
                    recorded_aggregate = accounting.get(
                        "aggregate_core_interference_seconds"
                    )
                    if (
                        recorded_aggregate is None
                        or abs(
                            float(recorded_aggregate)
                            - aggregate_interference
                        ) > 1e-9
                    ):
                        missing_accounting = True
                    if aggregate_interference > allowance:
                        violations.append(
                            f"{pair_name} round {round_index} {role}: "
                            "aggregate measurement-CPU foreign and "
                            "SMT-sibling busy time "
                            f"{aggregate_interference:.3f}s exceeds "
                            f"{allowance:.3f}s"
                        )
                pressure = accounting.get("pressure_some_delta_us")
                if pressure is not None:
                    max_pressure_delta = max(
                        max_pressure_delta, int(pressure)
                    )
    if missing_accounting:
        violations.append("per-arm CPU accounting is incomplete")
    if len(frequencies) != expected_frequency_observations:
        violations.append(
            "pinned-CPU frequency accounting is incomplete "
            f"({len(frequencies)}/{expected_frequency_observations} "
            "positive readings)"
        )
    frequency_spread_ratio = None
    if frequencies:
        frequency_spread_ratio = (
            max(frequencies) / min(frequencies) - 1
        )
        if frequency_spread_ratio > max_frequency_spread_ratio:
            violations.append(
                "pinned-CPU frequency spread "
                f"{frequency_spread_ratio:.3f} exceeds "
                f"{max_frequency_spread_ratio:.3f}"
            )
    preflights = [
        dict(sample["preflight"])
        for samples in rows.values()
        for sample in samples
        if sample.get("preflight") is not None
    ]
    preflights.extend(
        dict(attempt["preflight"])
        for attempt in rejected_pair_attempts
        if attempt.get("preflight") is not None
    )
    preflights.extend(
        dict(failure["preflight"])
        for failure in preflight_failures
    )
    return {
        "measurement_cpu": measurement_cpu,
        "smt_sibling_cpus": list(sibling_cpus),
        "max_core_interference_ratio": max_ratio,
        "accounting_quantization_ticks": ACCOUNTING_QUANTIZATION_TICKS,
        "max_effective_core_interference_ratio":
            max_effective_interference_ratio,
        "max_interference_allowance_seconds":
            max_interference_allowance_seconds,
        "max_frequency_spread_ratio": max_frequency_spread_ratio,
        "max_measurement_cpu_foreign_ratio": max_foreign_ratio,
        "max_measurement_cpu_interrupt_ratio": max_interrupt_ratio,
        "max_smt_sibling_busy_ratio": max_sibling_ratio,
        "max_aggregate_core_interference_ratio":
            max_aggregate_interference_ratio,
        "total_rejected_pair_attempts": len(rejected_pair_attempts),
        "max_attempts_per_pair": max(
            max_attempts_per_pair,
            max(
                (
                    int(attempt.get("attempt", 1))
                    for attempt in rejected_pair_attempts
                ),
                default=1,
            ),
        ),
        "total_exhausted_pairs": len(exhausted_pairs),
        "total_rejected_preflight_windows": sum(
            len(preflight.get("rejected_windows", []))
            for preflight in preflights
        ),
        "max_preflight_wait_seconds": max(
            (
                float(preflight.get("elapsed_seconds", 0.0))
                for preflight in preflights
            ),
            default=0.0,
        ),
        "total_preflight_failures": len(preflight_failures),
        "max_cpu_pressure_some_delta_us": max_pressure_delta,
        "max_concurrent_lake_lean_count": max_concurrent,
        "max_load_1m_per_cpu": max_load,
        "min_arm_mean_frequency_khz":
            min(frequencies) if frequencies else None,
        "max_arm_mean_frequency_khz":
            max(frequencies) if frequencies else None,
        "expected_frequency_observations": expected_frequency_observations,
        "observed_frequency_observations": len(frequencies),
        "frequency_spread_ratio": frequency_spread_ratio,
        "violations": violations,
    }


def measurement_completion_issues(
    spec: SweepSpec,
    rows: dict[str, list[dict[str, object]]],
    required_samples: int,
    exhausted_pairs: Sequence[dict[str, object]],
) -> list[str]:
    """Explain why an interrupted or retry-exhausted sweep is incomplete."""
    issues = [
        (
            f"{pair.name}: admitted {len(rows[pair.name])}/"
            f"{required_samples} required paired samples"
        )
        for pair in spec.pairs
        if len(rows[pair.name]) != required_samples
    ]
    issues.extend(
        (
            f"{item['pair']} round {item['round']}: "
            + (
                str(item["reason"])
                if item.get("reason") is not None
                else f"exhausted {item['attempts']} pair attempt(s)"
            )
        )
        for item in exhausted_pairs
    )
    return issues


def validity_summary(
    spec: SweepSpec,
    args: argparse.Namespace,
    results: dict[str, dict[str, object]],
    observations: dict[str, object] | None,
    exceptions: Sequence[str],
) -> tuple[bool, list[str]]:
    """Derive release validity from provenance, contention, and conclusions."""
    issues = list(exceptions)
    if observations is not None:
        issues.extend(
            issue for issue in observations["violations"]
            if issue not in issues
        )
    if args.shared_host:
        control_magnitudes = [
            int(results[pair.name]["build_magnitude_wall_nanos"])
            for pair in spec.pairs
            if pair.null_control
        ]
        if (
            control_magnitudes
            and min(control_magnitudes) > 0
            and max(control_magnitudes) / min(control_magnitudes)
            < MIN_CONTROL_MAGNITUDE_RATIO
        ):
            issues.append(
                "null-control build magnitudes are not sufficiently distinct"
            )
    for pair in spec.pairs:
        if pair.null_control:
            continue
        if (
            args.shared_host
            and results[pair.name].get("resolution")
            == "no-comparable-control"
        ):
            issue = f"{pair.name}: no magnitude-comparable null control"
            if issue not in issues:
                issues.append(issue)
        if "tactic_budget_ms" not in pair.metadata:
            continue
        if args.shared_host:
            tick_hz = int(os.sysconf("SC_CLK_TCK"))
            quantization = ACCOUNTING_QUANTIZATION_TICKS / tick_hz
            pair_allowances = [
                sum(
                    max(
                        quantization,
                        args.max_core_interference_ratio
                        * int(sample[role]["wall_nanos"])
                        / 1_000_000_000,
                    )
                    for role in ("reference", "candidate")
                )
                for sample in results[pair.name]["samples"]
            ]
            interference_ceiling_nanos = int(
                max(pair_allowances, default=0.0) * 1_000_000_000
            )
            results[pair.name][
                "budget_interference_ceiling_nanos"
            ] = interference_ceiling_nanos
            budget_nanos = int(results[pair.name]["budget_nanos"])
            if interference_ceiling_nanos >= budget_nanos:
                issue = (
                    f"{pair.name}: tactic budget is not resolvable under "
                    "the admitted core-interference ceiling"
                )
                if issue not in issues:
                    issues.append(issue)
        status = results[pair.name].get("budget_status")
        if status != "passed":
            issue = f"{pair.name}: tactic budget {status}"
            if issue not in issues:
                issues.append(issue)
    release_quality = (
        not args.allow_dirty
        and not args.allow_busy
        and not issues
    )
    return release_quality, issues


def default_output(env: dict[str, object], output_stem: str) -> Path:
    commit = str(env["git_commit"] or "unknown")[:12]
    host = re.sub(r"[^A-Za-z0-9_.-]+", "-", str(env["hostname"]))
    return (
        ROOT / "reports" / "bench-results" /
        f"{output_stem}-{commit}-{host}.json"
    )


def run_cli(
    spec: SweepSpec,
    caller_file: Path,
    argv: Sequence[str] | None = None,
) -> int:
    validate_spec(spec)
    args = parse_args(
        spec.description,
        argv,
        default_samples=spec.required_samples or 4,
    )
    configure_shared_host(args)
    if spec.required_samples is not None and args.samples != spec.required_samples:
        raise RuntimeError(
            f"this sweep requires --samples {spec.required_samples}, "
            f"got {args.samples}"
        )
    if args.samples % 2 != 0:
        raise RuntimeError(
            "fresh-module sweeps require an even --samples so pair "
            "orientation is balanced"
        )
    protocol_issues = shared_host_protocol_issues(spec, args)
    if protocol_issues:
        raise RuntimeError(
            "invalid shared-host protocol: " + "; ".join(protocol_issues)
        )
    env = environment()
    validity_exceptions: list[str] = []
    dirt = dirty_issues(
        dict(env["repository"]), dict(env["dependency_checkouts"])
    )
    if dirt and not args.allow_dirty:
        raise RuntimeError("dirty measurement environment: " + "; ".join(dirt))
    if dirt:
        validity_exceptions.extend(dirt)
    busy = host_issues(
        dict(env["host_before"]),
        args.max_load_per_cpu,
        concurrent_is_issue=not args.shared_host,
        load_is_issue=not args.shared_host,
    )
    if busy and not args.allow_busy:
        raise RuntimeError("busy measurement environment: " + "; ".join(busy))
    if busy:
        validity_exceptions.extend(busy)
    warm_imports(spec, args.warm_timeout)
    post_warm = host_issues(
        host_state(),
        args.max_load_per_cpu,
        concurrent_is_issue=not args.shared_host,
        load_is_issue=False,
    )
    if post_warm and not args.allow_busy:
        raise RuntimeError(
            "busy measurement environment after warmup: "
            + "; ".join(post_warm)
        )
    validity_exceptions.extend(
        issue for issue in post_warm if issue not in validity_exceptions
    )
    before = source_hashes(spec, caller_file)
    pairs = list(spec.pairs)
    rows: dict[str, list[dict[str, object]]] = {
        pair.name: [] for pair in pairs
    }
    rejected_pair_attempts: list[dict[str, object]] = []
    exhausted_pairs: list[dict[str, object]] = []
    preflight_failures: list[dict[str, object]] = []
    topology = (
        cpu_topology(args.cpu)
        if args.shared_host and args.cpu is not None
        else None
    )
    monitored_cpus: list[int] = []
    sibling_cpus: list[int] = []
    if topology is not None and args.cpu is not None:
        monitored_cpus = parse_cpu_list(
            str(topology["thread_siblings_list"])
            if topology["thread_siblings_list"] is not None
            else None
        )
        if args.cpu not in monitored_cpus:
            monitored_cpus.append(args.cpu)
        monitored_cpus.sort()
        sibling_cpus = [
            cpu for cpu in monitored_cpus if cpu != args.cpu
        ]
        if not sibling_cpus:
            raise RuntimeError(
                "shared-host CPU topology has no recorded SMT sibling"
            )

    measurement_exhausted = False
    for round_index in range(args.samples):
        for slot_index, pair in enumerate(rotate(pairs, round_index)):
            state = host_state()
            issues = host_issues(
                state,
                args.max_load_per_cpu,
                concurrent_is_issue=not args.shared_host,
                load_is_issue=not args.shared_host,
            )
            if issues and not args.allow_busy:
                raise RuntimeError("host became busy: " + "; ".join(issues))
            validity_exceptions.extend(issue for issue in issues
                                       if issue not in validity_exceptions)
            modules = ordered_modules(pair, round_index)
            if args.shared_host and args.cpu is not None:
                row, rejected, preflight_failure = build_shared_host_pair(
                    pair.name,
                    round_index + 1,
                    slot_index,
                    modules,
                    args.timeout,
                    args.cpu,
                    monitored_cpus,
                    sibling_cpus,
                    args.max_core_interference_ratio,
                    args.max_pair_retries,
                    args.preflight_window_seconds,
                    args.preflight_timeout_seconds,
                )
                rejected_pair_attempts.extend(rejected)
                if row is None:
                    if preflight_failure is not None:
                        preflight_failures.append(preflight_failure)
                        failure_issues = list(
                            preflight_failure["issues"]
                        )
                        reason = failure_issues[0]
                    else:
                        failure_issues = list(rejected[-1]["issues"])
                        reason = None
                    exhausted_pairs.append({
                        "pair": pair.name,
                        "round": round_index + 1,
                        "slot_index": slot_index,
                        "attempts": len(rejected),
                        "issues": failure_issues,
                        "reason": reason,
                    })
                    measurement_exhausted = True
                    break
                rows[pair.name].append(row)
            else:
                built: dict[str, dict[str, object]] = {}
                for role, module in modules:
                    print(
                        f"[{round_index + 1}/{args.samples}] {pair.name} "
                        f"{role} ({module.module})",
                        flush=True,
                    )
                    sample = build_sample(
                        module.module,
                        args.timeout,
                        measurement_cpu=None,
                        monitored_cpus=monitored_cpus,
                    )
                    validate_axioms(pair.name, role, module, sample)
                    built[role] = sample
                reference = built["reference"]
                candidate = built["candidate"]
                rows[pair.name].append({
                    "round": round_index + 1,
                    "slot_index": slot_index,
                    "build_order": [role for role, _module in modules],
                    "host_before_pair": sampled_host_state(state),
                    "reference": reference,
                    "candidate": candidate,
                    "signed_wall_delta_nanos": (
                        int(candidate["wall_nanos"])
                        - int(reference["wall_nanos"])
                    ),
                })
        if measurement_exhausted:
            break

    after = source_hashes(spec, caller_file)
    if after != before:
        raise RuntimeError("measurement sources changed during the sweep")

    repository_after = checkout_state(ROOT)
    dependencies_after = dependency_checkouts()
    if repository_after.get("state_sha256") != dict(env["repository"]).get(
        "state_sha256"
    ):
        raise RuntimeError("repository checkout changed during the sweep")
    if dependencies_after != env["dependency_checkouts"]:
        raise RuntimeError("dependency checkout changed during the sweep")
    host_after = host_state()
    final_busy = host_issues(
        host_after,
        args.max_load_per_cpu,
        concurrent_is_issue=not args.shared_host,
        load_is_issue=not args.shared_host,
    )
    if final_busy and not args.allow_busy:
        raise RuntimeError("host became busy: " + "; ".join(final_busy))
    validity_exceptions.extend(issue for issue in final_busy
                               if issue not in validity_exceptions)
    env["host_after"] = host_after
    completion_issues = measurement_completion_issues(
        spec, rows, args.samples, exhausted_pairs
    )
    validity_exceptions.extend(
        issue for issue in completion_issues
        if issue not in validity_exceptions
    )
    results = {} if completion_issues else summarize(spec, rows)
    observations = None
    if args.shared_host and args.cpu is not None:
        observations = shared_host_observations(
            rows,
            args.cpu,
            sibling_cpus,
            args.max_core_interference_ratio,
            args.max_frequency_spread_ratio,
            rejected_pair_attempts,
            exhausted_pairs,
            preflight_failures,
        )
    if completion_issues:
        release_quality = False
        if observations is not None:
            validity_exceptions.extend(
                issue for issue in observations["violations"]
                if issue not in validity_exceptions
            )
    else:
        release_quality, validity_exceptions = validity_summary(
            spec,
            args,
            results,
            observations,
            validity_exceptions,
        )

    record = {
        "schema": spec.schema,
        "measurement": spec.measurement,
        "measurement_state": (
            "incomplete" if completion_issues else "complete"
        ),
        "environment": env,
        "validity": {
            "release_quality": release_quality,
            "exceptions": validity_exceptions,
            "observed": observations,
            "host_protocol": (
                "designated-shared-host-v3"
                if args.shared_host
                else "quiescent-host-v1"
            ),
        },
        "config": {
            "samples": args.samples,
            "timeout_seconds": args.timeout,
            "warm_timeout_seconds": args.warm_timeout,
            "warm_command_template": "lake build +<module>:deps",
            "command_template": "lake build +<module>:olean",
            "order": [pair.name for pair in pairs],
            "rotation": "pairs left by round index; pair orientation alternates",
            "pairing": (
                "adjacent measured reference and candidate fresh modules; "
                "contamination retries the complete oriented pair"
            ),
            "max_load_per_cpu": args.max_load_per_cpu,
            "max_core_interference_ratio":
                args.max_core_interference_ratio,
            "accounting_quantization_ticks":
                ACCOUNTING_QUANTIZATION_TICKS,
            "measurement_cpu_foreign_accounting":
                "busy-minus-child-minus-runner-minus-irq-softirq",
            "core_interference_accounting":
                "measurement-cpu-foreign-plus-all-SMT-sibling-busy",
            "max_pair_retries": args.max_pair_retries,
            "preflight_window_seconds": args.preflight_window_seconds,
            "preflight_timeout_seconds": args.preflight_timeout_seconds,
            "preflight_max_busy_ticks": PREFLIGHT_MAX_BUSY_TICKS,
            "max_frequency_spread_ratio":
                args.max_frequency_spread_ratio,
            "minimum_control_magnitude_ratio":
                MIN_CONTROL_MAGNITUDE_RATIO,
            "null_magnitude_factor": NULL_MAGNITUDE_FACTOR,
            "frequency_measurement":
                "cpufreq-time-in-state-arm-mean",
            "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
            "allow_dirty": args.allow_dirty,
            "allow_busy": args.allow_busy,
            "shared_host": args.shared_host,
            "expected_host": args.expected_host,
            "requested_cpu": args.cpu,
            "cpu_affinity": cpu_affinity(),
            "cpu_topology": topology,
        },
        "results": results,
        "partial_samples": rows if completion_issues else None,
        "rejected_pair_attempts": rejected_pair_attempts,
        "exhausted_pairs": exhausted_pairs,
        "preflight_failures": preflight_failures,
        "source_sha256": before,
    }
    output = args.output or default_output(env, spec.output_stem)
    if not output.is_absolute():
        output = ROOT / output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    try:
        display = output.relative_to(ROOT)
    except ValueError:
        display = output
    print(display)
    return 0 if release_quality else 2
