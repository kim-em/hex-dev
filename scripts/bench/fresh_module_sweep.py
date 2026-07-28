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
DEFAULT_MAX_LOAD_PER_CPU = 0.5
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


def parse_args(
    description: str, argv: Sequence[str] | None = None
) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--samples", type=int, default=3)
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
        "--max-load-per-cpu",
        type=float,
        default=DEFAULT_MAX_LOAD_PER_CPU,
        help="maximum one-minute load average divided by logical CPU count",
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


def host_state() -> dict[str, object]:
    cpus = os.cpu_count() or 1
    try:
        load = list(os.getloadavg())
    except OSError:
        load = []
    return {
        "logical_cpus": cpus,
        "load_average": load,
        "load_1m_per_cpu": load[0] / cpus if load else None,
        "concurrent_lake_lean": lean_processes(),
    }


def host_issues(state: dict[str, object], max_load_per_cpu: float) -> list[str]:
    issues: list[str] = []
    processes = state["concurrent_lake_lean"]
    if processes:
        issues.append(f"{len(processes)} concurrent Lake/Lean process(es)")
    load = state["load_1m_per_cpu"]
    if load is not None and float(load) > max_load_per_cpu:
        issues.append(
            f"one-minute load/CPU {float(load):.3f} exceeds {max_load_per_cpu:.3f}"
        )
    return issues


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
        if pair.reference.module == pair.candidate.module:
            raise RuntimeError(f"{pair.name}: reference and candidate are identical")
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
    files.update(
        path if path.is_absolute() else ROOT / path
        for path in spec.extra_sources
    )
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
        terminate_process_group(child)
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


def warm_imports(spec: SweepSpec, timeout: float) -> None:
    """Build every measured module's imports before recording any pair."""
    modules = sorted(probe_modules(spec))
    command = ["lake", "build", *[f"+{module}:deps" for module in modules]]
    print(f"[warm] {' '.join(command)}", flush=True)
    try:
        proc, _elapsed, _rss = run_timed(command, timeout)
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
        summary[pair.name] = result
    return summary


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
    args = parse_args(spec.description, argv)
    warm_imports(spec, args.warm_timeout)
    env = environment()
    validity_exceptions: list[str] = []
    dirt = dirty_issues(
        dict(env["repository"]), dict(env["dependency_checkouts"])
    )
    if dirt and not args.allow_dirty:
        raise RuntimeError("dirty measurement environment: " + "; ".join(dirt))
    if dirt:
        validity_exceptions.extend(dirt)
    busy = host_issues(dict(env["host_before"]), args.max_load_per_cpu)
    if busy and not args.allow_busy:
        raise RuntimeError("busy measurement environment: " + "; ".join(busy))
    if busy:
        validity_exceptions.extend(busy)
    before = source_hashes(spec, caller_file)
    pairs = list(spec.pairs)
    rows: dict[str, list[dict[str, object]]] = {
        pair.name: [] for pair in pairs
    }

    for round_index in range(args.samples):
        for pair in rotate(pairs, round_index):
            state = host_state()
            issues = host_issues(state, args.max_load_per_cpu)
            if issues and not args.allow_busy:
                raise RuntimeError("host became busy: " + "; ".join(issues))
            validity_exceptions.extend(issue for issue in issues
                                       if issue not in validity_exceptions)
            modules = ordered_modules(pair, round_index)
            built: dict[str, dict[str, object]] = {}
            for role, module in modules:
                print(
                    f"[{round_index + 1}/{args.samples}] {pair.name} "
                    f"{role} ({module.module})",
                    flush=True,
                )
                sample = build_sample(module.module, args.timeout)
                validate_axioms(pair.name, role, module, sample)
                built[role] = sample
            reference = built["reference"]
            candidate = built["candidate"]
            rows[pair.name].append({
                "round": round_index + 1,
                "build_order": [role for role, _module in modules],
                "reference": reference,
                "candidate": candidate,
                "signed_wall_delta_nanos": (
                    int(candidate["wall_nanos"])
                    - int(reference["wall_nanos"])
                ),
            })

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
    final_busy = host_issues(host_after, args.max_load_per_cpu)
    if final_busy and not args.allow_busy:
        raise RuntimeError("host became busy: " + "; ".join(final_busy))
    validity_exceptions.extend(issue for issue in final_busy
                               if issue not in validity_exceptions)
    env["host_after"] = host_after

    record = {
        "schema": spec.schema,
        "measurement": spec.measurement,
        "environment": env,
        "validity": {
            "release_quality": not validity_exceptions,
            "exceptions": validity_exceptions,
        },
        "config": {
            "samples": args.samples,
            "timeout_seconds": args.timeout,
            "warm_timeout_seconds": args.warm_timeout,
            "warm_command_template": "lake build +<module>:deps",
            "command_template": "lake build +<module>:olean",
            "order": [pair.name for pair in pairs],
            "rotation": "pairs left by round index; pair orientation alternates",
            "pairing": "adjacent measured reference and candidate fresh modules",
            "max_load_per_cpu": args.max_load_per_cpu,
            "allow_dirty": args.allow_dirty,
            "allow_busy": args.allow_busy,
        },
        "results": summarize(spec, rows),
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
    return 0
