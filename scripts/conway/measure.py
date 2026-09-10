#!/usr/bin/env python3
"""Measure clean Conway rebuilds, retaining dependency caches (Linux).

First build the targets to warm dependencies. Run from the repository root.
All Conway output directories and umbrella artifacts are removed before each
run; companion measurements remove both HexGFq and HexGFqMathlib outputs.
--no-cache forbids Lake restoring the removed outputs from remote cache.
GNU time reports maximum child RSS; sampled process-tree RSS also captures
simultaneous compilers. Compressed verbose logs retain per-module timings.
A measurement is rejected if it unexpectedly rebuilds an external dependency.
"""

import argparse
import hashlib
import gzip
import signal
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time
from provenance import sources, dependencies, hashes, imports


def clean(prefix):
    root = Path(".lake/build")
    for path in list(root.rglob("*")):
        if path.exists() and (
            path.name == prefix or path.name.startswith(prefix + ".")
        ):
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()


def rss_tree(pid):
    pending, total = [pid], 0
    while pending:
        current = pending.pop()
        try:
            status = Path(f"/proc/{current}/status").read_text()
            match = re.search(r"VmRSS:\s+(\d+)", status)
            total += int(match[1]) if match else 0

            for task in Path(f"/proc/{current}/task").iterdir():
                pending.extend(map(int, (task / "children").read_text().split()))
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("label")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--companion", action="store_true")
    ap.add_argument(
        "--warm-dependencies",
        action="store_true",
        help="Build external imports before cleaning and starting the clock",
    )
    ap.add_argument(
        "--ceiling",
        type=float,
        default=0,
        help="Terminate candidates exceeding this wall time; zero means no cap",
    )
    ap.add_argument(
        "--keep-going",
        action="store_true",
        help="Record all failed or capped candidate runs",
    )
    ap.add_argument(
        "--max-rss-kib",
        type=int,
        default=0,
        help="Stop a candidate at this aggregate memory limit; zero disables",
    )
    args = ap.parse_args()
    if args.runs < 1 or args.threads < 1 or args.ceiling < 0 or args.max_rss_kib < 0:
        ap.error(
            "runs and threads must be positive; resource limits must be nonnegative"
        )
    prefix = "HexGFqMathlib" if args.companion else "HexConway"
    prefixes = ["HexGFq", "HexGFqMathlib"] if args.companion else [prefix]
    targets = ["HexGFq", "HexGFqMathlib"] if args.companion else ["HexConway"]
    timer = shutil.which("time")
    if timer is None or "GNU" not in subprocess.check_output(
        [timer, "--version"], text=True
    ):
        ap.error("GNU time is required (install the system 'time' package)")
    measured_sources = sources(prefixes)
    external_imports = sorted(
        {
            name
            for path in measured_sources
            for name in imports(path)
            if name.split(".", 1)[0] not in prefixes
            and Path(name.replace(".", "/") + ".lean").is_file()
        }
    )
    if args.warm_dependencies and external_imports:
        subprocess.run(
            ["lake", "--no-cache", "build", *external_imports],
            check=True,
            env={**os.environ, "LEAN_NUM_THREADS": str(args.threads)},
        )
    out = Path("reports/conway")
    out.mkdir(exist_ok=True, parents=True)
    report = dict(
        machine=platform.node(),
        cpu=next(
            x.split(":", 1)[1].strip()
            for x in Path("/proc/cpuinfo").read_text().splitlines()
            if x.startswith("model name")
        ),
        platform=platform.platform(),
        toolchain=Path("lean-toolchain").read_text().strip(),
        threads=args.threads,
        scheduling="Lake default scheduling; four import chains per polynomial-proof family; compatibility follows its primitivity chain; factor-prime proofs form one chain",
        cpu_affinity=sorted(os.sched_getaffinity(0)),
        mem_total_kib=int(
            re.search(r"MemTotal:\s+(\d+)", Path("/proc/meminfo").read_text())[1]
        ),
        lake_manifest_sha256=hashlib.sha256(
            Path("lake-manifest.json").read_bytes()
        ).hexdigest(),
        cleaned_prefixes=prefixes,
        ceiling_seconds=args.ceiling,
        memory_ceiling_kib=args.max_rss_kib,
        rss_sampling_seconds=0.1,
        targets=targets,
        commit=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        dirty=bool(
            subprocess.check_output(
                ["git", "status", "--porcelain", "--", ".", ":(exclude)reports/"],
                text=True,
            )
        ),
        dirty_excludes=["reports/"],
        warmed_imports=external_imports if args.warm_dependencies else [],
        runs=[],
    )
    report["scope"] = json.loads(Path("scripts/conway/scope.json").read_text())
    report["input_sha256"] = {
        str(p): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(Path("scripts/conway").glob("*"))
        if p.is_file() and p.suffix in {".py", ".json", ".in", ".txt"}
    }
    report["source_sha256"] = hashes(measured_sources)
    report["dependency_sha256"] = hashes(dependencies(measured_sources))
    for i in range(args.runs):
        for name in prefixes:
            clean(name)
        log = out / f"{args.label}-{i+1}.log"
        timing = out / f"{args.label}-{i+1}.time"
        cmd = [
            timer,
            "-v",
            "-o",
            str(timing),
            "lake",
            "--no-cache",
            "-v",
            "build",
            *targets,
        ]
        load_start = os.getloadavg()
        start, peak = time.monotonic(), 0
        capped = False
        memory_capped = False
        with log.open("w") as f:
            proc = subprocess.Popen(
                cmd,
                stdout=f,
                stderr=subprocess.STDOUT,
                env={**os.environ, "LEAN_NUM_THREADS": str(args.threads)},
                start_new_session=True,
            )
            while proc.poll() is None:
                peak = max(peak, rss_tree(proc.pid))
                time.sleep(0.1)
                if args.max_rss_kib and peak > args.max_rss_kib:
                    memory_capped = True
                    os.killpg(proc.pid, signal.SIGTERM)
                    proc.wait()
                elif args.ceiling and time.monotonic() - start > args.ceiling:
                    capped = True
                    os.killpg(proc.pid, signal.SIGTERM)
                    proc.wait()
        wall = time.monotonic() - start
        sizes = {
            str(p): p.stat().st_size
            for p in Path(".lake/build").rglob("*")
            if p.is_file()
            and any(
                name in p.parts or p.name.startswith(name + ".") for name in prefixes
            )
        }
        sizes_by_suffix = {}
        for path, size in sizes.items():
            suffix = Path(path).suffix
            sizes_by_suffix[suffix] = sizes_by_suffix.get(suffix, 0) + size
        rss_match = re.search(
            r"Maximum resident set size \(kbytes\): (\d+)", timing.read_text()
        )
        max_child_rss = int(rss_match[1]) if rss_match else None
        modules = re.findall(r"Built ([^\n]+)", log.read_text())
        dependency_builds = [
            name
            for name in modules
            if name.split()[0].split(".", 1)[0].split(":", 1)[0] not in prefixes
        ]
        row = dict(
            load_average_start=load_start,
            load_average_end=os.getloadavg(),
            dependency_builds=dependency_builds,
            capped=capped,
            memory_capped=memory_capped,
            max_child_rss_kib=max_child_rss,
            wall_seconds=wall,
            peak_tree_rss_kib=peak,
            exit_code=proc.returncode,
            artifact_bytes=sum(sizes.values()),
            artifact_count=len(sizes),
            artifact_bytes_by_suffix=sizes_by_suffix,
            modules=modules,
            log=str(log),
            timing=str(timing),
        )
        packed_log = log.with_suffix(".log.gz")
        packed_log.write_bytes(gzip.compress(log.read_bytes(), mtime=0))
        log.unlink()
        row["log"] = str(packed_log)
        report["runs"].append(row)
        (out / f"{args.label}.json").write_text(json.dumps(report, indent=2) + "\n")
        print(
            f"{args.label} {i+1}: {wall:.3f}s, tree RSS {peak} KiB, exit {proc.returncode}",
            flush=True,
        )
        if dependency_builds:
            raise SystemExit(
                "Dependencies were rebuilt; warm them and repeat this measurement"
            )
        if proc.returncode and not args.keep_going:
            raise SystemExit(proc.returncode)


if __name__ == "__main__":
    main()
