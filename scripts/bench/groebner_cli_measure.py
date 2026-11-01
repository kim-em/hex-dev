#!/usr/bin/env python3
"""Retain matched development sweeps of the standalone unchecked F4 driver.

Supply a frozen binary/source manifest and suite JSON. Inputs are sibling files
named <case>.json and <case>.ms. Each campaign uses adjacent AB then BA, one
leased CPU on the Linux shared host and identical GNU-time wrappers. Complete outputs are independently
parsed. Partial campaigns, failures and mismatches are retained and cannot
establish coverage or leadership. Certificate generation/checking is excluded.
"""

from pathlib import Path
import argparse, os, sys, json, hashlib, subprocess, time, resource, select, signal, ctypes, math, statistics, shutil

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.oracle.groebner_singular import polynomial, canonical


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--suite", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--hex", type=Path, required=True)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--msolve", type=Path)
    parser.add_argument("--msolve-source", type=Path)
    parser.add_argument("--msolve-mode", type=int, choices=[2, 42], default=2)
    parser.add_argument("--time", default=shutil.which("time"))
    args = parser.parse_args()
    if bool(args.reference) == bool(args.msolve):
        parser.error("select exactly one of --reference or --msolve")
    if args.msolve and not args.msolve_source:
        parser.error("--msolve requires --msolve-source for provenance")
    if not args.time:
        parser.error("GNU time is required for child peak RSS")
    time_version = subprocess.check_output([args.time, "--version"], text=True)
    if "GNU" not in time_version:
        parser.error("--time must select GNU time")
    manifest = json.loads(args.manifest.read_text())
    root = args.suite.resolve().parent
    plan = json.loads(args.suite.read_text())
    mode = args.msolve_mode if args.msolve else None
    out = args.output.resolve()
    out.mkdir(exist_ok=False)
    sha = lambda f: hashlib.file_digest(f.open("rb"), "sha256").hexdigest()
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
    if sha(args.hex.resolve()) != manifest["binary_sha256"]["compute"]:
        parser.error("Hex binary differs from frozen manifest")
    if (
        args.reference
        and sha(args.reference.resolve())
        != manifest["binary_sha256"]["compute-reference"]
    ):
        parser.error("reference binary differs from frozen manifest")
    inputs = out / "inputs"
    inputs.mkdir()
    shutil.copy2(args.suite, inputs / args.suite.name)
    for case in plan["cases"]:
        for extension in [".json", ".ms"]:
            shutil.copy2(
                root / (case["name"] + extension), inputs / (case["name"] + extension)
            )
    root = inputs
    cliargs = [
        "--work",
        "100000000000",
        "--packed-bytes",
        str(16 * 1024**3),
        "--pairs",
        "100000000",
        "--monomials",
        "10000000",
        "--matrix-entries",
        "1000000000",
    ]
    binaries = {
        "A": (args.hex if mode else args.reference).resolve(),
        "B": (args.msolve if mode else args.hex).resolve(),
    }
    m = {
        **manifest,
        "cpu": cpu,
        "threads": 1,
        "host": os.uname().nodename,
        "load_start": os.getloadavg(),
        "suite_sha256": sha(args.suite),
        "schedule": "two fixed blocks, adjacent AB then BA per input; retain all completed samples",
        "contract": "Full unchecked reduced candidates; no certificate generation, independent final certification or kernel replay in timing. GNU time wrapper is identical on both arms and supplies post-exec peak RSS; wall time includes wrapper/launch/startup/parse/full output. A/B are ordinary/minimal SDK initialization of identical driver code unless msolve mode is present, then A is the dedicated driver and B is msolve full reduced grevlex output. One algorithm thread; resource caps match. No quiet-host filtering.",
        "baseline_source_fingerprint": manifest["source_fingerprint"],
        "script": Path(__file__).read_text(),
        "samples": [],
        "msolve_mode": mode,
        "binary_sha256": {a: sha(f) for a, f in binaries.items()},
        "time_version": time_version,
        "time_sha256": sha(Path(args.time).resolve()),
        "protocol": plan["protocol"],
        "input_sha256": {f.name: sha(f) for f in sorted(inputs.iterdir())},
    }
    if mode:
        ms = args.msolve_source.resolve()
        assert args.msolve.resolve() == (ms / "msolve").resolve(), (
            "msolve wrapper must belong to the recorded source tree"
        )
        m.update(
            msolve_commit=subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ms, text=True
            ).strip(),
            msolve_engine_sha256=sha(ms / "src/neogb/.libs/libneogb.so.4.0.0"),
            msolve_cli_sha256=sha(ms / ".libs/msolve"),
            msolve_build_flags={
                str(f): "\n".join(
                    line
                    for line in f.read_text().splitlines()
                    if line.startswith(
                        ("CC =", "CFLAGS =", "CPPFLAGS =", "LDFLAGS =", "LIBS =")
                    )
                )
                for f in [ms / "Makefile", ms / "src/neogb/Makefile"]
            },
        )
    libc = ctypes.CDLL(None, use_errno=True)
    libc.pidfd_open.argtypes = [ctypes.c_int, ctypes.c_uint]
    libc.pidfd_open.restype = ctypes.c_int

    def limits():
        os.setsid()
        resource.setrlimit(
            resource.RLIMIT_AS, (plan["protocol"]["address_space_bytes"],) * 2
        )
        resource.setrlimit(resource.RLIMIT_FSIZE, (64 * 1024**2,) * 2)

    try:
        for block, order in enumerate(["AB", "BA"]):
            for case in plan["cases"]:
                bases = {}
                results = {}
                for arm in order:
                    prefix = f"{case['name']}-b{block}-{arm}"
                    rss = out / (prefix + ".rss")
                    basisfile = out / (prefix + ".basis")
                    program = (
                        [
                            str(binaries[arm]),
                            "-g",
                            "2",
                            "-t",
                            "1",
                            "-l",
                            str(mode),
                            "-v",
                            "2",
                            "-f",
                            str(root / (case["name"] + ".ms")),
                            "-o",
                            str(basisfile),
                        ]
                        if mode and arm == "B"
                        else [
                            str(binaries[arm]),
                            *cliargs,
                            str(root / (case["name"] + ".json")),
                        ]
                    )
                    command = [args.time, "-f", "%M", "-o", str(rss), *program]
                    start = time.monotonic_ns()
                    timeout = False
                    with (
                        (out / (prefix + ".stdout")).open("wb") as stdout,
                        (out / (prefix + ".stderr")).open("wb") as stderr,
                    ):
                        proc = subprocess.Popen(
                            command,
                            stdout=stdout,
                            stderr=stderr,
                            env=env,
                            preexec_fn=limits,
                        )
                        fd = libc.pidfd_open(proc.pid, 0)
                        if fd < 0:
                            raise OSError(ctypes.get_errno(), "pidfd_open")
                        try:
                            ready, _, _ = select.select(
                                [fd], [], [], plan["protocol"]["timeout_seconds"]
                            )
                            if not ready:
                                timeout = True
                                os.killpg(proc.pid, signal.SIGKILL)
                            _, status, usage = os.wait4(proc.pid, 0)
                            proc.returncode = os.waitstatus_to_exitcode(status)
                        finally:
                            os.close(fd)
                    elapsed = time.monotonic_ns() - start
                    record = {
                        "case": case["name"],
                        "family": case["family"],
                        "p": case["p"],
                        "block": block,
                        "arm": arm,
                        "command": command,
                        "wall_nanos": elapsed,
                        "status": "timeout"
                        if timeout
                        else "ok"
                        if proc.returncode == 0
                        else "failed",
                        "returncode": proc.returncode,
                        "peak_rss_kib": int(rss.read_text().splitlines()[-1])
                        if rss.exists() and rss.read_text().splitlines()[-1].isdigit()
                        else None,
                    }
                    if proc.returncode == 0:
                        try:
                            if mode and arm == "B":
                                data = "".join(
                                    line
                                    for line in basisfile.read_text().splitlines()
                                    if not line.startswith("#")
                                ).strip()
                                assert data.startswith("[") and data.endswith("]:")
                                bases[arm] = sorted(
                                    polynomial(s, case["variables"], case["p"])
                                    for s in data[1:-2].split(",")
                                )
                            else:
                                payload = json.loads(
                                    (out / (prefix + ".stdout")).read_text()
                                )
                                assert payload["kind"] == "unchecked_candidate"
                                bases[arm] = canonical(payload["basis"])
                                results[arm] = {
                                    k: v
                                    for k, v in payload.items()
                                    if k not in ["basis", "candidateNanos"]
                                }
                                record["statistics"] = {
                                    **payload["statistics"],
                                    "candidate_nanos": payload["candidateNanos"],
                                }
                        except (
                            ValueError,
                            KeyError,
                            AssertionError,
                            IndexError,
                            OSError,
                        ) as error:
                            record["status"] = "invalid_output"
                            record["error"] = str(error)
                            bases.pop(arm, None)
                            results.pop(arm, None)
                    m["samples"].append(record)
                    print(prefix, record["status"], round(elapsed / 1e6, 2), flush=True)
                equal = len(bases) == 2 and bases["A"] == bases["B"]
                if not mode and len(results) == 2:
                    equal = equal and results["A"] == results["B"]
                for sample in m["samples"][-2:]:
                    sample["complete_basis_equal"] = equal
    finally:
        m["load_end"] = os.getloadavg()
        (out / "metadata.json").write_text(json.dumps(m, indent=2) + "\n")
        lease.close()
    ratios = []
    families = {}
    for case in plan["cases"]:
        for block in [0, 1]:
            a, b = [
                next(
                    s
                    for s in m["samples"]
                    if s["case"] == case["name"]
                    and s["block"] == block
                    and s["arm"] == arm
                )
                for arm in ["A", "B"]
            ]
            if a["status"] == b["status"] == "ok" and a["complete_basis_equal"]:
                r = (
                    a["wall_nanos"] / b["wall_nanos"]
                    if mode
                    else b["wall_nanos"] / a["wall_nanos"]
                )
                ratios.append(r)
                families.setdefault(case["family"], []).append(r)
    g = lambda v: math.exp(sum(map(math.log, v)) / len(v)) if v else None
    summary = {
        "cpu": cpu,
        "samples": len(m["samples"]),
        "complete_bases_equal": sum(s["complete_basis_equal"] for s in m["samples"])
        // 2,
        "paired_inputs": len(plan["cases"]) * 2,
        "successful_processes": {
            arm: sum(s["arm"] == arm and s["status"] == "ok" for s in m["samples"])
            for arm in ["A", "B"]
        },
        "timeouts": sum(s["status"] == "timeout" for s in m["samples"]),
        "failed_processes": sum(s["status"] != "ok" for s in m["samples"]),
        "ratio_direction": "Hex/msolve process" if mode else "minimal/full process",
        "geomean": g(ratios),
        "median": statistics.median(ratios) if ratios else None,
        "minimum": min(ratios) if ratios else None,
        "maximum": max(ratios) if ratios else None,
        "per_family": {k: g(v) for k, v in families.items()},
        "family_balanced_geomean": g([g(v) for v in families.values()])
        if set(families) == {c["family"] for c in plan["cases"]}
        else None,
        "peak_rss_kib": {
            arm: max(
                (
                    s["peak_rss_kib"]
                    for s in m["samples"]
                    if s["arm"] == arm and s["peak_rss_kib"] is not None
                ),
                default=None,
            )
            for arm in ["A", "B"]
        },
    }
    (out / "analysis.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))

    if (
        summary["failed_processes"]
        or summary["complete_bases_equal"] != summary["paired_inputs"]
    ):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
