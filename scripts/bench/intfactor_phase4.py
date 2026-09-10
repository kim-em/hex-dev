#!/usr/bin/env python3
"""Collect and render reproducible HexIntFactor Phase-4 evidence.

All children run on one pinned shared-host CPU. PARI uses calibrated in-process batches.
GMP-ECM uses one fixed 256-input batch shape with sigma 0:7, B1 1000, and B2 1
(B2 < B1 disables stage 2) for both the overhead control and every operand.
"""

from __future__ import annotations

import argparse
from contextlib import suppress
import hashlib
import json
import os
import platform
from pathlib import Path
import shlex
import signal
import socket
import statistics
import subprocess
import sys
import shutil
import traceback
import time

try:
    import idle_core
    import core_telemetry
except ModuleNotFoundError:
    from scripts.bench import idle_core, core_telemetry


ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / ".lake" / "build" / "bin" / "hexintfactor_bench"
ECM_BATCH = 256
BALANCED_SEED_COUNT = 5
BALANCED = (
    (32, 4_296_195_809),
    (40, 1_099_546_267_613),
    (48, 281_475_177_027_259),
    (56, 72_057_609_069_267_727),
    (64, 18_446_744_168_197_812_149),
    (72, 4_722_366_488_642_080_239_163),
    (80, 1_208_925_819_625_624_289_983_961),
)
ECM_CASES = (
    (48, 268_436_384_306_737),
    (56, 68_719_683_059_430_703),
    (64, 17_592_238_821_149_133_773),
    (72, 2_362_258_565_959_719_996_521),
    (76, 37_796_135_460_432_195_119_879),
    (80, 604_738_165_771_235_538_626_863),
)
FIXED_BUDGET_NANOS = {
    "runDefaultFuelSchedule": 2_000_000_000,
    "runTableDispatch": 10_000_000,
    "runTableTrial": 10_000_000,
    "runPMinusOneBatch": 100_000_000,
    "runEcmBatch": 100_000_000,
    "runEcmRhoBatch": 500_000_000,
    "runEcm48": 20_000_000,
    "runEcm56": 20_000_000,
    "runEcm64": 20_000_000,
    "runEcm72": 20_000_000,
    "runEcm76": 20_000_000,
    "runEcm80": 20_000_000,
    "runCyclotomicBatch": 10_000_000,
    "runPowerGenericBatch": 20_000_000,
    "runPowerSplitBatch": 20_000_000,
    "runDownstreamOrder": 10_000_000,
    "runDownstreamPrimitiveRoot": 20_000_000,
    **{
        f"runBalancedFactor{bits}": budget
        for bits, budget in (
            (32, 10_000_000), (40, 50_000_000), (48, 100_000_000),
            (56, 200_000_000), (64, 750_000_000),
            (72, 2_000_000_000), (80, 6_000_000_000),
        )
    },
    **{f"runBalancedCompletion{bits}": 10_000_000 for bits, _ in BALANCED},
}


class Attempt:
    """Append-only subprocess evidence; the output never implies acceptance early."""

    def __init__(self, output: Path):
        self.output = output.resolve()
        self.directory = Path(str(self.output) + ".attempt")
        self.output.parent.mkdir(parents=True, exist_ok=True)
        if self.output.exists():
            raise FileExistsError(self.output)
        self.directory.mkdir()  # Never overwrite a previous attempt, even a partial one.
        self.record: dict[str, object] = {
            "schema": "hex-int-factor-attempt/1", "status": "running",
            "command": sys.argv, "cwd": str(ROOT), "started_ns": time.time_ns(),
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commands": [],
        }
        self.save()

    def save(self) -> None:
        temporary = self.directory / "status.tmp"
        with temporary.open("w") as stream:
            stream.write(json.dumps(self.record, indent=2, sort_keys=True) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.output)

    def execute(self, command: list[str], *, stdin: str | None,
                timeout: float, allowed: tuple[int, ...]) -> subprocess.CompletedProcess[str]:
        commands = self.record["commands"]
        index = len(commands)
        stem = self.directory / f"command-{index:04d}"
        executable = shutil.which(command[0])
        entry = {
            "command": command, "stdin": stdin, "timeout_seconds": timeout,
            "started_ns": time.time_ns(), "status": "running",
            "executable": executable,
            "executable_sha256": sha256(Path(executable)) if executable else None,
            "stdout": str(stem) + ".stdout", "stderr": str(stem) + ".stderr",
        }
        commands.append(entry)
        self.save()
        # Files receive output as it is produced, including partial timeout output.
        with Path(entry["stdout"]).open("w") as stdout, Path(entry["stderr"]).open("w") as stderr:
            try:
                process_started = time.monotonic_ns()
                proc = subprocess.Popen(command, cwd=ROOT, text=True,
                    stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                    stdout=stdout, stderr=stderr, start_new_session=True)
                try:
                    proc.communicate(stdin, timeout=timeout)
                except BaseException:
                    # Give the monitor time to persist partial telemetry, then
                    # stop the entire group even if a descendant ignored TERM.
                    # WNOWAIT keeps the leader's PID reserved until killpg, so
                    # an early exit cannot redirect the kill to a reused PID.
                    entry["termination_grace_seconds"] = 5
                    try:
                        with suppress(ProcessLookupError):
                            os.killpg(proc.pid, signal.SIGTERM)
                        deadline = time.monotonic() + 5
                        while time.monotonic() < deadline:
                            if os.waitid(os.P_PID, proc.pid,
                                    os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None:
                                break
                            time.sleep(0.01)
                    finally:
                        with suppress(ProcessLookupError):
                            os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                        entry["termination_returncode"] = proc.returncode
                    raise
                process_elapsed = time.monotonic_ns() - process_started
                entry.update(returncode=proc.returncode, status="completed",
                             elapsed_nanos=process_elapsed)
            except BaseException as error:
                entry.update(status="failed", error_type=type(error).__name__, error=str(error))
                raise
            finally:
                entry["ended_ns"] = time.time_ns()
                self.save()
        result = subprocess.CompletedProcess(
            command, proc.returncode, Path(entry["stdout"]).read_text(),
            Path(entry["stderr"]).read_text())
        result.elapsed_nanos = process_elapsed
        if proc.returncode not in allowed:
            entry["status"] = "failed"
            self.save()
            raise subprocess.CalledProcessError(proc.returncode, command, result.stdout, result.stderr)
        return result


ACTIVE_ATTEMPT: Attempt | None = None


def run(command: list[str], *, stdin: str | None = None,
        timeout: float = 60.0, allowed: tuple[int, ...] = (0,)) -> subprocess.CompletedProcess[str]:
    if ACTIVE_ATTEMPT is not None:
        return ACTIVE_ATTEMPT.execute(command, stdin=stdin, timeout=timeout, allowed=allowed)
    process_started = time.monotonic_ns()
    proc = subprocess.run(command, cwd=ROOT, input=stdin, capture_output=True,
                          text=True, timeout=timeout)
    proc.elapsed_nanos = time.monotonic_ns() - process_started
    if proc.returncode not in allowed:
        raise subprocess.CalledProcessError(proc.returncode, command, proc.stdout, proc.stderr)
    return proc


def collect_attempt(args: argparse.Namespace) -> int:
    global ACTIVE_ATTEMPT
    attempt = Attempt(args.output)
    ACTIVE_ATTEMPT = attempt
    try:
        attempt.record["source_sha256"] = {
            name: sha256(ROOT / name)
            for name in git("ls-files").splitlines()
            if (ROOT / name).is_file()
        }
        attempt.record["commit"] = git("rev-parse", "HEAD")
        attempt.record["dirty_status"] = args.dirty_status
        attempt.save()
        return collect(args, attempt)
    except BaseException as error:
        attempt.record.update(status="rejected", error_type=type(error).__name__,
                              error=str(error), traceback=traceback.format_exc())
        raise
    finally:
        attempt.record["ended_ns"] = time.time_ns()
        try:
            attempt.record["state_after"] = host_state(attempt.record.get("cpu", 0))
        except Exception as error:
            attempt.record["state_after_error"] = str(error)
        attempt.save()
        ACTIVE_ATTEMPT = None


def verify_sources(attempt: Attempt) -> None:
    changed = [name for name, digest in attempt.record["source_sha256"].items()
               if not (ROOT / name).is_file() or sha256(ROOT / name) != digest]
    if changed:
        raise RuntimeError("sources changed during measurement: " + ", ".join(changed))


def git(*args: str) -> str:
    return run(["git", *args]).stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def version_line(command: list[str]) -> str:
    proc = run(command)
    lines = (proc.stdout or proc.stderr).splitlines()
    if not lines:
        raise RuntimeError(f"version command returned no output: {shlex.join(command)}")
    return lines[0].strip()


def host_state(cpu: int) -> dict[str, object]:
    model = "unknown"
    for block in Path("/proc/cpuinfo").read_text().split("\n\n"):
        fields = dict(
            line.split(":", 1) for line in block.splitlines() if ":" in line
        )
        if fields.get("processor", "").strip() == str(cpu):
            model = fields.get("model name", "unknown").strip()
            break
    pressure = Path("/proc/pressure/cpu")
    return {
        "cpu": cpu,
        "proc_stat": Path("/proc/stat").read_text(),
        "smt_siblings": sorted(idle_core.sibling_map().get(cpu, {cpu})),
        "frequency_khz": {p.name: p.read_text().strip() for p in
            Path(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq").glob("scaling_*")
            if p.is_file()},
        "affinity": sorted(os.sched_getaffinity(0)),
        "cpu_model": model,
        "load_average": list(os.getloadavg()),
        "cpu_pressure": (
            pressure.read_text().strip() if pressure.exists() else "unavailable"
        ),
    }


def median_row(samples: list[float]) -> dict[str, object]:
    return {
        "samples_nanos": samples,
        "median_nanos": statistics.median(samples),
        "min_nanos": min(samples),
        "max_nanos": max(samples),
    }


def result(export: dict[str, object], short_name: str) -> dict[str, object]:
    full = f"Hex.IntFactorBench.{short_name}"
    rows = export["results"]
    assert isinstance(rows, list)
    return next(row for row in rows if row["function"] == full)


def fixed_median(export: dict[str, object], short_name: str) -> float:
    return float(result(export, short_name)["median_nanos"])


def param_median(export: dict[str, object], short_name: str, param: int) -> float:
    row = result(export, short_name)
    samples = [
        float(point["per_call_nanos"])
        for point in row["points"]
        if point["status"] == "ok" and point["param"] == param
    ]
    if not samples:
        raise RuntimeError(f"{short_name}: no successful samples at {param}")
    return statistics.median(samples)


def validate_export(export: dict[str, object]) -> None:
    rows = export["results"]
    assert isinstance(rows, list)
    failures: list[str] = []
    for row in rows:
        name = str(row["function"])
        if row["kind"] == "parametric":
            if row["verdict"] != "consistent_with_declared_complexity":
                failures.append(f"{name}: verdict={row['verdict']}")
        else:
            if not row["hashes_agree"]:
                failures.append(f"{name}: repeat hashes disagree")
            ok_repeats = sum(point["status"] == "ok" for point in row["points"])
            if ok_repeats != row["config"]["repeats"]:
                failures.append(
                    f"{name}: only {ok_repeats}/{row['config']['repeats']} repeats completed"
                )
            check = row["expected_hash_check"]
            if check["status"] != "match":
                failures.append(f"{name}: expected hash {check['status']}")
            short = name.rsplit(".", 1)[-1]
            budget = FIXED_BUDGET_NANOS.get(short)
            if budget is None:
                failures.append(f"{name}: no registered scientific budget")
            elif float(row["median_nanos"]) > budget:
                failures.append(
                    f"{name}: median {row['median_nanos']} ns > {budget} ns budget"
                )
    if not any(row["function"] == "Hex.IntFactorBench.runDivisors" for row in rows):
        failures.append("missing public divisor registration")
    for bits, _ in BALANCED:
        normal = result(export, f"runBalancedFactor{bits}")
        completion = result(export, f"runBalancedCompletion{bits}")
        if normal["observed_hash"] != completion["observed_hash"]:
            failures.append(f"balanced-{bits}: full/completion output hashes differ")
    table = fixed_median(export, "runTableDispatch")
    trial = fixed_median(export, "runTableTrial")
    if result(export, "runTableDispatch")["observed_hash"] != \
            result(export, "runTableTrial")["observed_hash"]:
        failures.append("table: output hashes differ")
    if table / trial > 1.25:
        failures.append(f"table: dispatch/trial={table / trial:.6f} > 1.25")
    generic_power = result(export, "runPowerGenericBatch")
    split_power = result(export, "runPowerSplitBatch")
    if generic_power["observed_hash"] != split_power["observed_hash"]:
        failures.append("power: output hashes differ")
    power_ratio = float(split_power["median_nanos"]) / float(
        generic_power["median_nanos"]
    )
    if power_ratio > 0.98:
        failures.append(f"power: split/generic={power_ratio:.6f} > 0.98")
    if failures:
        raise RuntimeError("invalid scientific export:\n  " + "\n  ".join(failures))


def gp_batch(gp: str, n: int, repeats: int,
             timeout: float) -> tuple[float, int]:
    program = (
        f"my(t=getwalltime());my(f);for(i=1,{repeats},f=factor({n}));"
        "print(getwalltime()-t);print(factorback(f));quit\n"
    )
    lines = run([gp, "-fq"], stdin=program, timeout=timeout).stdout.splitlines()
    values = [line.strip() for line in lines if line.strip()]
    if len(values) != 2:
        raise RuntimeError(f"unexpected GP reply for {n}: {lines!r}")
    return float(values[0]) * 1_000_000.0 / repeats, int(values[1])


def measure_pari(gp: str, n: int, rounds: int, timeout: float) -> dict[str, object]:
    repeats = 1
    while True:
        per_call, product = gp_batch(gp, n, repeats, timeout)
        if product != n:
            raise RuntimeError(f"PARI product mismatch at {n}: {product}")
        if per_call * repeats >= 50_000_000 or repeats >= 1 << 20:
            break
        repeats *= 2
    samples = []
    for _ in range(rounds):
        per_call, product = gp_batch(gp, n, repeats, timeout)
        if product != n:
            raise RuntimeError(f"PARI product mismatch at {n}: {product}")
        samples.append(per_call)
    return {"batch_repeats": repeats, **median_row(samples)}


def ecm_batch(ecm: str, n: int, timeout: float) -> tuple[float, list[list[int]]]:
    proc = run(
        [ecm, "-q", "-sigma", "0:7", "1000", "1"],
        stdin=f"{n}\n" * ECM_BATCH, timeout=timeout,
        allowed=(0, 2, 6, 8, 10, 14),
    )
    # Only subprocess wall time belongs to the comparator protocol. Hashing
    # executables and persisting evidence happen outside this duration.
    elapsed = float(proc.elapsed_nanos) / ECM_BATCH
    if proc.returncode not in (0, 2, 6, 8, 10, 14):
        raise RuntimeError(f"GMP-ECM failed ({proc.returncode}) at {n}: {proc.stderr}")
    outputs = [
        [int(token) for token in line.split() if token.isdigit()]
        for line in proc.stdout.splitlines() if line.strip()
    ]
    if len(outputs) != ECM_BATCH:
        raise RuntimeError(
            f"GMP-ECM returned {len(outputs)} rows, expected {ECM_BATCH}, at {n}"
        )
    return elapsed, outputs


def measure_ecm(ecm: str, n: int, rounds: int,
                timeout: float) -> dict[str, object]:
    samples: list[float] = []
    example: list[int] = []
    for _ in range(rounds):
        per_call, outputs = ecm_batch(ecm, n, timeout)
        bad = any(
            row != [n] and (len(row) != 2 or row[0] * row[1] != n)
            for row in outputs
        )
        if bad:
            raise RuntimeError(f"GMP-ECM factor mismatch at {n}: {outputs[:3]}")
        samples.append(per_call)
        example = outputs[0]
    return {
        "batch_repeats": ECM_BATCH,
        **median_row(samples),
        "output_example": example,
        "found_factor": len(example) == 2,
    }


def render(record: dict[str, object]) -> None:
    if record.get("status", "accepted") != "accepted":
        raise RuntimeError("refusing to render unaccepted evidence")
    export = record["benchmark_export"]
    assert isinstance(export, dict)
    if record.get("scope") == "divisors":
        validate_divisors(export, record["divisor_audit"])
    print("| target | harness result |")
    print("|---|---|")
    for row in export["results"]:
        short = row["function"].rsplit(".", 1)[-1]
        if row["kind"] == "fixed":
            text = (
                f"median {row['median_nanos'] / 1e6:.3f} ms; "
                f"expected hash {row['expected_hash_check']['status']}"
            )
        else:
            text = row["verdict"]
        print(f"| `{short}` | {text} |")
    if record.get("scope") == "divisors":
        return
    controls = record["internal_controls"]
    print(
        "\n| bits | full factor | raw rho split | completion | "
        "full / rho | full / (rho + completion) |"
    )
    print("|---:|---:|---:|---:|---:|---:|")
    for row in controls["balanced"]:
        print(
            f"| {row['bits']} | {row['normal_nanos']/1e6:.3f} ms | "
            f"{row['rho_nanos']/1e6:.3f} ms | "
            f"{row['completion_nanos']/1e6:.3f} ms | "
            f"{row['full_over_rho']:.3f}x | "
            f"{row['full_over_rho_plus_completion']:.3f}x |"
        )
    print("\n| bits | Hex factor | PARI factor | Hex / PARI |")
    print("|---:|---:|---:|---:|")
    for row in record["comparisons"]["pari"]:
        print(
            f"| {row['bits']} | {row['lean_nanos']/1e6:.3f} ms | "
            f"{row['pari']['median_nanos']/1e6:.3f} ms | "
            f"{row['lean_over_pari']:.2f}x |"
        )
    overhead = record["comparisons"]["gmp_ecm_overhead"]["median_nanos"]
    print(f"\nGMP-ECM fixed-batch protocol floor: {overhead/1e6:.3f} ms/input\n")
    print("| bits | Hex ECM | GMP raw | GMP adjusted | factor | eligible | Hex / adjusted |")
    print("|---:|---:|---:|---:|:---:|:---:|---:|")
    for row in record["comparisons"]["gmp_ecm"]:
        ratio = f"{row['lean_over_adjusted']:.2f}x" if row["eligible"] else "—"
        print(
            f"| {row['bits']} | {row['lean_nanos']/1e6:.3f} ms | "
            f"{row['ecm']['median_nanos']/1e6:.3f} ms | "
            f"{row['adjusted_nanos']/1e6:.3f} ms | "
            f"{'yes' if row['ecm']['found_factor'] else 'no'} | "
            f"{'yes' if row['eligible'] else 'no'} | {ratio} |"
        )


DIVISOR_COUNTS = (64, 256, 1024, 4096, 16384, 32768)
DIVISOR_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
DIVISOR_CAMPAIGN = 4
DIVISOR_PROTOCOL = "reports/hex-int-factor-divisor-protocol-4.md"


def validate_divisor_audit(audit: str) -> dict[int, int]:
    """Independently reconstruct and compare every complete divisor array."""
    expected_hashes = {}
    lines = audit.splitlines()
    if len(lines) != len(DIVISOR_COUNTS):
        raise ValueError("divisor audit has missing or extra rows")
    for count, line in zip(DIVISOR_COUNTS, lines):
        param, subject, checksum, *values = map(int, line.split(","))
        expected = [1]
        for prime in DIVISOR_PRIMES[:count.bit_length() - 1]:
            expected += [d * prime for d in expected]
        expected.sort()
        if param != count or subject != expected[-1] or values != expected:
            raise ValueError(f"divisor audit mismatch at {count}")
        expected_hashes[count] = checksum
    return expected_hashes


def validate_divisors(export: dict, audit: str) -> None:
    """Independently reconstruct every output; check every trial and its checksum."""
    expected_hashes = validate_divisor_audit(audit)
    if "results" not in export:
        raise ValueError("no benchmark export")
    rows = export["results"]
    if len(rows) != 1 or rows[0]["function"] != "Hex.IntFactorBench.runDivisors":
        raise ValueError("expected exactly the public divisor registration")
    row = rows[0]
    config = row["config"]
    required = {"outer_trials": 7, "param_floor": 64, "param_ceiling": 32768,
                "target_inner_nanos": 1000000000, "max_seconds_per_call": 10,
                "signal_floor_multiplier": 1, "slope_tolerance": 0.15,
                "cache_mode": "warm", "verdict_warmup_fraction": 0.2,
                "narrow_range_noise_floor": 1.5}
    if any(config.get(key) != value for key, value in required.items()):
        raise ValueError("divisor configuration differs from preregistration")
    if config.get("param_schedule") != {"kind": "custom", "params": list(DIVISOR_COUNTS)}:
        raise ValueError("divisor schedule differs from preregistration")
    if row.get("verdict_dropped_leading") != 1:
        raise ValueError("divisor verdict must exclude exactly the registered warmup rung")
    points = row["points"]
    if len(points) != 7 * len(DIVISOR_COUNTS):
        raise ValueError("missing or extra divisor trials")
    for count in DIVISOR_COUNTS:
        group = [p for p in points if p["param"] == count]
        if sorted(p.get("trial_index", -1) for p in group) != list(range(7)):
            raise ValueError(f"divisor trial indices differ at {count}")
        if len(group) != 7 or any(p["status"] != "ok" or
                int(p["result_hash"], 16) != expected_hashes[count] for p in group):
            raise ValueError(f"divisor trial/hash failure at {count}")
    if row["verdict"] != "consistent_with_declared_complexity":
        raise RuntimeError(f"invalid scientific export: divisors verdict={row['verdict']}")


def inspect_divisors(attempt: Attempt, directory: Path, audit: str) -> None:
    """Record available evidence and validation without changing the disposition."""
    errors = {}
    for name, filename in (("benchmark_export", "bench.json"), ("telemetry", "telemetry.json")):
        try:
            attempt.record[name] = json.loads((directory / filename).read_text())
        except (OSError, ValueError) as error:
            errors[name] = str(error)
    attempt.record["ingestion_errors"] = errors
    try:
        validate_divisor_audit(audit)
        attempt.record["audit_validation"] = {"status": "passed"}
    except Exception as error:
        attempt.record["audit_validation"] = {
            "status": "failed", "error_type": type(error).__name__, "error": str(error)}
    try:
        validate_divisors(attempt.record.get("benchmark_export", {}), audit)
        attempt.record["scientific_validation"] = {"status": "passed"}
    except Exception as error:
        attempt.record["scientific_validation"] = {
            "status": "failed", "error_type": type(error).__name__, "error": str(error)}
    attempt.save()


def recheck_attempt(source: Path, output: Path) -> int:
    """Revalidate retained bytes; this can never turn a rejected run into acceptance."""
    record = json.loads(source.read_text())
    directory = Path(str(source) + ".attempt")
    attempt = Attempt(output)
    attempt.record.update(scope="divisor-recheck", status="diagnostic",
        original_status=record["status"], original_attempt=str(source),
        input_sha256={str(p): sha256(p) for p in
            (source, directory / "bench.json", directory / "telemetry.json") if p.exists()},
        unavailable_raw_artifacts=[str(p) for p in
            (directory / "bench.json", directory / "telemetry.json") if not p.exists()],
        validator_sha256=sha256(Path(__file__)))
    inspect_divisors(attempt, directory, record.get("divisor_audit", ""))
    print(json.dumps(attempt.record["scientific_validation"]))
    return 0 if attempt.record["scientific_validation"]["status"] == "passed" else 1


def collect_divisors(args: argparse.Namespace, attempt: Attempt, cpu: int) -> int:
    original_affinity = os.sched_getaffinity(0)
    try:
        if args.dirty_status:
            raise RuntimeError("divisor acceptance requires a clean worktree")
        attempt.record.update(scope="divisors", campaign=DIVISOR_CAMPAIGN,
            protocol=DIVISOR_PROTOCOL, state_before=host_state(cpu),
            host_activity_policy="context-only",
            smt_siblings=sorted(core_telemetry.sibling_set(cpu)))
        attempt.save()
        run(["lake", "build", "hexintfactor_bench"], timeout=900)
        attempt.record["benchmark_executable_sha256"] = sha256(BENCH)
        attempt.save()
        audit = run(["taskset", "-c", str(cpu), str(BENCH), "divisor-audit"], timeout=60).stdout
        attempt.record["divisor_audit"] = audit
        try:
            validate_divisor_audit(audit)
            attempt.record["audit_validation"] = {"status": "passed"}
        except Exception as error:
            attempt.record["audit_validation"] = {
                "status": "failed", "error_type": type(error).__name__,
                "error": str(error)}
            attempt.save()
            raise
        attempt.save()
        export_path = attempt.directory / "bench.json"
        telemetry_path = attempt.directory / "telemetry.json"
        try:
            run([sys.executable, str(ROOT / "scripts/bench/core_telemetry.py"),
                 "--cpu", str(cpu), "--output", str(telemetry_path),
                 "--interval", "0.25", "--", str(BENCH), "run", "--filter",
                 "Hex.IntFactorBench.runDivisors", "--export-file", str(export_path)],
                timeout=900)
        finally:
            inspect_divisors(attempt, attempt.directory, audit)
        if attempt.record["scientific_validation"]["status"] != "passed":
            raise RuntimeError("divisor validation failed; see retained scientific_validation")
        verify_sources(attempt)
        attempt.record["status"] = "accepted"
        attempt.save()
        render(attempt.record)
        return 0
    finally:
        os.sched_setaffinity(0, original_affinity)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--audit-attempt", type=Path, help="revalidate retained evidence without measurement")
    parser.add_argument("--pari", default="gp")
    parser.add_argument("--ecm", default="ecm")
    parser.add_argument("--cpu", default="auto")
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--allow-dirty", action="store_true")
    parser.add_argument("--divisors", action="store_true", help="collect only the preregistered divisor supplement")
    args = parser.parse_args()
    if args.report:
        render(json.loads(args.report.read_text()))
        return 0
    if args.output is None:
        parser.error("--output is required unless --report is used")
    if args.audit_attempt:
        return recheck_attempt(args.audit_attempt, args.output)
    if args.rounds < 5 or args.rounds % 2 == 0 or args.timeout <= 0:
        parser.error("--rounds must be odd and at least 5; --timeout must be positive")
    dirty = git("status", "--porcelain", "--untracked-files=all")
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty")

    args.dirty_status = dirty
    return collect_attempt(args)


def collect(args: argparse.Namespace, attempt: Attempt) -> int:
    dirty = args.dirty_status
    cpu = idle_core.resolve(args.cpu)
    attempt.record["cpu"] = cpu
    if args.divisors:
        return collect_divisors(args, attempt, cpu)
    idle_core.pin_self(cpu)
    before = host_state(cpu)
    attempt.record["state_before"] = before
    attempt.save()
    run(["lake", "build", "hexintfactor_bench", "HexIntFactorKernelProbe"],
        timeout=max(900.0, args.timeout))
    if not BENCH.exists():
        raise RuntimeError(f"missing benchmark executable: {BENCH}")

    attempt.record["benchmark_executable_sha256"] = sha256(BENCH)
    attempt.save()
    export_path = attempt.directory / "bench.json"
    run([
        str(BENCH), "run", "--filter", "Hex.IntFactorBench",
        "--export-file", str(export_path),
    ], timeout=max(1800.0, args.timeout))
    export = json.loads(export_path.read_text())
    attempt.record["benchmark_export"] = export
    attempt.save()
    validate_export(export)
    divisor_audit = run([str(BENCH), "divisor-audit"], timeout=60).stdout
    validate_divisors({"results": [result(export, "runDivisors")]}, divisor_audit)
    attempt.record["divisor_audit"] = divisor_audit
    attempt.save()

    control_output = run([str(BENCH), "control-audit"], timeout=120.0).stdout
    control_rows = [line.strip() for line in control_output.splitlines()
                    if line.strip()]
    expected_controls = ["table,success", *[
        f"balanced-{bits},success" for bits, _ in BALANCED
    ], "power,success"]
    if control_rows != expected_controls:
        raise RuntimeError(
            "control audit did not return the exact expected rows:\n"
            + control_output
        )
    fuel_rows = []
    for line in run([str(BENCH), "default-fuel"], timeout=600.0).stdout.splitlines():
        n, fuel, status, attempts = line.split(",")
        fuel_rows.append({
            "n": int(n), "default_fuel": int(fuel), "status": status,
            "attempts": int(attempts),
        })
    if any(row["status"] != "success" for row in fuel_rows):
        raise RuntimeError("default-fuel schedule contains a failure")

    balanced_rows = []
    pari_rows = []
    for bits, n in BALANCED:
        normal = result(export, f"runBalancedFactor{bits}")
        completion = result(export, f"runBalancedCompletion{bits}")
        normal_batch_ns = float(normal["median_nanos"])
        completion_ns = float(completion["median_nanos"])
        rho_ns = param_median(export, "runBalancedRho", bits)
        balanced_rows.append({
            "bits": bits, "n": n, "normal_nanos": normal_batch_ns,
            "rho_nanos": rho_ns, "completion_nanos": completion_ns,
            "public_route": "table-complete" if bits == 32 else "rho-driven",
            "full_over_rho": normal_batch_ns / rho_ns,
            "full_over_rho_plus_completion": normal_batch_ns /
                (rho_ns + completion_ns),
            "hash": normal["observed_hash"],
        })
        pari = measure_pari(args.pari, n, args.rounds, args.timeout)
        normal_ns = normal_batch_ns / BALANCED_SEED_COUNT
        pari_rows.append({
            "bits": bits, "n": n, "lean_batch_nanos": normal_batch_ns,
            "lean_seed_count": BALANCED_SEED_COUNT,
            "lean_nanos": normal_ns, "pari": pari,
            "lean_over_pari": normal_ns / float(pari["median_nanos"]),
        })
        print(f"measured balanced-{bits}", file=sys.stderr)

    overhead = measure_ecm(args.ecm, 15, args.rounds, args.timeout)
    overhead_ns = float(overhead["median_nanos"])
    ecm_rows = []
    for bits, n in ECM_CASES:
        external = measure_ecm(args.ecm, n, args.rounds, args.timeout)
        raw_ns = float(external["median_nanos"])
        adjusted = max(1.0, raw_ns - overhead_ns)
        fraction = overhead_ns / raw_ns
        lean_ns = fixed_median(export, f"runEcm{bits}")
        eligible = fraction <= 0.5 and raw_ns > overhead_ns
        ecm_rows.append({
            "bits": bits, "n": n, "lean_nanos": lean_ns,
            "ecm": external, "adjusted_nanos": adjusted,
            "overhead_fraction": fraction, "eligible": eligible,
            "lean_over_adjusted": lean_ns / adjusted,
        })
        print(f"measured ECM-{bits}", file=sys.stderr)

    table_dispatch = fixed_median(export, "runTableDispatch")
    table_trial = fixed_median(export, "runTableTrial")
    power_generic = fixed_median(export, "runPowerGenericBatch")
    power_split = fixed_median(export, "runPowerSplitBatch")
    record = {
        "schema": "hex-int-factor-phase4/3",
        "environment": {
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commit": git("rev-parse", "HEAD"),
            "dirty": bool(dirty), "dirty_status": dirty,
            "lean": run(["lake", "env", "lean", "--version"]).stdout.strip(),
            "lean_bench_sha256": sha256(BENCH),
            "kernel_source_sha256": sha256(ROOT / "bench/HexBench/IntFactorKernel.lean"),
            "pari_version": version_line([args.pari, "--version"]),
            "ecm_config": run([args.ecm, "-printconfig"]).stdout.strip(),
            "command": shlex.join(sys.argv),
            "state_before": before, "state_after": host_state(cpu),
        },
        "config": {
            "rounds": args.rounds, "timeout_seconds": args.timeout,
            "pari_timing": "GP getwalltime around a calibrated in-process factor batch",
            "gmp_ecm_command": f"{args.ecm} -q -sigma 0:7 1000 1",
            "gmp_ecm_batch_repeats": ECM_BATCH,
            "gmp_ecm_overhead_input": 15,
            "gmp_ecm_timing": "fixed persistent 256-input batch; B2 < B1 disables stage 2",
            "scientific_fixed_budget_nanos": FIXED_BUDGET_NANOS,
        },
        "benchmark_export": export,
        "control_audit": control_rows,
        "internal_controls": {
            "table": {
                "dispatch_nanos": table_dispatch, "trial_nanos": table_trial,
                "ratio": table_dispatch / table_trial,
                "hash": result(export, "runTableDispatch")["observed_hash"],
            },
            "balanced": balanced_rows,
            "power": {
                "generic_nanos": power_generic, "split_nanos": power_split,
                "split_over_generic": power_split / power_generic,
                "hash": result(export, "runPowerGenericBatch")["observed_hash"],
            },
        },
        "default_fuel_schedule": fuel_rows,
        "comparisons": {
            "pari": pari_rows,
            "gmp_ecm_overhead": overhead,
            "gmp_ecm": ecm_rows,
        },
    }
    attempt.record.update(record)
    verify_sources(attempt)
    attempt.record["status"] = "accepted"
    attempt.save()
    render(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
