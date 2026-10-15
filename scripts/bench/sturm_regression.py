#!/usr/bin/env python3
"""Compare frozen native Sturm sources with the pinned LeanBench baseline rule.

Four trial-major AB/BA blocks run each full declared parent ladder once per
arm. Parameters, tuning, warmup and
signal-floor policy remain with the registration. All parent exports and
failures are retained. This is a computational regression check, not a new
Phase-4 complexity attestation or another sign-model rerun.
An explicitly bound cap adaptation may increase the safety timeout in both
arms after one original two-arm cap failure; it cannot change the verdict rule.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys

from cpu_lease import cpu_lease
from sweep_freshness import strip_lean_comments


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# The existing owner disposition gives this auxiliary traversal no timing claim.
AUXILIARY = "Hex.SturmBench.runSigns"
NATIVE_FIXED = {"Hex.SturmExternalBench.runNative" + suffix
                for suffix in ("Count", "Mixed", "Negative", "Common", "4", "16", "32", "64")}


def native_harness_pins(manifest: dict) -> dict:
    """Keep the runner and its CLI dependency fixed; ignore proof-only pins."""
    wanted = {"Cli", "«lean-bench»"}
    selected = {entry["name"]: {key: entry.get(key) for key in ("type", "url", "rev", "subDir")}
                for entry in manifest["packages"] if entry["name"] in wanted}
    if set(selected) != wanted:
        raise RuntimeError("missing native harness dependency pin")
    return selected


def registrations(text: str) -> tuple[list[str], list[str], list[str]]:
    """Select claimed timing ladders and require every known native hash control."""
    if "no Hashable" in text:
        raise RuntimeError("unhashed benchmark registration")
    parametric = sorted(line.strip().split()[0] for line in text.splitlines()
                        if "expected complexity:" in line)
    fixed = sorted(line.strip().split()[0] for line in text.splitlines() if "[fixed]" in line)
    if not parametric or len(set(parametric)) != len(parametric) or not all(
            name.startswith(("Hex.SturmBench.", "Hex.SturmFrontendBench.")) for name in parametric):
        raise RuntimeError("unexpected computational benchmark registration")
    if AUXILIARY not in parametric:
        raise RuntimeError("auxiliary registration missing; recheck the scope disposition")
    native = [name for name in fixed if name.startswith("Hex.SturmExternalBench.runNative")]
    if len(set(fixed)) != len(fixed) or not NATIVE_FIXED.issubset(native):
        raise RuntimeError("missing or duplicate native fixed correctness controls")
    excluded = [AUXILIARY] + [name for name in fixed if name not in native]
    selected = [name for name in parametric if name != AUXILIARY]
    if not selected:
        raise RuntimeError("empty timing selection")
    return selected, native, excluded


TOOL_SOURCES = ("scripts/bench/sturm_regression.py", "scripts/bench/cpu_lease.py",
                "scripts/bench/sweep_freshness.py", "bench/HexSturm/CompareExports.lean")


def state_directory():
    value = os.environ.get("XDG_STATE_HOME", "")
    return Path(value) if value and Path(value).is_absolute() else Path.home() / ".local/state"


def validate_cap_protocol(previous_dir, policy, sources, identity, reservation, names):
    """Bind one cap increase to the retained, consumed two-arm cap failure.

    The new collector may have a new source commit, but the native binaries,
    guard and every recorded producer/registration input must remain unchanged.
    A different cap or decision cannot create another adaptation reservation.
    """
    if not isinstance(policy, dict) or set(policy) != {
            "seconds", "reason", "benchmarks", "previous_context_sha256", "previous_exports"}:
        raise RuntimeError("incomplete cap protocol")
    seconds = policy["seconds"]
    if isinstance(seconds, bool) or not isinstance(seconds, (int, float)) or not math.isfinite(seconds) or seconds <= 0:
        raise RuntimeError("invalid cap seconds")
    if not isinstance(policy["reason"], str) or not policy["reason"].strip():
        raise RuntimeError("missing cap protocol reason")
    previous_dir = previous_dir.resolve()
    previous_path = previous_dir / "context.json"
    previous = json.loads(previous_path.read_text())
    journal = json.loads(reservation.read_text())
    previous_hash = digest(previous_path)
    if (journal.get("first_output") != str(previous_dir) or
            journal.get("context_sha256") != previous_hash or
            policy["previous_context_sha256"] != previous_hash):
        raise RuntimeError("cap protocol differs from retained first attempt")
    if (previous.get("status") != "failed" or previous.get("integrity_failure") or
            previous.get("attempt_reserved") is not True or
            previous.get("measurements_collected") is not True or
            previous.get("reruns") != 0 or previous.get("cap_protocol") is not None):
        raise RuntimeError("cap adaptation requires an intact original failed comparison")
    if previous.get("comparison_identity") != identity or previous.get("guard_unchanged") is not True:
        raise RuntimeError("cap adaptation changes the native binaries or guard")
    if policy["benchmarks"] != names or previous.get("benchmarks") != names:
        raise RuntimeError("cap protocol must cover every original timing family")
    for arm, source in sources.items():
        old_source = previous.get("sources", {}).get(arm, {})
        if (old_source.get("binary_sha256") != source["binary_sha256"] or
                old_source.get("sources") != source["sources"]):
            raise RuntimeError("cap adaptation changes frozen producer inputs: " + arm)
    failures = previous.get("parent_failures", [])
    if len(failures) != 2 or [f.get("arm") for f in failures] != ["baseline", "candidate"]:
        raise RuntimeError("cap adaptation requires both original source arms")
    if failures[0].get("function") != failures[1].get("function"):
        raise RuntimeError("cap failures concern different timing families")
    exports = {}
    failed_params = []
    for failure in failures:
        points = failure.get("points", [])
        killed = [p.get("param") for p in points if p.get("status") == "killed_at_cap"]
        if (failure.get("budget_truncated") is not False or not killed or
                any(p.get("status") not in {"ok", "killed_at_cap"} for p in points)):
            raise RuntimeError("original failure is not a per-call cap termination")
        failed_params.append(killed)
        # Identify the source arm by the actual retained source-pair filenames,
        # rather than assuming that executable basenames are "baseline"/"candidate".
        commands = [r["command"] for r in previous.get("commands", [])
                    if len(r.get("command", [])) > 2 and r["command"][1:3] == ["run", failure["function"]]
                    and "--export-file" in r["command"]
                    and Path(r["command"][r["command"].index("--export-file") + 1]).name.endswith(
                        "-" + failure["arm"] + ".json")]
        if not commands:
            raise RuntimeError("missing original failed export")
        command = commands[-1]
        path = Path(command[command.index("--export-file") + 1])
        if path.parent.resolve() != previous_dir:
            raise RuntimeError("original failed export is outside its retained directory")
        exports[path.name] = digest(path)
        document = json.loads(path.read_text())
        results = document.get("results", [])
        if len(results) != 1 or results[0].get("function") != failure["function"]:
            raise RuntimeError("original failed export has a different subject")
        result = results[0]
        statuses = [{k: p.get(k) for k in ("param", "status", "error")} for p in result.get("points", [])]
        if statuses != points or result.get("budget_truncated") is not False:
            raise RuntimeError("original failed export differs from reserved failure")
        old_cap = result.get("config", {}).get("max_seconds_per_call")
        if (isinstance(old_cap, bool) or not isinstance(old_cap, (int, float)) or
                not math.isfinite(old_cap) or old_cap <= 0 or seconds <= old_cap):
            raise RuntimeError("cap protocol must increase the failed per-call limit")
    if failed_params[0] != failed_params[1]:
        raise RuntimeError("source arms hit different cap parameters")
    if policy["previous_exports"] != exports:
        raise RuntimeError("cap protocol differs from retained failed export hashes")
    return {"directory": str(previous_dir), "context_sha256": previous_hash,
            "exports": exports, "policy": policy}


def install_signals():
    def interrupt(signum, _frame):
        raise KeyboardInterrupt("signal " + str(signum))
    for signum in (signal.SIGTERM, signal.SIGHUP):
        if signal.getsignal(signum) != signal.SIG_IGN:
            signal.signal(signum, interrupt)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("baseline", "candidate", "baseline-source", "candidate-source", "guard", "root", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--decision", type=Path, required=True)
    parser.add_argument("--preflight", action="store_true",
                        help="validate bindings and correctness controls without leasing a CPU or timing")
    parser.add_argument("--rerun-of", type=Path,
                        help="one unchanged rerun of a completed inconclusive comparison")
    parser.add_argument("--cap-from", type=Path,
                        help="one reviewed cap increase after the retained original two-arm cap failure")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    out = args.output.resolve()
    if out == root or root in out.parents:
        parser.error("collect outside the frozen source tree")
    out.mkdir(parents=True, exist_ok=False)
    binaries = {arm: getattr(args, arm).resolve() for arm in ("baseline", "candidate")}
    sources = {}
    guard = args.guard.resolve()
    context = {"question": "Does the current native Sturm computation regress against the most recent committed measured source?",
               "classification": "Computational baseline comparison; no new complexity or proof-cost verdict",
               "trials": 4, "order": "trial-major, full-ladder adjacent source arms, AB on even blocks and BA on odd blocks",
               "threshold_percent": 10, "script_sha256": digest(Path(__file__)),
               "commands": [], "sources": sources,
               "launch_directory": str(root),
               "env_scope": "Parent export git fields describe the launch directory. Frozen source manifests and binary hashes identify each executable's implementation.",
               "reruns": 0, "status": "running"}
    context["mode"] = "preflight" if args.preflight else "comparison"
    context["measurements_collected"] = False
    context["attempt_reserved"] = False
    lease = None
    first_reservation = None
    environment = {**os.environ, "LEAN_ABORT_ON_PANIC": "1"}

    def save():
        (out / "context.json").write_text(json.dumps(context, indent=2) + "\n")

    def run(command: list[str], label: str) -> tuple[int, str]:
        record = {"command": command, "stdout": label + ".stdout", "stderr": label + ".stderr",
                  "load_before": os.getloadavg(), "status": "running"}
        context["commands"].append(record)
        save()
        with (out / record["stdout"]).open("w") as stdout, (out / record["stderr"]).open("w") as stderr:
            result = subprocess.run(command, cwd=root, env=environment, stdout=stdout, stderr=stderr)
        record.update(returncode=result.returncode, load_after=os.getloadavg(), status="completed")
        save()
        return result.returncode, (out / record["stdout"]).read_text()

    try:
        save()
        decision_bytes = args.decision.read_bytes()
        decision = json.loads(decision_bytes)
        (out / "decision.json").write_bytes(decision_bytes)
        context["decision_sha256"] = hashlib.sha256(decision_bytes).hexdigest()
        for field in ("question", "interruption", "regression", "inconclusive_rerun"):
            if not isinstance(decision.get(field), str) or not decision[field].strip():
                raise RuntimeError("missing decision policy: " + field)
        if decision.get("interruption_consumes_decision") is not True:
            raise RuntimeError("decision must retain interruptions after reservation as consumed attempts")
        build = decision.get("guard_build", {})
        if build.get("result") != "success" or not isinstance(build.get("command"), list) or not build["command"] or not all(isinstance(arg, str) and arg for arg in build["command"]):
            raise RuntimeError("missing successful frozen guard build attestation")
        if decision.get("script_sha256") != context["script_sha256"]:
            raise RuntimeError("collector differs from decision binding")
        if decision.get("guard_sha256") != digest(guard):
            raise RuntimeError("guard differs from decision binding")
        if set(decision.get("tool_sources", {})) != set(TOOL_SOURCES):
            raise RuntimeError("incomplete tool source bindings")
        for path, expected in decision["tool_sources"].items():
            if digest(root / path) != expected:
                raise RuntimeError("tool source differs from decision binding: " + path)
        context["loaded_helpers"] = {}
        for module in ("cpu_lease", "sweep_freshness"):
            path = Path(sys.modules[module].__file__).resolve()
            if digest(path) != decision["tool_sources"]["scripts/bench/" + module + ".py"]:
                raise RuntimeError("loaded helper differs from decision binding: " + module)
            context["loaded_helpers"][str(path)] = digest(path)
        if decision["tool_sources"][TOOL_SOURCES[0]] != context["script_sha256"]:
            raise RuntimeError("launch collector differs from frozen tree")
        context["tool_sources"] = decision["tool_sources"]
        context["guard_sha256"] = decision["guard_sha256"]
        for arm in binaries:
            source = getattr(args, arm + "_source").resolve()
            if digest(source) != decision.get(arm + "_source_sha256"):
                raise RuntimeError("source manifest differs from decision binding: " + arm)
            sources[arm] = json.loads(source.read_text())
            (out / (arm + "-source.json")).write_bytes(source.read_bytes())
            if sources[arm]["status"]:
                raise RuntimeError("source snapshot is not a clean commit: " + arm)
            if digest(binaries[arm]) != sources[arm]["binary_sha256"]:
                raise RuntimeError("binary differs from frozen source binding: " + arm)
        for path, expected in sources["candidate"]["sources"].items():
            if digest(root / path) != expected:
                raise RuntimeError("candidate source changed: " + path)
        if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() != sources["candidate"]["head"]:
            raise RuntimeError("candidate tree differs from frozen commit")
        if build.get("source_head") != sources["candidate"]["head"]:
            raise RuntimeError("guard build attestation names a different source")
        if subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip():
            raise RuntimeError("candidate tree is not clean")
        harness = lambda source: {path: sha for path, sha in source["sources"].items()
                                  if path.startswith(".lake/packages/lean-bench/")}
        if not harness(sources["baseline"]) or harness(sources["baseline"]) != harness(sources["candidate"]):
            raise RuntimeError("benchmark harness sources differ")
        if sources["baseline"]["sources"]["lean-toolchain"] != sources["candidate"]["sources"]["lean-toolchain"]:
            raise RuntimeError("source toolchains differ")
        old_manifest_bytes = subprocess.check_output(
            ["git", "show", sources["baseline"]["head"] + ":lake-manifest.json"], cwd=root)
        if hashlib.sha256(old_manifest_bytes).hexdigest() != sources["baseline"]["sources"]["lake-manifest.json"]:
            raise RuntimeError("baseline dependency manifest differs from snapshot")
        old_pins = native_harness_pins(json.loads(old_manifest_bytes))
        new_pins = native_harness_pins(json.loads((root / "lake-manifest.json").read_text()))
        if old_pins != new_pins:
            raise RuntimeError("native harness dependency pins differ")
        context["native_harness_pins"] = new_pins
        # Bind the old source read from git to its retained snapshot, then
        # allow comments and trailing whitespace, preserving meaningful indentation.
        for path in ("bench/HexSturm/Bench.lean", "bench/HexSturm/Frontend.lean"):
            old = subprocess.check_output(["git", "show", sources["baseline"]["head"] + ":" + path], cwd=root)
            if hashlib.sha256(old).hexdigest() != sources["baseline"]["sources"][path]:
                raise RuntimeError("baseline registration source differs from snapshot")
            lines = lambda text: [line.rstrip() for line in strip_lean_comments(text).splitlines() if line.strip()]
            if lines(old.decode()) != lines((root / path).read_text()):
                raise RuntimeError("registration inputs/configuration changed: " + path)
        if digest(guard) != context["guard_sha256"]:
            raise RuntimeError("guard changed during binding validation")
        context["lean_bench_revision"] = subprocess.check_output(
            ["git", "-C", str(root / ".lake/packages/lean-bench"), "rev-parse", "HEAD"], text=True).strip()
        context.update(host=platform.node(), platform=platform.platform())
        save()
        identity = {arm: sources[arm]["binary_sha256"] for arm in binaries}
        identity["guard"] = context["guard_sha256"]
        context["comparison_identity"] = hashlib.sha256(
            json.dumps(identity, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        state_root = state_directory()
        reservation_dir = state_root / "hex" / "sturm-comparisons"
        original_marker = reservation_dir / (context["comparison_identity"] + ".json")
        decision_marker = original_marker
        if (args.cap_from is None) != (decision.get("cap_protocol") is None):
            raise RuntimeError("--cap-from and the bound cap_protocol are required together")
        if args.cap_from is not None:
            # One stable slot per native comparison, independent of the chosen
            # cap, decision wording or collector digest. Never replace the old slot.
            decision_marker = reservation_dir / (context["comparison_identity"] + "-cap.json")
        context["decision_reservation"] = str(decision_marker)
        if args.rerun_of is None and decision_marker.exists() and not args.preflight:
            raise RuntimeError("decision already used; an eligible --rerun-of is required")
        if args.rerun_of is not None:
            previous_path = args.rerun_of.resolve() / "context.json"
            previous = json.loads(previous_path.read_text())
            if previous.get("status") != "completed" or previous.get("outcome") != "inconclusive" or previous.get("integrity_failure"):
                raise RuntimeError("rerun requires a completed inconclusive comparison")
            if previous.get("reruns") != 0:
                raise RuntimeError("cannot rerun a rerun")
            for field in ("sources", "script_sha256", "guard_sha256", "tool_sources", "decision_sha256", "comparison_identity"):
                if previous.get(field) != context.get(field):
                    raise RuntimeError("rerun bindings differ: " + field)
            reservation = json.loads(decision_marker.read_text())
            if reservation.get("first_output") != str(args.rerun_of.resolve()) or reservation.get("context_sha256") != digest(previous_path):
                raise RuntimeError("rerun does not match retained first decision attempt")
            marker = args.rerun_of.resolve() / "unchanged-rerun.json"
            if marker.exists():
                raise RuntimeError("unchanged rerun already reserved")
            context.update(reruns=1, rerun_of=str(args.rerun_of.resolve()),
                           previous_context_sha256=digest(previous_path))
        lists = {}
        fixed_lists = {}
        excluded_lists = {}
        for arm, binary in binaries.items():
            code, text = run([str(binary), "list"], arm + "-list")
            if code:
                raise RuntimeError("cannot inspect frozen benchmark registrations")
            lists[arm], fixed_lists[arm], excluded_lists[arm] = registrations(text)
        if lists["baseline"] != lists["candidate"] or fixed_lists["baseline"] != fixed_lists["candidate"] or excluded_lists["baseline"] != excluded_lists["candidate"]:
            raise RuntimeError("source arms have different benchmark registrations")
        names = lists["candidate"]
        context["benchmarks"] = names
        context["verified_native_fixed"] = fixed_lists["candidate"]
        context["excluded_registrations"] = excluded_lists["candidate"]
        context["excluded"] = "The auxiliary runSigns traversal has no timing claim under the existing owner disposition. Fixed expected-hash cases have no timing claim in hex-sturm-performance.md; native cases are verified. External FLINT/Z3 comparisons remain informational owner evidence."
        if args.cap_from is not None:
            context["cap_protocol"] = validate_cap_protocol(
                args.cap_from, decision["cap_protocol"], sources, context["comparison_identity"],
                original_marker, names)
        save()
        for arm, binary in binaries.items():
            code, _ = run([str(binary), "verify", *names, AUXILIARY, *fixed_lists[arm]], arm + "-verify")
            if code:
                raise RuntimeError("frozen native correctness verification failed")
        if not args.preflight:
            cpu, lease = cpu_lease()
            context.update(cpu=cpu, original_affinity=sorted(os.sched_getaffinity(0)),
                           load_before=os.getloadavg())
            os.sched_setaffinity(0, {cpu})
            if args.rerun_of is not None:
                with marker.open("x") as handle:
                    context["attempt_reserved"] = True
                    json.dump({"output": str(out), "previous_context_sha256": digest(previous_path)}, handle)
            else:
                reservation_dir.mkdir(parents=True, exist_ok=True)
                with decision_marker.open("x") as handle:
                    first_reservation = decision_marker
                    context["attempt_reserved"] = True
                    json.dump({"first_output": str(out)}, handle)
            context["attempt_reserved"] = True
        for trial in range(0 if args.preflight else 4):
            for index, name in enumerate(names):
                for arm in (("baseline", "candidate") if trial % 2 == 0 else ("candidate", "baseline")):
                    stem = f"{trial}-{index}-{arm}"
                    command = [str(binaries[arm]), "run", name, "--outer-trials", "1", "--export-file", str(out / (stem + ".json"))]
                    if args.cap_from is not None:
                        command += ["--max-seconds-per-call", str(decision["cap_protocol"]["seconds"])]
                    code, _ = run(command, stem)
                    context["measurements_collected"] = True
                    if code:
                        failure = {"arm": arm, "function": name, "returncode": code,
                                   "export": stem + ".json"}
                        exported = out / (stem + ".json")
                        if exported.exists():
                            try:
                                failure["results"] = json.loads(exported.read_text()).get("results")
                            except (OSError, ValueError) as exc:
                                failure["export_error"] = str(exc)
                        context["parent_failures"] = [failure]
                        raise RuntimeError("parent measurement failed: " + stem)
                documents = []
                for arm in ("baseline", "candidate"):
                    document = json.loads((out / f"{trial}-{index}-{arm}.json").read_text())
                    results = document["results"]
                    if len(results) != 1 or results[0]["kind"] != "parametric":
                        raise RuntimeError("invalid parent result: " + name)
                    documents.append(results[0])
                a, b = documents
                if args.cap_from is not None and any(
                        result["config"].get("max_seconds_per_call") != decision["cap_protocol"]["seconds"]
                        for result in documents):
                    raise RuntimeError("parent did not apply the bound per-call cap")
                if any(result["budget_truncated"] or not result["points"] or
                       any(point["status"] != "ok" or point["result_hash"] is None for point in result["points"])
                       for result in documents):
                    context["parent_failures"] = [
                        {"arm": arm, "function": result["function"],
                         "budget_truncated": result["budget_truncated"],
                         "points": [{key: point.get(key) for key in ("param", "status", "error")}
                                    for point in result["points"]]}
                        for arm, result in zip(("baseline", "candidate"), documents)]
                    raise RuntimeError("incomplete/failed parent measurement: " + name)
                signature = lambda result: (result["function"], result["config"],
                                            [(point["param"], point["result_hash"]) for point in result["points"]])
                if a["function"] != name or signature(a) != signature(b):
                    raise RuntimeError("cross-arm input/configuration/hash mismatch: " + name)
                ratios = []
                for left, right in zip(a["points"], b["points"]):
                    x, y = left.get("per_call_nanos"), right.get("per_call_nanos")
                    valid = all(isinstance(value, (int, float)) and math.isfinite(value) and value > 0
                                for value in (x, y))
                    ratios.append({"param": left["param"], "candidate_over_baseline": y / x if valid else None})
                context.setdefault("paired_ratios", []).append(
                    {"block": trial, "function": name, "scope": "descriptive only; does not change guard verdict", "ratios": ratios})
                print(f"block {trial}: {name} source pair retained", flush=True)
        verdicts = []
        for index, name in enumerate([] if args.preflight else names):
            paths = [str(out / f"{trial}-{index}-{arm}.json") for arm in ("baseline", "candidate") for trial in range(4)]
            code, _ = run([str(guard), str(out / f"guard-{index}.json"), *paths], f"guard-{index}")
            verdicts.append({"function": name, "returncode": code, "report": f"guard-{index}.json"})
        context["guards"] = verdicts
        context["status"] = "completed"
        codes = {item["returncode"] for item in verdicts}
        context["regression_findings"] = [item["function"] for item in verdicts if item["returncode"] == 1]
        context["outcome"] = ("preflight" if args.preflight else
                              "invalid" if codes - {0, 1, 2} else
                              "regression" if 1 in codes else
                              "inconclusive" if 2 in codes else "pass")
        if not args.preflight:
            context["pass"] = context["outcome"] == "pass"
    except BaseException as exc:
        context.update(status="interrupted" if isinstance(exc, (KeyboardInterrupt, SystemExit)) else "failed", error=str(exc))
        raise
    finally:
        def digest_after(path):
            try:
                return digest(path)
            except OSError:
                return None
        context.update(load_after=os.getloadavg(), binaries_after={arm: digest_after(binary) for arm, binary in binaries.items()})
        changed = [path for path, expected in sources.get("candidate", {}).get("sources", {}).items()
                   if digest_after(root / path) != expected]
        context["candidate_source_changes"] = changed
        context["guard_unchanged"] = (digest_after(guard) == context["guard_sha256"]
                                      if "guard_sha256" in context else None)
        tools_changed = [path for path, expected in context.get("tool_sources", {}).items()
                         if digest_after(root / path) != expected]
        context["tool_source_changes"] = tools_changed
        helpers_changed = [path for path, expected in context.get("loaded_helpers", {}).items()
                           if digest_after(Path(path)) != expected]
        context["loaded_helper_changes"] = helpers_changed
        script_changed = digest_after(Path(__file__)) != context["script_sha256"]
        if changed or tools_changed or helpers_changed or script_changed or context["guard_unchanged"] is False or any(
                context["binaries_after"][arm] != source["binary_sha256"]
                for arm, source in sources.items() if "binary_sha256" in source):
            context["pass"] = False
            context["integrity_failure"] = True
            context["outcome"] = "invalid"
        save()
        if first_reservation is not None:
            temporary = first_reservation.with_suffix(".tmp")
            temporary.write_text(json.dumps({"first_output": str(out), "context_sha256": digest(out / "context.json")}))
            temporary.replace(first_reservation)
        if lease is not None:
            lease.close()
    return 0 if (context.get("pass") or context.get("outcome") == "preflight") and not context.get("integrity_failure") else 1


if __name__ == "__main__":
    install_signals()
    raise SystemExit(main())
