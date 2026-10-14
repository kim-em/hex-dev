#!/usr/bin/env python3
"""Compare frozen native Sturm sources with the pinned LeanBench baseline rule.

Four trial-major AB/BA blocks run each full declared parent ladder once per
arm. Only outer-trial placement is changed; parameters, tuning, warmup and
signal-floor policy remain with the registration. All parent exports and
failures are retained. This is a computational regression check, not a new
Phase-4 complexity attestation or another sign-model rerun.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess

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
    return [name for name in parametric if name != AUXILIARY], native, excluded


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("baseline", "candidate", "baseline-source", "candidate-source", "guard", "root", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
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
    lease = None
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
        for arm in binaries:
            source = getattr(args, arm + "_source").resolve()
            sources[arm] = json.loads(source.read_text())
            (out / (arm + "-source.json")).write_bytes(source.read_bytes())
            if sources[arm]["status"]:
                raise RuntimeError("source snapshot is not a clean commit: " + arm)
            if digest(binaries[arm]) != sources[arm]["binary_sha256"]:
                raise RuntimeError("binary differs from frozen source binding: " + arm)
        for path, expected in sources["candidate"]["sources"].items():
            if digest(root / path) != expected:
                raise RuntimeError("candidate source changed: " + path)
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
        # conservatively allow only comments/line indentation in registrations.
        for path in ("bench/HexSturm/Bench.lean", "bench/HexSturm/Frontend.lean"):
            old = subprocess.check_output(["git", "show", sources["baseline"]["head"] + ":" + path], cwd=root)
            if hashlib.sha256(old).hexdigest() != sources["baseline"]["sources"][path]:
                raise RuntimeError("baseline registration source differs from snapshot")
            lines = lambda text: [line.strip() for line in strip_lean_comments(text).splitlines() if line.strip()]
            if lines(old.decode()) != lines((root / path).read_text()):
                raise RuntimeError("registration inputs/configuration changed: " + path)
        context["guard_sha256"] = digest(guard)
        context["lean_bench_revision"] = subprocess.check_output(
            ["git", "-C", str(root / ".lake/packages/lean-bench"), "rev-parse", "HEAD"], text=True).strip()
        cpu, lease = cpu_lease()
        context.update(cpu=cpu, original_affinity=sorted(os.sched_getaffinity(0)),
                       host=platform.node(), platform=platform.platform(), load_before=os.getloadavg())
        os.sched_setaffinity(0, {cpu})
        save()
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
        save()
        for arm, binary in binaries.items():
            code, _ = run([str(binary), "verify", *names, AUXILIARY, *fixed_lists[arm]], arm + "-verify")
            if code:
                raise RuntimeError("frozen native correctness verification failed")
        for trial in range(4):
            for index, name in enumerate(names):
                for arm in (("baseline", "candidate") if trial % 2 == 0 else ("candidate", "baseline")):
                    stem = f"{trial}-{index}-{arm}"
                    command = [str(binaries[arm]), "run", name, "--outer-trials", "1", "--export-file", str(out / (stem + ".json"))]
                    code, _ = run(command, stem)
                    if code:
                        raise RuntimeError("parent measurement failed: " + stem)
                documents = []
                for arm in ("baseline", "candidate"):
                    document = json.loads((out / f"{trial}-{index}-{arm}.json").read_text())
                    results = document["results"]
                    if len(results) != 1 or results[0]["kind"] != "parametric":
                        raise RuntimeError("invalid parent result: " + name)
                    documents.append(results[0])
                a, b = documents
                if any(result["budget_truncated"] or not result["points"] or
                       any(point["status"] != "ok" or point["result_hash"] is None for point in result["points"])
                       for result in documents):
                    raise RuntimeError("incomplete/failed parent measurement: " + name)
                signature = lambda result: (result["function"], result["config"],
                                            [(point["param"], point["result_hash"]) for point in result["points"]])
                if a["function"] != name or signature(a) != signature(b):
                    raise RuntimeError("cross-arm input/configuration/hash mismatch: " + name)
                print(f"block {trial}: {name} source pair retained", flush=True)
        verdicts = []
        for index, name in enumerate(names):
            paths = [str(out / f"{trial}-{index}-{arm}.json") for arm in ("baseline", "candidate") for trial in range(4)]
            code, _ = run([str(guard), str(out / f"guard-{index}.json"), *paths], f"guard-{index}")
            verdicts.append({"function": name, "returncode": code, "report": f"guard-{index}.json"})
        context["guards"] = verdicts
        context["status"] = "completed"
        context["pass"] = all(item["returncode"] == 0 for item in verdicts)
    except BaseException as exc:
        context.update(status="failed", error=str(exc))
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
        context["guard_unchanged"] = digest_after(guard) == context.get("guard_sha256")
        if changed or not context["guard_unchanged"] or any(context["binaries_after"][arm] != sources.get(arm, {}).get("binary_sha256") for arm in binaries):
            context["pass"] = False
            context["integrity_failure"] = True
        save()
        if lease is not None:
            lease.close()
    return 0 if context.get("pass") else 1


if __name__ == "__main__":
    raise SystemExit(main())
