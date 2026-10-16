"""Verify the retained bounded comparison without running measurements."""

import gzip
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    require(sys.argv[1:] in ([], ["--current"]), "usage: replay.py [--current]")
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "manifest.json").read_text())
    raw = {}
    for entry in manifest["files"]:
        path = entry["path"]
        require(path not in raw, "duplicate archive entry")
        compressed = (root / path).read_bytes()
        require(hashlib.sha256(compressed).hexdigest() == entry["gzip_sha256"], path)
        data = gzip.decompress(compressed)
        require(hashlib.sha256(data).hexdigest() == entry["raw_sha256"], path)
        require(len(data) == entry["raw_bytes"], path)
        raw[path] = data

    def read(path):
        return json.loads(raw["capture/" + path + ".gz"])

    decision = read("decision.json")
    proposal = read("proposal.json")
    require(all(decision[key] == value for key, value in proposal.items()), "proposal/decision agreement")
    criterion = decision["criterion"]
    require(criterion == {"must_improve": [["height", 128], ["height", 2048], ["third", 1024]],
                          "minimum_improvement_percent": 10,
                          "maximum_neighbor_regression_percent": 10}, "recorded six-case rule")
    context = read("comparison/context.json")
    require(context["status"] == "completed" and context["inputs_unchanged"], "incomplete attempt")
    require(hashlib.sha256(raw["capture/decision.json.gz"]).hexdigest() ==
            context["decision_sha256"], "decision binding")
    sources = {arm: read(arm + "-source.json") for arm in ("baseline", "candidate")}
    for arm, source in sources.items():
        require(hashlib.sha256(raw["capture/" + arm + "-source.json.gz"]).hexdigest() ==
                decision["source_manifests"][arm], "source manifest binding")
        require(source["binary_sha256"] == context["binaries"][arm], "binary binding")
        require(source["head"] == context["source_heads"][arm], "source commit binding")
        before = read(arm + "-inputs-before.json")
        require(before == read(arm + "-inputs-after.json"), "independent before/after build inventories")
        require(all(source[key] == value for key, value in before.items()), "recorded build inputs")
        require(source["status"] == "" and source["build_result"] == "success" and
                source["inputs_unchanged"] and source["executable"], "build status")
        require(len(source["sources"]) == decision["source_scope"]["bound_inputs_per_arm"] and
                len(source["packages"]) == 16 and len(source["native_import_closure"]["files"]) ==
                decision["source_scope"]["native_files_per_arm"], "input counts")
    require(sources["baseline"]["head"] == manifest["baseline_commit"] == decision["parent"],
            "baseline commit")
    require(sources["candidate"]["head"] == manifest["source_commit"], "candidate commit")
    require(context["binaries"] == manifest["binaries"], "reported executable hashes")
    require(sources["baseline"]["packages"] == sources["candidate"]["packages"], "dependency pins")
    for field, expected_diff in (("sources", set(decision["source_scope"]["changed_inputs"])),
                                 ("native_import_closure", set(decision["source_scope"]["changed_native_inputs"]))):
        values = [sources[arm][field] for arm in ("baseline", "candidate")]
        if field == "native_import_closure":
            values = [value["files"] for value in values]
        require(set(values[0]) == set(values[1]) and
                {path for path in values[0] if values[0][path] != values[1][path]} == expected_diff,
                "changed inputs: " + field)
    if sys.argv[1:] == ["--current"]:
        repository = root.parents[2]
        current_inputs = dict(sources["candidate"]["native_import_closure"]["files"])
        for path in ("HexOrderedFn/Tests.lean", "lean-toolchain", "lakefile.lean", "lake-manifest.json"):
            current_inputs[path] = sources["candidate"]["sources"][path]
        for path, expected_hash in current_inputs.items():
            require(hashlib.sha256((repository / path).read_bytes()).hexdigest() ==
                    expected_hash, "reviewed source: " + path)
    for name in ("probe.py", "freeze_build.py"):
        expected_hashes = [value for path, value in decision["tools"].items() if Path(path).name == name]
        require(expected_hashes == [hashlib.sha256(raw["capture/" + name + ".gz"]).hexdigest()],
                "preregistered script: " + name)

    expected = [(trial, name, param, arm)
                for trial in range(decision["trials"])
                for name, param in decision["scope"]
                for arm in (("baseline", "candidate") if trial % 2 == 0 else ("candidate", "baseline"))]
    rows = context["rows"]
    require([(r["trial"], r["name"], r["param"], r["arm"]) for r in rows] == expected,
            "complete trial-major schedule")
    hashes = {}
    samples = {}
    for row in rows:
        stem = f'{row["trial"]}-{row["name"]}-{row["param"]}-{row["arm"]}'
        require(row["stdout"] == stem + ".stdout" and row["stderr"] == stem + ".stderr",
                "distinct raw streams")
        observation = read("comparison/" + row["stdout"])
        binary = sources[row["arm"]]["binary"]
        require(row["command"] == [binary, "_child", "--bench", "Hex.OrderedFnBench." + row["name"],
                "--param", str(row["param"]), "--target-nanos", str(decision["target_inner_nanos"])],
                "recorded command")
        require(observation == row["observation"] and row["returncode"] == 0, "raw observation")
        require(observation["kind"] == "parametric" and observation["env"]["exe_name"] == Path(binary).name and
                observation["env"]["lean_version"] == decision["compiler_version"], "child executable/compiler")
        require(observation["status"] == "ok" and observation["error"] is None, "child failure")
        require(observation["function"] == "Hex.OrderedFnBench." + row["name"] and
                observation["param"] == row["param"], "workload identity")
        value = observation["per_call_nanos"]
        require(math.isfinite(value) and value > 0, "invalid timing")
        key = row["name"], row["param"]
        require(observation["result_hash"] is not None, "missing result hash")
        hashes.setdefault(key, set()).add(observation["result_hash"])
        samples.setdefault((*key, row["arm"]), []).append(value)
    require(all(len(values) == 1 for values in hashes.values()), "result hash disagreement")
    analysis = []
    for name, param in decision["scope"]:
        medians = {arm: statistics.median(samples[name, param, arm])
                   for arm in ("baseline", "candidate")}
        change = 100 * (medians["candidate"] / medians["baseline"] - 1)
        analysis.append(dict(name=name, param=param, medians=medians, pct_change=change))
    require(analysis == context["analysis"], "analysis replay")
    required = {tuple(case) for case in criterion["must_improve"]}
    changes = {(row["name"], row["param"]): row["pct_change"] for row in analysis}
    require(required <= set(changes), "missing required criterion case")
    passed = all(changes[case] < -criterion["minimum_improvement_percent"] for case in required) and all(
        change <= criterion["maximum_neighbor_regression_percent"]
        for case, change in changes.items() if case not in required)
    require(passed == context["expansion_criterion_passed"] and passed, "bounded criterion")
    print(f'PASS: {len(raw)} archive bindings; {len(rows)} raw observations; six median comparisons.')


if __name__ == "__main__":
    main()
