"""Verify the retained bounded comparison without running measurements."""

import gzip
import hashlib
import json
import math
from pathlib import Path
import statistics


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
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
    require(sources["candidate"]["head"] == manifest["source_commit"], "candidate commit")
    require(sources["baseline"]["packages"] == sources["candidate"]["packages"], "dependency pins")

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
        require(observation == row["observation"] and row["returncode"] == 0, "raw observation")
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
    passed = next(row for row in analysis if row["param"] == 12288)["pct_change"] < -10 and all(
        row["pct_change"] <= 10 for row in analysis if row["param"] != 12288)
    require(passed == context["expansion_criterion_passed"] and passed, "bounded criterion")
    print(f'PASS: {len(raw)} archive bindings; {len(rows)} raw observations; three median comparisons.')


if __name__ == "__main__":
    main()
