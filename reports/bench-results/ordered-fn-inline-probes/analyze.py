"""Recompute the completed attribution probes without collecting measurements."""
from pathlib import Path
import json
import math
import statistics

root = Path(__file__).parent
for variant in ("full-sign", "scan-only"):
    folder = root / variant
    rows = [json.loads(line) for line in
            (folder / "probe-observations.jsonl").read_text().splitlines()]
    stored = json.loads((folder / "probe-analysis.json").read_text())
    assert len(rows) == stored["completed_arms"] == 18
    assert stored["failed_arms"] == 0
    assert stored["all_pair_hashes_agree"] is True
    context = json.loads((folder / "probe-context.json").read_text())
    decision = json.loads((folder / "decision.json").read_text())
    assert context["binaries"]["inline"] == decision["native_binary_sha256"]
    assert all(row["returncode"] == 0 and
               row["observation"]["status"] == "ok" for row in rows)
    for row in rows:
        raw = folder / (f"probe-{row['trial']}-{row['name']}-"
                        f"{row['arm']}.stdout")
        assert json.loads(raw.read_text()) == row["observation"]
    for trial in range(3):
        for name in ("height", "third", "approximation"):
            pair = [row for row in rows
                    if row["trial"] == trial and row["name"] == name]
            assert len(pair) == 2
            assert {row["arm"] for row in pair} == {"baseline", "inline"}
            assert len({row["observation"]["result_hash"] for row in pair}) == 1
    changes = {}
    for point in stored["points"]:
        arms = {arm: [row["observation"]["per_call_nanos"] for row in rows
                      if row["name"] == point["name"] and row["arm"] == arm]
                for arm in ("baseline", "inline")}
        assert all(len(values) == 3 for values in arms.values())
        assert all(point[arm] == values for arm, values in arms.items())
        change = 100 * (statistics.median(arms["inline"]) /
                        statistics.median(arms["baseline"]) - 1)
        assert math.isclose(change, point["change_percent"], abs_tol=1e-10)
        changes[point["name"]] = change
    expand = all(changes[name] < -10 for name in ("height", "third"))
    assert stored["expand_full_comparison"] == expand
    print(json.dumps({"variant": variant, "change_percent": changes,
                      "expand_full_comparison": expand}))

failed_context = json.loads((root / "failed-capture/probe-context.json").read_text())
full_context = json.loads((root / "full-sign/probe-context.json").read_text())
assert failed_context["binaries"]["inline"] == full_context["binaries"]["inline"]
failed = [json.loads(line) for line in
          (root / "failed-capture/probe-observations.jsonl").read_text().splitlines()]
assert len(failed) == 18
assert sum("error" in row for row in failed) == 9
assert all(row["arm"] == "inline" and "Permission denied" in row["error"]
           for row in failed if "error" in row)
for row in failed:
    if row["arm"] == "baseline":
        assert row["returncode"] == 0 and row["observation"]["status"] == "ok"
        raw = root / "failed-capture" / (
            f"probe-{row['trial']}-{row['name']}-baseline.stdout")
        assert json.loads(raw.read_text()) == row["observation"]
for trial in range(3):
    for name in ("height", "third", "approximation"):
        pair = [row for row in failed
                if row["trial"] == trial and row["name"] == name]
        assert len(pair) == 2
        assert {row["arm"] for row in pair} == {"baseline", "inline"}
print("Nine failed candidate invocations remain excluded from timing observations.")
