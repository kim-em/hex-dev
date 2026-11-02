#!/usr/bin/env python3
"""Check that the report-specific F4 audit rejects altered retained evidence."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_performance_audit import campaign


def write(path, value):
    path.unlink()
    path.write_text(json.dumps(value))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["combined", "scan-cache", "driver-output", "report", "output"]:
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    source = args.combined / "before-after-selected"
    results = []
    mutations = {
        "metadata-counter": "counters differ from metadata",
        "metadata-scheduling": "scheduling differs from metadata",
        "duplicate-arm": "duplicate arm",
        "basis-coefficient": "complete JSON mismatch",
        "coherent-counter": "complete JSON mismatch",
        "candidate-time": "candidate time differs from metadata",
        "recorded-mean": "recorded median mismatch",
        "missing-key": "scheduling",
        "duplicate-key": "duplicate JSON object key"}
    for kind, expected in mutations.items():
        with tempfile.TemporaryDirectory(prefix="groebner-audit-negative-") as directory:
            target = Path(directory)
            for path in source.iterdir():
                if path.is_file():
                    (target / path.name).symlink_to(path.resolve())
            metadata = json.loads((source / "metadata.json").read_text())
            sample = metadata["samples"][1]
            raw_path = target / f"{sample['case']}-b{sample['block']}-{sample['arm']}.stdout"
            raw = json.loads(raw_path.read_text())
            if kind == "metadata-counter":
                sample["statistics"]["rounds"] += 1
            elif kind == "metadata-scheduling":
                sample["scheduling"] = "sugar"
            elif kind == "duplicate-arm":
                sample["arm"] = "A"
            elif kind == "basis-coefficient":
                raw["basis"][0][0][1] += 1
            elif kind == "coherent-counter":
                sample["statistics"]["rounds"] += 1
                raw["statistics"]["rounds"] += 1
            elif kind == "candidate-time":
                raw["candidateNanos"] += 1
            elif kind == "recorded-mean":
                analysis = json.loads((source / "analysis.json").read_text())
                analysis["median"] += 1
                write(target / "analysis.json", analysis)
            elif kind == "missing-key":
                del raw["scheduling"]
            write(target / "metadata.json", metadata)
            write(raw_path, raw)
            if kind == "duplicate-key":
                text = raw_path.read_text()
                raw_path.write_text(text[:-1] + ',"basis":[]}')
            try:
                campaign(target)
            except (ValueError, KeyError) as error:
                if expected not in str(error):
                    raise RuntimeError(f"wrong rejection for {kind}: {error}") from error
                results.append(dict(mutation=kind, rejected=True, message=str(error)))
            else:
                raise RuntimeError("missed mutation: " + kind)
    replacements = {
        "summary-cell": ("| New/selected baseline | 0.9263 |", "| New/selected baseline | 0.8263 |", "report table mismatch"),
        "driver-phrase": ("has process mean 0.9191", "has process mean 0.8191", "driver ratio phrase mismatch"),
        "candidate-phrase": ("candidate-time mean is 0.9773", "candidate-time mean is 0.8773", "combined candidate phrase mismatch")}
    for kind, (before, after, expected) in replacements.items():
        text = args.report.read_text()
        if text.count(before) != 1:
            raise RuntimeError("ambiguous report mutation: " + kind)
        with tempfile.TemporaryDirectory(prefix="groebner-report-negative-") as directory:
            report = Path(directory) / "report.md"
            report.write_text(text.replace(before, after))
            command = [sys.executable, str(ROOT / "scripts/bench/groebner_performance_audit.py"),
                       "--combined", str(args.combined), "--scan-cache", str(args.scan_cache),
                       "--driver-output", str(args.driver_output), "--report", str(report)]
            result = subprocess.run(command, capture_output=True, text=True)
            if result.returncode == 0 or expected not in result.stderr:
                raise RuntimeError(f"missed/wrong report rejection for {kind}: {result.stderr}")
            results.append(dict(mutation=kind, rejected=True, message=expected))
    args.output.write_text(json.dumps(results, indent=2) + "\n")
    print(f"report audit: {len(results)} altered-evidence cases rejected")


if __name__ == "__main__":
    main()
