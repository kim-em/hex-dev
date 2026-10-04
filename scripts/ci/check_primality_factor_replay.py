#!/usr/bin/env python3
"""Check retained certificate links and reproduce one native policy certificate."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REPORTS = ROOT / "reports/primality/factor-policy"


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def primecert_term(source):
    """Extract the generated bracketed term independently of the theorem name."""
    start = source.index("prime_cert%")
    opening = source.index("[", start)
    depth = 0
    for index in range(opening, len(source)):
        if source[index] == "[":
            depth += 1
        elif source[index] == "]":
            depth -= 1
            if depth == 0:
                return source[start:index + 1]
    raise ValueError("unterminated PrimeCert certificate")


def main():
    manifest = json.loads((REPORTS / "kernel-certificates.json").read_text())
    assert digest((ROOT / manifest["source"]).read_text()) == manifest["source_sha256"]
    certificates = {entry["certificate_sha256"]: entry for entry in manifest["certificates"]}
    for sha, entry in certificates.items():
        assert digest(entry["certificate"]) == sha
        assert entry["kernel_replayed"] is True
    primecert = json.loads((REPORTS / "primecert-kernel-replay.json").read_text())
    replays = {entry["id"]: entry for entry in primecert["replays"]}
    for entry in replays.values():
        assert digest(entry["source"]) == entry["source_sha256"]
        assert digest(primecert_term(entry["source"])) == entry["term_sha256"]
        assert entry["returncode"] == 0
    links = json.loads((REPORTS / "replay-links.json").read_text())
    linked = set()
    for link in links:
        key = (link["report"], link["sample"])
        assert key not in linked
        linked.add(key)
        row = json.loads((REPORTS / link["report"]).read_text())["samples"][link["sample"]]
        if "certificate_sha256" in link:
            sha = digest(row["result"]["certificate"])
            assert sha == link["certificate_sha256"]
            assert certificates[sha]["theorem"] == link["theorem"]
            assert row["subject"] == certificates[sha]["subject"]
        else:
            replay = replays[link["case"]]
            assert digest(row["stdout"]) == link["output_sha256"]
            assert digest(primecert_term(row["stdout"])) == replay["term_sha256"]
    for path in REPORTS.glob("*.json"):
        data = json.loads(path.read_text())
        if not isinstance(data, dict):
            continue
        for index, row in enumerate(data.get("samples", [])):
            if row.get("result", {}).get("status") in ["success", "generated"]:
                assert (path.name, index) in linked
    case = next(entry for entry in certificates.values()
                if entry["case"] == "Curve448" and entry["profile"] == "balanced")
    output = subprocess.check_output(
        [str(ROOT / ".lake/build/bin/hexprimality_factor_experiment"),
         "construct", "balanced", str(case["subject"])], text=True, timeout=120)
    result = json.loads(output)
    assert result["status"] == "success" and result["subject"] == case["subject"]
    assert digest(result["certificate"]) == case["certificate_sha256"]
    print(f"Checked {len(links)} replay links and exact native Curve448 certificate")


if __name__ == "__main__":
    main()
