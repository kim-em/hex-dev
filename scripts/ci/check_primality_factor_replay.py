#!/usr/bin/env python3
"""Check retained certificate links and reproduce exact native policy certificates."""
from __future__ import annotations

import hashlib
from functools import cache
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
REPORTS = ROOT / "reports/primality/factor-policy"
sys.path.insert(0, str(ROOT / "scripts/bench"))
from primality_factor_corpus import validate


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


@cache
def load_report(name):
    """Read immutable retained reports once when checking many sample links."""
    return json.loads((REPORTS / name).read_text())


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
    corpus = json.loads((REPORTS / "corpus-v3.json").read_text())
    validate(corpus)
    corrected = json.loads((REPORTS / "corpus-v4.json").read_text())
    validate(corrected)
    corpora = {"v3": corpus, "v4": corrected}
    assert {c["subject"] for c in corpus["cases"]}.isdisjoint(
        c["subject"] for c in corrected["cases"])
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
        row = load_report(link["report"])["samples"][link["sample"]]
        if "certificate_sha256" in link:
            sha = digest(row["result"]["certificate"])
            assert sha == link["certificate_sha256"]
            assert certificates[sha]["theorem"] == link["theorem"]
            assert row["subject"] == certificates[sha]["subject"]
        else:
            replay = replays[link["case"]]
            assert digest(row["stdout"]) == link["output_sha256"]
            assert digest(primecert_term(row["stdout"])) == replay["term_sha256"]
    fresh = REPORTS / "corpus-replay-v3.json"
    assert fresh.exists(), "the independent corpus requires a complete replay manifest"
    if fresh.exists():
        data = json.loads(fresh.read_text())
        assert not data["partial"]
        for source, sha in data["hex_sources"].items():
            assert digest((ROOT / source).read_text()) == sha
        directory = ROOT / "bench/HexPrimalityTheory/ProofProbe/FactorCorpus"
        assert set(data["hex_sources"]) == {str(p.relative_to(ROOT)) for p in directory.glob("*.lean")}
        for system, suffix in [("native", ".hex.log"), ("primecert", ".primecert.log")]:
            result = data[f"{system}_build"]
            if data[system]:
                assert result is not None and result["returncode"] == 0
                assert digest(fresh.with_suffix(suffix).read_text()) == result["log_sha256"]
        for name, sha in data["reports"].items():
            report = load_report(name)
            assert digest((REPORTS / name).read_text()) == sha and report["complete"]
            if name in ["tuning-v3.json", "validation-v3.json", "validation-v4.json"]:
                version = name.removesuffix(".json").split("-")[-1]
                selected = corpora[version]
                split = name.split("-")[0]
                cases = [c for c in selected["cases"] if c["split"] == split]
                assert report["cases"] == cases
                assert report["corpus_sha256"] == digest((REPORTS / f"corpus-{version}.json").read_text())
                expected = {(c["id"], 0, p) for c in cases
                            for p in ["baseline", "interleaved", "primecert"]}
                actual = {(r["case"], r["trial"], r["profile"]) for r in report["samples"]}
                assert expected == actual and len(actual) == len(report["samples"])
                subjects = {c["id"]: c["subject"] for c in cases}
                for row in report["samples"]:
                    assert row["subject"] == subjects[row["case"]] and row["state"] != "running"
                    if row["profile"] != "primecert":
                        assert row["executable_sha256"] == report["executable_sha256"]
                        if "result" in row:
                            assert row["result"]["attempts"] <= 1024
        for system in ["native", "primecert"]:
            for sha, entry in data[system].items():
                literal = entry["certificate"] if system == "native" else entry["term"]
                assert digest(literal) == sha
                if system == "native":
                    source = "bench/" + entry["module"].replace(".", "/") + ".lean"
                    assert source in data["hex_sources"]
                    source = (ROOT / source).read_text()
                    assert f'theorem {entry["theorem"]} : _root_.Nat.Prime {entry["subject"]}' in source
                    assert f"(c := {literal}) (by decide +kernel)" in source
                else:
                    assert digest(entry["source"]) == entry["source_sha256"]
                    assert primecert_term(entry["source"]) == literal
        for link in data["links"]:
            key = (link["report"], link["sample"])
            assert key not in linked
            linked.add(key)
            row = load_report(link["report"])["samples"][link["sample"]]
            table = data["native" if link["system"] == "hex" else "primecert"]
            entry = table[link["term_sha256"]]
            literal = row["result"]["certificate"] if link["system"] == "hex" else primecert_term(row["stdout"])
            assert digest(literal) == link["term_sha256"]
            assert row["subject"] == link["subject"] == entry["subject"]
    for path in REPORTS.glob("*.json"):
        data = load_report(path.name)
        if not isinstance(data, dict):
            continue
        for index, row in enumerate(data.get("samples", [])):
            if row.get("result", {}).get("status") in ["success", "generated"]:
                assert (path.name, index) in linked
    adoption = ROOT / "reports/primality/adoption"
    measurements = json.loads((adoption / "measurements.json").read_text())
    assert measurements["complete"]
    provenance = json.loads((adoption / "provenance.json").read_text())
    assert provenance["source_commit"] == measurements["source_commit"]
    assert provenance["executable_sha256"] == measurements["executable_sha256"]
    assert provenance["sources"] == measurements["sources"]
    assert digest((adoption / provenance["source_patch"]).read_text()) == provenance["patch_sha256"]
    replay = json.loads((adoption / "kernel-replay.json").read_text())
    assert digest((adoption / "measurements.json").read_text()) == replay["measurements_sha256"]
    assert replay["build_returncode"] == 0
    source = (ROOT / replay["source"]).read_text()
    assert digest(source) == replay["source_sha256"]
    assert digest((adoption / "kernel-replay.log").read_text()) == replay["log_sha256"]
    dispatch = json.loads((adoption / "dispatch.json").read_text())
    assert dispatch["policy"] == "interleaved" and dispatch["returncode"] == 0
    assert len(dispatch["cases"]) == len(dispatch["confirmations"]) == 3
    assert digest((adoption / "dispatch.log").read_text()) == dispatch["log_sha256"]
    successes = {i for i, row in enumerate(measurements["samples"])
                 if row.get("result", {}).get("status") == "success"}
    assert successes == {link["sample"] for link in replay["links"]}
    for link in replay["links"]:
        row = measurements["samples"][link["sample"]]
        sha = digest(row["result"]["certificate"])
        assert sha == link["certificate_sha256"]
        entry = replay["certificates"][sha]
        assert digest(entry["certificate"]) == sha and entry["subject"] == row["subject"]
        assert f'theorem {entry["theorem"]} : _root_.Nat.Prime {entry["subject"]}' in source
        assert f'(c := {entry["certificate"]}) (by decide +kernel)' in source
    case = next(entry for entry in certificates.values()
                if entry["case"] == "Curve448" and entry["profile"] == "balanced")
    output = subprocess.check_output(
        [str(ROOT / ".lake/build/bin/hexprimality_factor_experiment"),
         "construct", "balanced", str(case["subject"])], text=True, timeout=120)
    result = json.loads(output)
    assert result["status"] == "success" and result["subject"] == case["subject"]
    assert digest(result["certificate"]) == case["certificate_sha256"]
    case = next(entry for entry in certificates.values()
                if entry["case"] == "Curve25519" and entry["profile"] == "efficient")
    output = subprocess.check_output(
        [str(ROOT / ".lake/build/bin/hexprimality_factor_experiment"),
         "construct", "interleaved", str(case["subject"])], text=True, timeout=120)
    result = json.loads(output)
    assert result["status"] == "success" and result["attempts"] == 31
    assert digest(result["certificate"]) == case["certificate_sha256"]
    # Pin the adopted provider on actual ECM paths as well as the p-1 fixture.
    fields = load_report("fields-v4.json")
    for name in ["P-521", "P-384", "Curve448"]:
        sample = next(row for row in fields["samples"]
                      if row["case"] == name and row["profile"] == "interleaved")
        output = subprocess.check_output(
            [str(ROOT / ".lake/build/bin/hexprimality_factor_experiment"),
             "construct", "interleaved", str(sample["subject"])],
            text=True, timeout=120)
        result = json.loads(output)
        assert result["status"] == "success"
        assert result["attempts"] == sample["result"]["attempts"]
        assert digest(result["certificate"]) == digest(sample["result"]["certificate"])
    subprocess.run([str(ROOT / ".lake/build/bin/hexprimality_factor_experiment"), "selftest"], check=True)
    print(f"Checked {len(linked)} replay links and exact native field-prime certificates")


if __name__ == "__main__":
    main()
