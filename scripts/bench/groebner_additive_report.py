#!/usr/bin/env python3
"""Recompute the additive monomial hash report from its retained capsule.

The capsule holds the first adjacent AB campaign and its one permitted
unchanged repeat. The hash changes collision-chain visits, so the charged
`work` counter legitimately differs; every pair must still have identical
complete reduced bases and every other logical counter. Each number in the
report is derived from the per-process samples and outputs.
"""
import argparse
import hashlib
import json
import math
import tarfile
import tempfile
from pathlib import Path

CAMPAIGNS = [("first", "additive-main-first32"), ("repeat", "additive-main-first32-repeat")]
FIELDS = (2, 32003, 2147483647)


def gm(values):
    values = list(values)
    return math.exp(sum(map(math.log, values)) / len(values))


def require(condition, message):
    if not condition:
        raise SystemExit("error: " + message)


def extract(index_path):
    index = json.loads(index_path.read_text())
    require(index.get("format") == 1, "unsupported parts index")
    target = Path(tempfile.mkdtemp(prefix="f4-additive-"))
    joined, total = target / "joined.tar.xz", hashlib.sha256()
    with joined.open("wb") as out:
        for part in index["parts"]:
            data = (index_path.parent / part["file"]).read_bytes()
            require(len(data) == part["bytes"] and hashlib.sha256(data).hexdigest() == part["sha256"],
                    "part digest differs: " + part["file"])
            total.update(data)
            out.write(data)
    require(total.hexdigest() == index["sha256"], "archive stream digest differs")
    with tarfile.open(joined) as archive:
        archive.extractall(target, filter="data")
    root = target / "additive"
    for relative, digest in json.loads((root / "sha256.json").read_text()).items():
        require(hashlib.sha256((root / relative).read_bytes()).hexdigest() == digest,
                "payload digest differs: " + relative)
    return root


def campaign(directory):
    meta = json.loads((directory / "metadata.json").read_text())
    index = {(s["case"], s["block"], s["arm"]): s for s in meta["samples"]}
    rows = []
    for case in meta["cases"]:
        name = case["name"]
        for block in (0, 1):
            a, b = index[(name, block, "A")], index[(name, block, "B")]
            require(a["status"] == b["status"] == "ok", f"{name} block {block} failed")
            out = [json.loads((directory / f"{name}-b{block}-{arm}.stdout").read_text()) for arm in "AB"]
            require(out[0]["basis"] == out[1]["basis"], f"bases differ for {name}")
            for key in out[0]["statistics"]:
                if key != "work":
                    require(out[0]["statistics"][key] == out[1]["statistics"][key], f"{key} differs for {name}")
            rows.append(dict(p=case["p"], family=case["family"],
                             candidate=b["candidate_nanos"] / a["candidate_nanos"],
                             process=b["wall_nanos"] / a["wall_nanos"]))
    return meta, rows


def render(results):
    lines = ["# Additive monomial hashes", "",
             "Each coordinate has a fixed 64-bit weight; a monomial's hash is the weighted sum of its "
             "exponents. Product degrees, support masks and full-width hashes combine from the factors' "
             "cached metadata. Every lookup still compares all exponents, so bases are unchanged; only "
             "the charged `work` counter differs, because collision-chain visits change.", "",
             "A is the frozen main build and B the frozen additive-hash build. Both arms run identical CLI "
             "options with `MIMALLOC_ALLOW_THP=0` on one leased CPU, in adjacent AB/BA pairs, on the "
             "first primary size of all ten families in all three fields plus Eco-14/Eco-15 over F₂. The "
             "first campaign was inconclusive, so the protocol's one unchanged repeat follows it.", "",
             "| Campaign | Pairs | Candidate B/A | Process B/A | Candidate B/A by field (2 / 32003 / 2³¹−1) |",
             "|---|---:|---:|---:|---|"]
    for label, rows in results:
        fields = " / ".join(f"{gm(r['candidate'] for r in rows if r['p'] == p):.4f}" for p in FIELDS)
        lines.append(f"| {label} | {len(rows)} | {gm(r['candidate'] for r in rows):.4f} | "
                     f"{gm(r['process'] for r in rows):.4f} | {fields} |")
    pooled = [r for _, rows in results for r in rows]
    lines += ["", f"Pooled over both campaigns, the candidate ratio is {gm(r['candidate'] for r in pooled):.4f} "
              f"and the process ratio {gm(r['process'] for r in pooled):.4f}. Every pair has identical complete "
              "reduced bases and identical logical counters other than `work`. These are descriptive "
              "observations on the shared AMD EPYC 9455 host with every completed sample retained; the two "
              "campaigns differ materially, so only a modest improvement is supported. Certificate generation, "
              "independent certification and kernel checking are excluded. The fastest-open-source milestone "
              "remains open under issue #10987.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = extract(args.archive)
    text = render([(label, campaign(root / name)[1]) for label, name in CAMPAIGNS])
    if args.check:
        require(args.report.read_text() == text, "report differs; regenerate it")
    else:
        args.report.write_text(text)
    print("Recomputed additive-hash report from retained samples.")


if __name__ == "__main__":
    main()
