#!/usr/bin/env python3
"""Recompute the transparent-huge-page driver report from retained campaign records.

Each argument names a campaign directory (or an extracted archive of one):
`--ab` holds the adjacent main/candidate comparison, `--primary` and
`--heldout` the matched msolve sweeps. Every number in the report is derived
from the per-process samples; nothing is copied from a summary file.
"""
import argparse
import collections
import json
import math
import statistics
from pathlib import Path


def gm(values):
    values = list(values)
    return math.exp(sum(map(math.log, values)) / len(values))


def require(condition, message):
    if not condition:
        raise SystemExit("error: " + message)


def ab_section(directory):
    meta = json.loads((directory / "metadata.json").read_text())
    samples = meta["samples"]
    index = {(s["case"], s["block"], s["arm"]): s for s in samples}
    cases = [c["name"] for c in meta["cases"]]
    rows, failed = [], []
    for case in cases:
        for block in (0, 1):
            pair = [index.get((case, block, arm)) for arm in "AB"]
            if not all(pair) or not all(s["status"] == "ok" for s in pair):
                failed.append((case, block))
                continue
            a, b = pair
            require(a["complete_output_and_counters_equal"] and b["complete_output_and_counters_equal"],
                    f"outputs or counters differ for {case} block {block}")
            rows.append(dict(case=case, family=a["family"], p=a["p"],
                             process=b["wall_nanos"] / a["wall_nanos"],
                             candidate=b["candidate_nanos"] / a["candidate_nanos"],
                             rss=(a["peak_rss_kib"], b["peak_rss_kib"])))
    by_field = collections.defaultdict(list)
    for r in rows:
        by_field[r["p"]].append(r)
    lines = ["| Field | Pairs | Candidate B/A | Process B/A | Process pair range | Peak RSS A/B, KiB |",
             "|---|---:|---:|---:|---:|---:|"]
    for p in sorted(by_field):
        rs = by_field[p]
        lines.append(f"| {p} | {len(rs)} | {gm(r['candidate'] for r in rs):.4f} | "
                     f"{gm(r['process'] for r in rs):.4f} | {min(r['process'] for r in rs):.4f}–"
                     f"{max(r['process'] for r in rs):.4f} | {max(r['rss'][0] for r in rs)}/{max(r['rss'][1] for r in rs)} |")
    lines.append(f"| all | {len(rows)} | {gm(r['candidate'] for r in rows):.4f} | "
                 f"{gm(r['process'] for r in rows):.4f} | {min(r['process'] for r in rows):.4f}–"
                 f"{max(r['process'] for r in rows):.4f} | |")
    return meta, rows, failed, "\n".join(lines)


def msolve_section(directory):
    meta = json.loads((directory / "metadata.json").read_text())
    samples = meta["samples"]
    index = {(s["case"], s["block"], s["arm"]): s for s in samples}
    cases = list(dict.fromkeys(s["case"] for s in samples))
    families = collections.defaultdict(list)
    solved = collections.defaultdict(lambda: {"A": 0, "B": 0, "n": 0})
    losses, per_case = [], {}
    for case in cases:
        family = next(s["family"] for s in samples if s["case"] == case)
        for block in (0, 1):
            pair = [index.get((case, block, arm)) for arm in "AB"]
            if not all(pair):
                continue
            solved[family]["n"] += 1
            for s in pair:
                solved[family][s["arm"]] += s["status"] == "ok"
            if all(s["status"] == "ok" for s in pair):
                require(all(s.get("complete_basis_equal") for s in pair), f"bases differ for {case}")
                ratio = pair[0]["wall_nanos"] / pair[1]["wall_nanos"]
                families[family].append(ratio)
                per_case.setdefault(case, []).append(ratio)
            elif pair[1]["status"] == "ok" and pair[0]["status"] != "ok":
                losses.append((case, block, pair[0]["status"]))
    require(families, "no jointly solved pairs in " + str(directory))
    family_ratio = {f: gm(v) for f, v in families.items()}
    balanced = gm(family_ratio.values())
    lines = ["| Family | Jointly solved pairs | Hex solved | msolve solved | Hex/msolve process |",
             "|---|---:|---:|---:|---:|"]
    for f in sorted(solved):
        ratio = f"{family_ratio[f]:.4f}" if f in family_ratio else "none jointly solved"
        lines.append(f"| {f} | {len(families[f])} | {solved[f]['A']}/{solved[f]['n']} | "
                     f"{solved[f]['B']}/{solved[f]['n']} | {ratio} |")
    ratios = [r for v in families.values() for r in v]
    rss = (max((s["peak_rss_kib"] or 0) for s in samples if s["arm"] == "A"),
           max((s["peak_rss_kib"] or 0) for s in samples if s["arm"] == "B"))
    status = collections.Counter((s["arm"], s["status"]) for s in samples)
    summary = dict(balanced=balanced, comparator=meta["msolve_build"]["commit"],
                   scored=len(family_ratio), families=len(solved), pairs=len(ratios), median=statistics.median(ratios),
                   minimum=min(ratios), maximum=max(ratios), losses=losses, rss=rss, status=status,
                   processes=len(samples), per_case={c: gm(v) for c, v in per_case.items()})
    return meta, summary, "\n".join(lines)


def render(ab, primary, heldout):
    ab_meta, ab_rows, ab_failed, ab_table = ab
    lines = ["# Transparent huge pages in the F4 drivers", "",
             "The standalone F4 drivers call `prctl(PR_SET_THP_DISABLE)` from a constructor that runs "
             "before Lean module initialization. The Lean runtime's allocator otherwise reserves its arena "
             "with `MADV_HUGEPAGE`; under the host's `transparent_hugepage/defrag=madvise` policy a first "
             "touch may compact memory synchronously and zero a whole 2 MiB page. Comparators using glibc "
             "`malloc` never request huge pages under that policy. Outputs and logical counters are unchanged.", "",
             "A is the frozen main build and B the frozen candidate "
             f"`{ab_meta['manifest'].get('source_fingerprint', '?')}`; both arms run the identical CLI options on one leased CPU with adjacent AB/BA "
             "pairs. The selection is the first primary size of all ten families in all three fields plus "
             "Eco-14/Eco-15 over F₂, as in the preceding delayed-update campaigns.", "",
             ab_table, "",
             f"All {len(ab_rows)} completed pairs have identical complete outputs and logical counters"
             + (f"; {len(ab_failed)} pairs did not complete." if ab_failed else "."), ""]
    for label, (meta, s, table) in [("fixed primary corpus", primary), ("held-out corpus", heldout)]:
        if meta is None:
            continue
        complete = meta.get("campaign_status", "running")
        lines += [f"## msolve, {label}", "",
                  f"{s['processes']} retained processes ({complete}); {s['pairs']} jointly solved adjacent pairs, "
                  f"all with equal complete reduced bases. The equal-family Hex/msolve process ratio over "
                  f"{s['scored']} of {s['families']} families is **{s['balanced']:.4f}** (median pair {s['median']:.4f}, range {s['minimum']:.4f}–{s['maximum']:.4f}). "
                  f"Peak RSS Hex/msolve is {s['rss'][0]}/{s['rss'][1]} KiB.", "", table, ""]
        if s["losses"]:
            lines += ["Pairs solved by msolve but not Hex: " + ", ".join(f"{c} (block {b}, {st})" for c, b, st in s["losses"]) + ".", ""]
        else:
            lines += ["No input solved by msolve went unsolved by Hex within the same limits.", ""]
    comparators = {s["comparator"] for meta, s, _ in (primary, heldout) if meta is not None}
    require(len(comparators) <= 1, "campaigns used different msolve builds")
    comparator = comparators.pop() if comparators else "not measured"
    lines += [f"The comparator is msolve `{comparator}` (full reduced output, "
              "`-g 2 -t 1 -l 2`). Process time includes startup, parsing and complete output. Candidate "
              "production excludes certificate generation, independent certification and kernel checking. "
              "These are observations on the shared AMD EPYC 9455 host; all completed samples are retained "
              "and no control-adjusted improvement is claimed. The fastest-open-source milestone remains "
              "open under issue #10987.", ""]
    return "\n".join(lines)


def extract(index_path):
    """Join the recorded parts, check every digest and unpack to a private directory."""
    import hashlib
    import tarfile
    import tempfile
    index = json.loads(index_path.read_text())
    require(index.get("format") == 1, "unsupported parts index")
    target = Path(tempfile.mkdtemp(prefix="f4-thp-"))
    joined = target / "joined.tar.xz"
    total = hashlib.sha256()
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
    root = target / "thp"
    manifest = json.loads((root / "sha256.json").read_text())
    for relative, digest in manifest.items():
        require(hashlib.sha256((root / relative).read_bytes()).hexdigest() == digest,
                "payload digest differs: " + relative)
    return root


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path,
                        help="parts index of the retained capsule; replaces the directory arguments")
    parser.add_argument("--ab", type=Path)
    parser.add_argument("--primary", type=Path)
    parser.add_argument("--heldout", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.archive:
        root = extract(args.archive)
        args.ab, args.heldout = root / "thp-first32", root / "thp-heldout-msolve"
        if (root / "thp-full-primary-msolve").is_dir():
            args.primary = root / "thp-full-primary-msolve"
    require(args.ab is not None, "supply --archive or --ab")
    ab = ab_section(args.ab)
    primary = msolve_section(args.primary) if args.primary else (None, None, None)
    heldout = msolve_section(args.heldout) if args.heldout else (None, None, None)
    text = render(ab, primary, heldout)
    if args.check:
        require(args.report.read_text() == text, "report differs; regenerate it")
    else:
        args.report.write_text(text)
    print("Recomputed THP driver report from retained samples.")


if __name__ == "__main__":
    main()
