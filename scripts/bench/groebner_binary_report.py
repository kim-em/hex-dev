#!/usr/bin/env python3
"""Check retained packed-F2 experiments and reproduce their benchmark report."""
import argparse
import hashlib
import math
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_binary_guards import blobs, combined, admission, refusals
from scripts.bench.groebner_comparator_report import msolve
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_trie_report import source, require, mean


def close(a, b, message):
    require(math.isclose(a, b, rel_tol=1e-12), message)



def check_guards(cap, manifest):
    current, native = cap.json("identity.json"), cap.json("native-identity.json")
    checks = cap.text("checks.manifest")
    require(native["source_fingerprint"] == manifest["source_fingerprint"] and
            native["source_manifest_sha256"] == hashlib.sha256(manifest["source_manifest"].encode()).hexdigest(),
            "native runtime differs")
    require(current["checks_fingerprint"] == native["checks_fingerprint"] and
            current["checks_manifest_sha256"] == native["checks_manifest_sha256"] ==
            hashlib.sha256(checks.encode()).hexdigest(), "check snapshots differ")
    blobs(cap, checks, "checks-sources/")
    text = cap.text("current.source.manifest")
    require(hashlib.sha256(text.encode()).hexdigest() == current["source_manifest_sha256"],
            "documented source manifest differs")
    blobs(cap, text, "current-sources/")
    before, after = listing(manifest["source_manifest"]), listing(text)
    path = "bench/HexGroebner/Bench/Primitives.lean"
    require(set(before) == set(after) and {p for p in before if before[p] != after[p]} == {path},
            "more than the cost comment changed")
    old = cap.text("pivots/root-sources/" + path)
    require(cap.text("current-sources/" + path) == old.replace(
        "-- The sparse provider uses the same canonical rows and complete result digest.",
        "-- O(n³) sparse elimination, with O(n²) preparation and complete output hashing.", 1),
        "cost comment differs")
    native_rows, full_rows = cap.json("native-status.json"), cap.json("full-status.json")
    require([r["name"] for r in native_rows] == ["clang", "gcc"] and all(
        r["variants"] == ["Native", "AVX2", "AVX2Remainder", "Scalar", "Remainder", "ScalarRemainder"] and
        r["sanitize"] == ["address", "undefined"] for r in native_rows), "native coverage differs")
    require([r["name"] for r in full_rows] ==
            ["build", "oracles", "driver", "bench", "dag", "phase4", "manifest", "headers", "lines"],
            "project coverage differs")
    for rows, identity in [(native_rows, native), (full_rows, current)]:
        require(all(r["exit_code"] == 0 and all(r[k] == v for k, v in identity.items()) for r in rows),
                "failed or stale checks")
    require("clang version 23.1.3" in cap.text("native-clang.log") and
            "16.2.0" in cap.text("native-gcc.log"), "sanitizer compilers differ")
    require("567 unique reduced bases match SymPy" in cap.text("full/oracles.log") and
            "567 reduced bases match Singular" in cap.text("full/oracles.log"), "oracle coverage differs")
    failure = cap.json("failed-before-cost-comment-status.json")
    require(failure[-1]["name"] == "phase4" and failure[-1]["exit_code"] == 1 and
            "cost-model derivation" in cap.text("failed-before-cost-comment.log"),
            "initial phase-check failure was not retained")
    return current, native


def sweep(cap, label, before, after, count=10, expected_binary=None):
    meta, recorded = cap.json(label + "/metadata.json"), cap.json(label + "/analysis.json")
    require(meta["source_unchanged"] and meta["threads"] == 1 and
            meta["source_manifest"] == after["source_manifest"] and meta["baseline_manifest"] == before and
            meta["binary_sha256"] == meta["binary_sha256_after"] ==
            {"A": before["binary_sha256"]["compute"], "B": after["binary_sha256"]["compute"]},
            "sweep source/executable binding differs")
    require(meta["requested_scheduling"] == {"A": "degree", "B": "degree"}, "scheduling differs")
    for name, digest in meta["input_sha256"].items():
        require(hashlib.sha256(cap.read(label + "/inputs/" + name)).hexdigest() == digest, "input differs")
    require(meta["requested_binary_pivots"] == expected_binary, "binary policy controls differ")
    samples = meta["samples"]
    order = [r["case"] for r in samples if r["block"] == 0 and r["arm"] == "A"]
    require(len(order) == len(set(order)) == count and len(samples) == count * 4 and
            [(r["case"], r["block"], r["arm"]) for r in samples] ==
            [(case, block, arm) for block in [0, 1] for case in order
             for arm in (["A", "B"] if block == 0 else ["B", "A"])], "AB/BA schedule differs")
    index = {(r["case"], r["block"], r["arm"]): r for r in samples}
    ratios, candidates, families = [], [], {}
    for case in order:
        inp = cap.json(label + "/inputs/" + case + ".json")
        for block in [0, 1]:
            outputs, pair = [], [index[case, block, a] for a in ["A", "B"]]
            for row in pair:
                arm = row["arm"]
                value = cap.json(f"{label}/{case}-b{block}-{arm}.stdout")
                require(row["status"] == "ok" and row["returncode"] == 0 and row["complete_basis_equal"],
                        "failed sample")
                require(value["kind"] == "unchecked_candidate" and value["p"] == inp["p"] and
                        value["variables"] == inp["variables"] and value["order"] == inp["order"] == "grevlex" and
                        value["scheduling"] == "degree", "candidate contract differs")
                flag = meta["requested_binary_pivots"][arm]
                require(value.get("binaryPivots", False) == (flag == "true"), "binary policy differs")
                if flag is not None:
                    require(row["command"][row["command"].index("--binary-pivots") + 1] == flag,
                            "binary command differs")
                counters = dict(row["statistics"])
                require(counters.pop("candidate_nanos") == value["candidateNanos"] and
                        counters == value["statistics"] and
                        int(cap.text(f"{label}/{case}-b{block}-{arm}.rss")) == row["peak_rss_kib"],
                        "counters/RSS differ")
                outputs.append(value)
            require(outputs[0]["basis"] == outputs[1]["basis"] and
                    outputs[0]["statistics"] == outputs[1]["statistics"] and
                    outputs[0]["batchSize"] == outputs[1]["batchSize"] and
                    outputs[0]["randomState"] == outputs[1]["randomState"] == 0,
                    "complete bases or logical statistics differ")
            ratios.append(pair[1]["wall_nanos"] / pair[0]["wall_nanos"])
            candidates.append(outputs[1]["candidateNanos"] / outputs[0]["candidateNanos"])
            families.setdefault(pair[0]["family"], []).append(ratios[-1])
    values = dict(geomean=mean(ratios), family_balanced_geomean=mean([mean(v) for v in families.values()]),
                  minimum=min(ratios), maximum=max(ratios), median=statistics.median(ratios))
    for key, value in values.items():
        close(recorded[key], value, "recorded " + key + " differs")
    require(recorded["samples"] == count * 4 and recorded["complete_bases_equal"] == count * 2 and
            recorded["failed_processes"] == recorded["timeouts"] == 0, "sweep coverage differs")
    for family, values in families.items():
        close(recorded["per_family"][family], mean(values), "family ratio differs")
    return dict(recorded=recorded, meta=meta, candidate=mean(candidates))


def kernels(cap, manifest, suffix, identity):
    prefix = "pivots/kernels" + suffix
    status = cap.json("pivots/kernel" + ("-long" if suffix else "") + "-status.json")
    require(status["identity"] == identity and status["threads"] == 1 and
            status["manifest"] == {"A": manifest, "B": manifest} and
            status["binary_sha256"] == status["binary_sha256_after"] ==
            {a: manifest["binary_sha256"]["bench"] for a in ["A", "B"]}, "kernel executable differs")
    rows = status["samples"]
    require(len({r["cpu"] for r in rows}) == 1, "kernel CPU lease differs")
    matched = [r for r in rows if r["label"].startswith("matched/")]
    require(len(matched) == 20 and [r["label"] for r in matched] ==
            [f"matched/binaryElimination/b{b}-{n}-{a}" for b in [0, 1] for n in [32, 64, 128, 256, 512]
             for a in (["A", "B"] if b == 0 else ["B", "A"])], "kernel AB/BA schedule differs")
    out = []
    for n in [32, 64, 128, 256, 512]:
        points, flags = {}, 0
        for b in [0, 1]:
            for a in ["A", "B"]:
                label = f"matched/binaryElimination/b{b}-{n}-{a}"
                row = next(r for r in matched if r["label"] == label)
                require(row["exit_code"] in [0, 2], "kernel command failed")
                function = "binaryEliminateSparse" if a == "A" else "binaryEliminate"
                command = row["command"]
                require("Hex.Groebner.Bench." + function in command and
                        command[command.index("--target-inner-nanos") + 1] ==
                        ("16000000000" if suffix else "500000000") and
                        command[command.index("--outer-trials") + 1] == "1", "kernel controls differ")
                result = cap.json(prefix + "/" + label + "/result.json")["results"][0]
                require(len(result["points"]) == 1, "kernel point count differs")
                p = result["points"][0]
                require(p["status"] == "ok" and p["param"] == n and p["result_hash"] is not None,
                        "kernel point failed")
                points[b, a] = p
                flags += p["below_signal_floor"]
        require(len({p["result_hash"] for p in points.values()}) == 1, "complete kernel hashes differ")
        out.append((n, mean([points[b, "B"]["per_call_nanos"] / points[b, "A"]["per_call_nanos"]
                            for b in [0, 1]]), flags))
    if not suffix:
        complexity = [r for r in rows if r["label"].startswith("complexity/")]
        require(len(rows) == 22 and len(complexity) == 2, "complexity coverage differs")
        for row in complexity:
            result = cap.json(prefix + "/" + row["label"] + "/result.json")["results"][0]
            require(row["exit_code"] in [0, 2] and len(result["points"]) == 15 and
                    all(p["status"] == "ok" for p in result["points"]), "complexity samples failed")
            require([(p["trial_index"], p["param"]) for p in result["points"]] ==
                    [(t, n) for t in range(3) for n in [32, 64, 128, 256, 512]],
                    "fixed trial-major complexity schedule differs")
    else:
        require(len(rows) == 20, "longer pass coverage differs")
    return out


class Comparator:
    def __init__(self, cap, suffix):
        self.cap, self.suffix = cap, suffix

    def path(self, path):
        return path.replace("pivots/msolve/", "pivots/msolve-f2" + self.suffix + "/")

    def json(self, path):
        return self.cap.json(self.path(path))

    def read(self, path):
        return self.cap.read(self.path(path))

    def text(self, path):
        return self.cap.text(self.path(path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["initial", "word", "blocked", "selected", "report"]:
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--rebased", type=Path, help="additional combined-tree source and verification snapshot")
    parser.add_argument("--refusals", type=Path, help="forced diagnostic refusal coverage")
    parser.add_argument("--admission", type=Path, help="non-timed native frame admission audit")
    parser.add_argument("--guards", type=Path, help="additional final verification snapshot")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--current", action="store_true")
    args = parser.parse_args()
    initial, word, blocked, selected = [Capsule(getattr(args, k)) for k in
                                        ["initial", "word", "blocked", "selected"]]
    original, prototype = source(initial, "baseline"), source(initial, "pivots")
    word_base, word_manifest = source(word, "baseline"), source(word, "pivots")
    blocked_base, blocked_manifest = source(blocked, "baseline"), source(blocked, "pivots")
    selected_manifest = source(selected, "pivots")
    require(word_base == blocked_base == prototype, "experiment baselines differ")
    require(all(selected_manifest["binary_sha256"][key] == blocked_manifest["binary_sha256"][key]
                for key in ["compute", "compute-reference"]), "selected computation executables changed")
    require(all(m["compilers"] == prototype["compilers"] and m["native_options"] == prototype["native_options"]
                for m in [original, word_manifest, blocked_manifest, selected_manifest]),
            "production compiler/options differ")
    identity, native = check_guards(selected, selected_manifest)
    historical = identity
    combined_identity = None
    rebased = None
    if args.rebased:
        rebased = Capsule(args.rebased)
        combined_identity = combined(rebased, selected, selected_manifest)
        identity = combined_identity
    guards = Capsule(args.guards) if args.guards else None
    if guards:
        identity = combined(guards, selected, selected_manifest, final=True)
    audit = Capsule(args.admission) if args.admission else None
    coverage = admission(audit, guards, blocked) if audit and guards else None
    require(not audit or coverage, "admission audit requires final guards")
    refusal_cap = Capsule(args.refusals) if args.refusals else None
    refusal_counts = refusals(refusal_cap, guards) if refusal_cap and guards else None
    require(not refusal_cap or refusal_counts, "forced refusals require final guards")
    if args.current:
        current = source_identity()
        require(all(current[k] == v for k, v in identity.items() if k != "source_commit"),
                "checkout differs from documented snapshot")
    observations = []
    for title, cap, before, after in [
        ("packed / prior", initial, original, prototype),
        ("word cursor / packed", word, prototype, word_manifest),
        ("zero blocks / packed", blocked, prototype, blocked_manifest),
    ]:
        flags = {"A": None if cap is initial else "true", "B": "true"}
        first = sweep(cap, "pivots/f2-false", before, after, expected_binary=flags)
        repeat = sweep(cap, "pivots/f2-false-repeat", before, after, expected_binary=flags)
        require(first["meta"]["input_sha256"] == repeat["meta"]["input_sha256"], "repeat inputs differ")
        observations.extend([(title, first), (title + " repeat", repeat)])
    control = sweep(initial, "pivots/prime-control", original, prototype, count=14, expected_binary={"A": None, "B": None})
    short = kernels(selected, selected_manifest, "", native)
    longer = kernels(selected, selected_manifest, "-long", historical)
    counts = {k: 2 for k in ["cyclic", "kat", "eco", "noon", "reimer", "minrank", "dense-quadratic"]}
    counts["mq"] = 6
    comparisons = []
    for title, cap, suffix in [("initial packed", initial, ""), ("selected", selected, ""),
                               ("selected repeat", selected, "-repeat")]:
        view = Comparator(cap, suffix)
        result, meta = msolve(view, "pivots", expected_families=counts, moduli={2})
        require(meta["requested_binary_pivots"] == {"A": "true", "B": None}, "comparator policy differs")
        comparisons.append((title, result, meta, view))
    require(all(row[2]["input_sha256"] == comparisons[0][2]["input_sha256"] for row in comparisons),
            "comparator input snapshots differ")
    for _, _, meta, view in comparisons[1:]:
        for row in meta["samples"]:
            if row["arm"] != "A":
                continue
            path = f"pivots/msolve/{row['case']}-b{row['block']}-A.stdout"
            before, after = comparisons[0][3].json(path), view.json(path)
            require(before["basis"] == after["basis"] and before["statistics"] == after["statistics"],
                    "comparator Hex bases/statistics differ between variants")
    lines = ["# Private packed pivots over ordinary F2", "",
        "An explicit `binaryPivots` option uses private packed pivots and an accumulator in bounded untraced matrix frames. It defaults to false. The deterministic driver accepts `--binary-pivots true|false` and reports the requested policy. Ordinary polynomial exponents retain their usual meaning; no Boolean-quotient relation is introduced.", "",
        "The selected implementation uses sparse toggles or word XOR according to row density, skips zero prepaid scan blocks, and gathers output with word masks and set-bit iteration. The transparent provider retains the sparse reference result, including every logical counter. Private payload must fit alongside the complete reference payload in the packed-byte allowance. A payload decline may repeat work in the reference continuation; the speculation bound is per frame.", "",
        "Manual shared-host comparisons use one algorithm thread, one automatically leased CPU, and adjacent AB then BA. All completed samples, failures, warnings, variability and RSS remain retained. Every full F4 comparison below checks complete bases and all logical statistics. These development suites are not held-out acceptance inputs.", "",
        "| Comparison | Process B/A | Candidate B/A | Equal-family B/A | Pair range | CPU |",
        "|---|---:|---:|---:|---:|---:|"]
    for title, row in observations + [("odd-prime control", control)]:
        r = row["recorded"]
        lines.append(f"| {title} | {r['geomean']:.6f} | {row['candidate']:.6f} | {r['family_balanced_geomean']:.6f} | {r['minimum']:.6f}–{r['maximum']:.6f} | {row['meta']['cpu']} |")
    lines += ["", "The word cursor variant is retained as an experiment. The selected zero-block scanner preserves the bitwise scan on nonzero blocks. Each variant has exactly one unchanged F2 repeat; no further unchanged F4 timing is collected.", "",
        "| Family | Packed first/repeat | Word cursor first/repeat | Zero blocks first/repeat |",
        "|---|---:|---:|---:|"]
    for family in observations[0][1]["recorded"]["per_family"]:
        cells = [f"{observations[i][1]['recorded']['per_family'][family]:.6f}/{observations[i+1][1]['recorded']['per_family'][family]:.6f}"
                 for i in [0, 2, 4]]
        lines.append("| " + family + " | " + " | ".join(cells) + " |")
    lines += ["", "The two MQ ratios in the zero-blocks column are below one, but effects this size are not established against the variability observed across campaigns. Several small-family ratios also vary substantially. These observations do not establish a full-system improvement, justify a universal default or assert overall performance leadership.", "",
        "The registered `binaryEliminate` and `binaryEliminateSparse` kernels use identical prepared F2 matrices with known reducers and dense targets. Timed work includes validation, workspace construction, elimination, complete decoded rows and counters, and structural hashing. Preparation is outside timing. Both arms use the same executable; complete result hashes agree.", "",
        "| Matrix parameter | Short-pass packed/sparse | Short floor flags / 4 | Longer-pass packed/sparse | Longer floor flags / 4 |",
        "|---|---:|---:|---:|---:|"]
    for (n, a, af), (m, b, bf) in zip(short, longer):
        require(n == m, "kernel schedules differ")
        lines.append(f"| {n} | {a:.6f} | {af} | {b:.6f} | {bf} |")
    lines += ["", "The initial pass targets 0.5 seconds of inner work; its matched rows are below the measured signal threshold. One longer matched pass targets 16 seconds. Its remaining flagged row is retained and does not independently justify a timing claim. No further unchanged kernel pass is collected. The short pass also retains the fixed trial-major complexity runs. The sparse arm can admit whole frames at parameters 32 and 64; from 128 upward its target count necessarily exceeds the ordinary frame cap and it uses the phased continuation. The packed cost model is O(n³/64+n²) at fixed word width; scans, decoding and hashing may dominate these finite sizes. These ratios compare those complete providers at the stated sizes and do not establish a full-system speedup of the same size.", "",
        "The independent msolve comparison uses the canonical F2 suite, one thread, full reduced grevlex output, commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`, Clang 23.1.3 and `-O3 -march=native`. Hex native C uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0; compiler/tuning differences remain part of this observed gap. Every comparison has 40 completed processes and 20 equal complete bases. Inputs and every Hex logical counter agree across these variants. All samples and outliers remain retained; no further unchanged comparator repeat is collected.", "",
        "| Hex version / msolve | Process ratio | Equal-family ratio | Pair range | CPU |",
        "|---|---:|---:|---:|---:|"]
    for title, result, meta, _ in comparisons:
        lines.append(f"| {title} | {result['geomean']:.6f} | {result['family_balanced_geomean']:.6f} | {result['minimum']:.6f}–{result['maximum']:.6f} | {meta['cpu']} |")
    lines += ["", "The selected-binary comparisons show a larger remaining gap than the initial prototype campaign and substantial variability. They do not demonstrate leadership or establish a cause for the change across campaigns. Candidate production, certificate generation, independent native verification and kernel checking remain distinct; these timings measure candidate/process work only.", "",
        "All twelve Clang/GCC ASan+UBSan variants pass on the measured carrier and final high-pivot test snapshot. All nine project gates pass after correcting only the sparse benchmark's adjacent cost-model comment. The verifier checks that exact one-line difference, both source identities, every archived source blob, and all status records. The initial phase-check failure is retained. The final compute and full-initialization executables are byte-identical to the timed zero-block binaries; the benchmark registrations add no computation-driver code.", "",
        "Coverage includes nonempty frames beyond the old dimensions, high-index packed pivot reads, target-pivot reuse, scalar/word path counters, byte/word boundaries, ordinary F2 complete F4 calls, malformed rows, exact physical-work boundaries with nonzero entries, and resource/ownership tests. Independent oracles check 567 bases with SymPy and Singular. Native verification and kernel replay remain separate from candidate timings. No fastest-open-source milestone or language impossibility is established.", "",
        f"Native runtime `{native['source_fingerprint']}`; documented runtime `{historical['source_fingerprint']}`; checks `{historical['checks_fingerprint']}`.", ""]
    if rebased:
        lines += [f"The combined tree after the scheduling-policy merge has runtime `{combined_identity['source_fingerprint']}` and checks `{combined_identity['checks_fingerprint']}`. Its separate twelve sanitizer variants, nine project gates and twenty CLI policy checks pass. Its computation executables are byte-identical to the measured carrier. The benchmark executable changes through the sampled-policy dependency; the packed runtime and kernel definitions are unchanged. Kernel timings remain bound to the original benchmark executable; no additional timing repeat is used.", ""]
    if guards:
        lines += [f"The final validation snapshot has runtime `{identity['source_fingerprint']}` and checks `{identity['checks_fingerprint']}`. The admission archive is named by its checks fingerprint and uses that same final runtime/check snapshot.", ""]
    if coverage:
        lines += ["The separate non-timed admission audit uses the exact ten timed F₂ inputs and flags. Its instrumented Clang 23 executable reproduces every complete basis and logical counter. All 108 attempted frames are accepted; shape, logical-work, physical-work and byte refusals are zero in this audit. Larger shapes can still decline under the documented caps. Counts are cumulative row visits, not distinct basis polynomials. Admission confirms path activity without establishing a timing effect.", "",
            "| Family | Inputs | Accepted / attempted frames | Known row visits | Target row visits |",
            "|---|---:|---:|---:|---:|"]
        for family, counts in coverage.items():
            lines.append(f"| {family} | {counts['inputs']} | {counts['accepted']} / {counts['attempted']} | {counts['reducer_rows']} | {counts['target_rows']} |")
        lines += ["", "The final validation adds measured buffer-size totals, target-built word-pivot reuse, 1024-target admission, and the exact logical-work boundary plus one entry. The retained initial diagnostic-probe compile failure is corrected by adding standard I/O declarations. The test measures byte-array payload lengths, excluding allocator headers, padding and RSS. The production elimination code and timed computation executables are unchanged.", ""]
    if refusal_counts:
        lines += ["A separate non-timed replay of the exact Clang sanitizer test executable exercises all diagnostic classifier branches: " + ", ".join(f"{key}={value}" for key, value in sorted(refusal_counts.items())) + ". It includes a forced byte refusal with an allowance smaller than the required private buffer. The two other categories distinguish whether the conservative byte upper bound excludes a byte refusal; they do not identify every internal failure cause.", ""]
    for name, cap in [("initial", initial), ("word", word), ("blocked", blocked), ("selected", selected)]:
        lines.append(f"`{getattr(args, name).name}`: SHA-256 `{cap.sha256}`.")
    if rebased:
        lines.append(f"`{args.rebased.name}`: SHA-256 `{rebased.sha256}`.")
    if guards:
        lines.append(f"`{args.guards.name}`: SHA-256 `{guards.sha256}`.")
    if audit:
        lines.append(f"`{args.admission.name}`: SHA-256 `{audit.sha256}`.")
    if refusal_cap:
        lines.append(f"`{args.refusals.name}`: SHA-256 `{refusal_cap.sha256}`.")
    lines += ["", "Regenerate with `python3 scripts/bench/groebner_binary_report.py " + " ".join(
        f"--{name} reports/bench-results/raw/{getattr(args, name).name}" for name in
        ["initial", "word", "blocked", "selected"]) +
        (f" --rebased reports/bench-results/raw/{args.rebased.name}" if rebased else "") +
        (f" --guards reports/bench-results/raw/{args.guards.name}" if guards else "") +
        (f" --admission reports/bench-results/raw/{args.admission.name}" if audit else "") +
        (f" --refusals reports/bench-results/raw/{args.refusals.name}" if refusal_cap else "") +
        " --report reports/bench-results/hexgroebner-binary.md --check`. Add `--current` to bind the checkout.", ""]
    text = "\n".join(lines)
    if args.check:
        require(args.report.read_text() == text, "report differs")
    else:
        args.report.write_text(text)
    print("verified packed-F2 source/check snapshots, complete F4 results and retained kernel samples")


if __name__ == "__main__":
    main()
