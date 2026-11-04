"""Verify additional packed-F2 guard snapshots without substituting timing sources."""
import hashlib
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_trie_report import source, require


def blobs(cap, manifest, prefix):
    for path, oid in listing(manifest).items():
        data = cap.read(prefix + path)
        require(hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == oid,
                "source blob differs: " + path)



def combined(rebased, selected, selected_manifest, final=False):
    combined = source(rebased, "pivots")
    documented = rebased.json("identity.json")
    require("clang version 23.1.3" in rebased.text("native-clang.log") and
            "16.2.0" in rebased.text("native-gcc.log"), "combined sanitizer compilers differ")
    if final:
        require("initial-admission-probe-failure.log" in rebased.payloads, "missing diagnostic probe failure record")
    if "initial-admission-probe-failure.log" in rebased.payloads:
        failure = rebased.json("initial-admission-probe-failure-status.json")
        require(failure[0]["name"] == "clang" and failure[0]["exit_code"] != 0 and
                "requires inclusion of the header <stdio.h>" in rebased.text("initial-admission-probe-failure.log"),
                "diagnostic probe failure record differs")
    require(documented["source_fingerprint"] == combined["source_fingerprint"] and
            documented["source_manifest_sha256"] == hashlib.sha256(
                combined["source_manifest"].encode()).hexdigest(), "combined runtime differs")
    checks = rebased.text("checks.manifest")
    require(documented["checks_manifest_sha256"] == hashlib.sha256(checks.encode()).hexdigest(),
            "combined check manifest differs")
    blobs(rebased, checks, "checks-sources/")
    for label, names in [("native", ["clang", "gcc"]),
            ("full", ["build", "oracles", "driver", "bench", "dag", "phase4", "manifest", "headers", "lines"])]:
        rows = rebased.json(label + "-status.json")
        require([r["name"] for r in rows] == names and all(r["exit_code"] == 0 and
                all(r[k] == v for k, v in documented.items()) for r in rows),
                "failed or stale combined checks")
    require(all(r["variants"] == ["Native", "AVX2", "AVX2Remainder", "Scalar", "Remainder", "ScalarRemainder"] and
                r["sanitize"] == ["address", "undefined"] for r in rebased.json("native-status.json")),
            "combined native coverage differs")
    require("567 unique reduced bases match SymPy" in rebased.text("full/oracles.log") and
            "567 reduced bases match Singular" in rebased.text("full/oracles.log"),
            "combined oracle coverage differs")
    require(combined["compilers"] == selected_manifest["compilers"] and
            combined["native_options"] == selected_manifest["native_options"],
            "combined compiler/options differ")
    require(all(combined["binary_sha256"][key] == selected_manifest["binary_sha256"][key]
                for key in ["compute", "compute-reference"]),
            "combined computation executable differs from measured carrier")
    old_sources = listing(selected.text("current.source.manifest"))
    new_sources = listing(combined["source_manifest"])
    allowed = {"HexGroebner/README.md", "HexGroebner/Sampled.lean", "HexGroebner/SamplingRound.lean",
               "bench/HexGroebner/Driver/Sampled.lean", "scripts/bench/groebner_cli_measure.py"}
    changes = {p for p in old_sources if old_sources[p] != new_sources[p]}
    edits = {
        "HexGroebner/EliminationKernel.lean": [("A declined\nattempt's work retains the sparse reference's accounting.",
            "A declined\nattempt's physical work is unreported; the continuation retains the reference counters.")],
        "HexGroebner/Symbolic.lean": [("work := limits.work - s.statistics.work,densePivots := limits.densePivots,binaryPivots := limits.binaryPivots",
            "work := limits.work - s.statistics.work\n    densePivots := limits.densePivots, binaryPivots := limits.binaryPivots")],
        "bench/HexGroebner/Bench/Primitives.lean": [("-- Dense elimination is O(n³); preparation and complete output hashing are O(n²).",
            "-- O(n³/64+n²) packed elimination is cubic at fixed word width.\n-- Quadratic scans, decoding and hashing can dominate these finite sizes.")],
    }
    require(set(old_sources) == set(new_sources) and changes <= allowed | set(edits),
            "combined tree changed the packed runtime or kernel definitions")
    for path in changes & set(edits):
        before = selected.text("current-sources/" + path)
        for old, new in edits[path]:
            require(before.count(old) == 1, "missing exact documentation edit")
            before = before.replace(old, new, 1)
        require(before == rebased.text("pivots/root-sources/" + path),
                "more than documentation or formatting changed")
    cli = rebased.json("cli/status.json")
    require(len(cli) == 20 and sum(r["exit_code"] == 2 for r in cli) == 4 and
            all(r["exit_code"] in [0, 2] for r in cli), "combined CLI coverage differs")
    for driver in ["compute", "compute-reference"]:
        for prime in [2, 32003]:
            reference = None
            for label in ["default", "false", "true", "duplicate"]:
                value = rebased.json(f"cli/{driver}-p{prime}-{label}.stdout")
                require(value["binaryPivots"] == (label == "true"), "combined CLI policy differs")
                result = value["basis"], value["statistics"]
                reference = reference or result
                require(result == reference, "combined CLI bases/statistics differ")
    return documented


def admission(cap, guard, timed):
    """Reconstruct frame denominators from the instrumented, non-timed run."""
    import csv
    import json
    from collections import Counter
    identity = cap.json("identity.json")
    require(identity == cap.json("audit/status.json")["identity"] and all(
        identity[k] == v for k, v in guard.json("identity.json").items() if k != "source_commit"),
        "admission source/check snapshot differs")
    status = cap.json("audit/status.json")
    require(hashlib.sha256(cap.read("probe/probe.c")).hexdigest() == status["probe_sha256"] and
            cap.read("probe/probe.c") == guard.read("probes/clang/probe.c"),
            "admission probe differs from the sanitizer-tested wrapper")
    meta = timed.json("pivots/f2-false/metadata.json")
    expected = {r["case"]: r for r in meta["samples"] if r["arm"] == "B" and r["block"] == 0}
    require(status["fields"] == ["columns", "reducers", "targets", "entries", "reason", "byteUpper", "byteAllowance"] and
            [r["case"] for r in status["samples"]] == list(expected),
            "admission schema/order/unique coverage differs")
    require(status["binary_sha256"] == guard.json("native-executables.json")["clang"]["usage"],
            "admission executable differs from the sanitizer carrier")
    require(len(status["samples"]) == len(expected) == 10, "admission coverage differs")
    families = {}
    for row in status["samples"]:
        case = row["case"]
        require(case in expected and row["family"] == expected[case]["family"] and
                row["exit_code"] == 0 and row["complete_basis_and_statistics_equal"],
                "failed admission input")
        raw = cap.read("audit/" + case + ".input.json")
        require(hashlib.sha256(raw).hexdigest() == row["input_sha256"] ==
                meta["input_sha256"][case + ".json"], "admission input differs")
        command = row["command"]
        marker = expected[case]["command"].index("--work")
        require(command[command.index("--work"):-1] == expected[case]["command"][marker:-1] and
                command[command.index("--binary-pivots")+1] == "true", "admission flags differ")
        value = cap.json("audit/" + case + ".stdout")
        original = timed.json("pivots/f2-false/" + case + "-b0-B.stdout")
        require(value["binaryPivots"] and value["basis"] == original["basis"] and
                value["statistics"] == original["statistics"], "admission complete result differs")
        frames = list(csv.DictReader(cap.text("audit/" + case + ".frames.csv").splitlines(),
                                    fieldnames=status["fields"]))
        for frame in frames:
            for key in status["fields"]:
                if key != "reason": frame[key] = int(frame[key])
        require(frames == row["frames"], "admission raw frames differ")
        counts = json.loads(cap.text("audit/" + case + ".stderr").splitlines()[-1])
        accepted = sum(f["reason"] == "accepted" for f in frames)
        require(counts == row["counts"] and int(counts["bulkAccepted"]) == accepted and
                int(counts["bulkDeclined"]) == len(frames)-accepted,
                "admission counters disagree")
        family = families.setdefault(row["family"], Counter())
        family["inputs"] += 1
        for f in frames:
            nc, nr, nt, entries = [f[k] for k in ["columns", "reducers", "targets", "entries"]]
            words, rows = (nc+63)//64, nr+nt
            logical = rows*65+2*entries+nc*5+nt*(entries+(nt+3)*nc+64)+nc
            physical = rows*words+3*entries+4*nt*nc+6*nc+nt*(rows*words+64)
            upper = (min(rows,nc)+1)*words*8+20*entries+128*rows+25*nt*nc+10*nc
            require(f["byteUpper"] == upper, "admission byte upper bound differs")
            reason = f["reason"]
            if reason == "accepted":
                require(nc <= 16384 and nr <= 16384 and nt <= 1024 and
                        logical <= 2**32 and physical <= 2**28, "accepted shape exceeds a cap")
                family["reducer_rows"] += nr
                family["target_rows"] += nt
            else:
                expected_reason = "shape" if nc > 16384 or nr > 16384 or nt > 1024 else (
                    "logical" if logical > 2**32 else "physical" if physical > 2**28 else
                    "other_without_byte_refusal" if upper <= f["byteAllowance"] else
                    "other_possible_byte_refusal")
                require(reason == expected_reason, "admission refusal classification differs")
            family["attempted"] += 1
            family[reason] += 1
    require(sum(v["attempted"] for v in families.values()) == 108 and
            sum(v["accepted"] for v in families.values()) == 108, "admission totals differ")
    return families


def refusals(cap, guard):
    """The same tested executable exercises every diagnostic reason branch."""
    import csv
    from collections import Counter
    status = cap.json("status.json")
    require(status["exit_code"] == 0 and status["binary_sha256"] ==
            guard.json("native-executables.json")["clang"]["checkNative"],
            "forced refusal executable differs")
    fields = ["columns", "reducers", "targets", "entries", "reason", "byteUpper", "byteAllowance"]
    require(status["fields"] == fields, "forced refusal schema differs")
    frames = list(csv.DictReader(cap.text("frames.csv").splitlines(), fieldnames=fields))
    counts = Counter(f["reason"] for f in frames)
    require(len(frames) == status["frames"] and counts == status["counts"] and set(counts) ==
            {"accepted", "shape", "logical", "physical", "other_without_byte_refusal", "other_possible_byte_refusal"},
            "forced refusal coverage differs")
    byte_refused = False
    for f in frames:
        nc, nr, nt, entries = [int(f[k]) for k in ["columns", "reducers", "targets", "entries"]]
        words, rows = (nc+63)//64, nr+nt
        logical = rows*65+2*entries+nc*5+nt*(entries+(nt+3)*nc+64)+nc
        physical = rows*words+3*entries+4*nt*nc+6*nc+nt*(rows*words+64)
        if f["reason"] == "shape": require(nc > 16384 or nr > 16384 or nt > 1024, "shape refusal differs")
        if f["reason"] == "logical": require(logical > 2**32, "logical refusal differs")
        if f["reason"] == "physical": require(logical <= 2**32 and physical > 2**28, "physical refusal differs")
        if f["reason"] == "other_possible_byte_refusal" and int(f["byteAllowance"]) < (min(rows,nc)+1)*words*8:
            byte_refused = True
    require(byte_refused, "private byte refusal not exercised")
    return counts
