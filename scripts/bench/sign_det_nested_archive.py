"""Validate retained nested-table timing records without rewriting metadata."""
from pathlib import Path
import gzip
import hashlib
import json
import tempfile
import statistics
from scripts.bench import sign_det_allocations as driver
from scripts.bench import sign_det_nested_tables as bench


def validate(directory):
    directory = Path(directory)
    manifest = json.loads((directory/"archive.json").read_text())
    digest = lambda raw: hashlib.sha256(raw).hexdigest()
    if digest((directory/"whole-source.patch").read_bytes()) != manifest["whole_source_patch_sha256"]:
        raise ValueError("changed source reconstruction patch")
    collections = manifest["timing_collections"]
    if [record["label"] for record in collections] != ["first", "unchanged-rerun"] or manifest["unchanged_reruns"] != 1:
        raise ValueError("wrong retained collections or rerun count")
    identities = []
    for record in collections:
        raw = {}
        for name, binding in record["files"].items():
            relative = Path(binding["file"])
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("archive path escapes its directory")
            stored = (directory/relative).read_bytes()
            if digest(stored) != binding["stored_sha256"]:
                raise ValueError("changed stored bytes: "+name)
            value = gzip.decompress(stored) if relative.suffix == ".gz" else stored
            if digest(value) != binding["sha256"]:
                raise ValueError("changed original bytes: "+name)
            raw[name] = value
        meta = json.loads(raw["metadata.json"])
        if (meta["state"] != "complete" or meta["scientific_samples"] != 120 or
                meta["source_unchanged"] is not True or meta["revision"] != manifest["source_revision"] or
                meta["source_sha256"] != meta["source_sha256_after"] or
                meta["binary_sha256"] != meta["binary_sha256_after"] or
                meta["harness_binding"] != meta["harness_binding_after"] or
                meta["revision_after"] != meta["revision"] or meta["git_status_after"] != ""):
            raise ValueError("incomplete collection or changed source identity")
        if set(raw)-{"metadata.json"} != set(meta["file_sha256"]):
            raise ValueError("missing original collection files")
        for name, expected in meta["file_sha256"].items():
            if digest(raw[name]) != expected:
                raise ValueError("collection hash disagreement: "+name)
        identities.append((meta["revision"], meta["source_sha256"], meta["binary_sha256"], meta["harness_binding"]))
        with tempfile.TemporaryDirectory() as temporary:
            temporary = Path(temporary)
            (temporary/"inputs.stdout").write_bytes(raw["inputs.stdout"])
            expected = bench.validate_inputs(temporary/"inputs.stdout", sizes=bench.SHORT_SIZES)
            for depth in bench.DEPTHS:
                for operation in ("runProduce", "runTree"):
                    name = operation+str(depth)
                    path = temporary/(name+".json"); path.write_bytes(raw[name+".json"])
                    result = bench.validate_result(path, name, expected, meta["revision"], sizes=bench.SHORT_SIZES)
                    stated = {key: record["observations"][name][key] for key in result}
                    export = json.loads(raw[name+".json"])["results"][0]
                    medians = {str(size): statistics.median(
                        point["per_call_nanos"]/1e6 for point in export["points"]
                        if point["param"] == size) for size in bench.SHORT_SIZES}
                    if medians != record["observations"][name]["medians_ms"]:
                        raise ValueError("timing medians disagree with original export")
                    if result != stated:
                        raise ValueError("summary disagrees with original export")
    if identities[0] != identities[1]:
        raise ValueError("rerun changed measured sources, binary or harness")
    return collections


def validate_allocation(directory):
    """Check all retained operation regions and independently bound results."""
    directory = Path(directory)
    manifest = json.loads((directory/"archive.json").read_text())
    digest = lambda raw: hashlib.sha256(raw).hexdigest()
    raw = {}
    for name, binding in manifest["files"].items():
        path = Path(binding["file"])
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("allocation path escapes archive")
        stored = (directory/path).read_bytes()
        if digest(stored) != binding["stored_sha256"]:
            raise ValueError("changed allocation stored bytes")
        value = gzip.decompress(stored) if path.suffix == ".gz" else stored
        if digest(value) != binding["sha256"]:
            raise ValueError("changed allocation original bytes")
        raw[name] = value
    meta = json.loads(raw["metadata.json"])
    nested = json.loads(raw["nested-binding.json"])
    if (meta["state"] != "complete" or nested["state"] != "complete" or
            meta["source_unchanged"] is not True or
            meta["source_sha256"] != meta["source_sha256_after"] or
            meta["binary_sha256"] != meta["binary_sha256_after"] or
            meta["revision"] != manifest["source_revision"] or
            nested["revision"] != meta["revision"] or
            nested["binary_sha256"] != meta["binary_sha256"] or meta["git_status"] != ""):
        raise ValueError("incomplete or unbound allocation capture")
    if set(nested["file_sha256"]) != set(raw)-{"nested-binding.json"}:
        raise ValueError("missing allocation files")
    for name, expected in nested["file_sha256"].items():
        if digest(raw[name]) != expected:
            raise ValueError("allocation capture hash disagreement")
    with tempfile.TemporaryDirectory() as temporary:
        inputs = Path(temporary)/"inputs.stdout"; inputs.write_bytes(raw["inputs.stdout"])
        expected = bench.validate_inputs(inputs, sizes=bench.SHORT_SIZES)
    functions = [bench.PREFIX+op+str(d) for d in bench.DEPTHS for op in ("runProduce", "runTree")]
    samples = meta["samples"]
    if (meta["functions"] != functions or meta["parameters"] != [8, 32, 128] or
            meta["trials"] != 3 or manifest["samples"] != 36 or
            [(r["trial"], r["parameter"], r["function"]) for r in samples] !=
                [(trial, size, function) for trial in range(1, 4)
                 for size in [8, 32, 128] for function in functions]):
        raise ValueError("wrong allocation schedule")
    # Raw paths are recorded in the original commands; the DHAT provenance
    # check uses those identities even when the archive is moved elsewhere.
    for number, row in enumerate(samples):
        stem = f"{number:03d}"
        logs = {suffix: raw[stem+suffix] for suffix in (".log", ".native.log", ".dhat.json")}
        for suffix, field in ((".log", "log_sha256"), (".native.log", "native_log_sha256"),
                              (".dhat.json", "dhat_sha256")):
            if digest(logs[suffix]) != row[field]:
                raise ValueError("raw allocation sample hash disagreement")
        counts_raw = driver.counters(logs[".log"].decode())
        measured = driver.benchmark_row(logs[".log"].decode(), row["function"], row["parameter"])
        native = driver.benchmark_row(logs[".native.log"].decode(), row["function"], row["parameter"])
        if (counts_raw != row["counters"] or measured["result_hash"] != row["result_hash"] or
                native["result_hash"] != row["result_hash"] or
                measured["peak_rss_kb"] != row["instrumented_peak_rss_kb"]):
            raise ValueError("allocation metadata disagrees with raw sample")
        profiler = row["command"][row["command"].index("--profiler")+1]
        origin = next(word.removeprefix("LD_PRELOAD=") for word in profiler.split()
                      if word.startswith("LD_PRELOAD="))
        driver.check_events(counts_raw, json.loads(logs[".dhat.json"]), Path(origin))
        depth, size = int(row["function"][-1]), row["parameter"]
        key = "productionResultHash" if "runProduce" in row["function"] else "replayResultHash"
        counts = row["counters"]
        if (row["state"] != "complete" or row["exit_code"] != 0 or
                row["result_hash"] != hex(expected[depth, size][key]) or
                counts["callbacks"] != 1 or counts["overflow"] != 0 or
                any(type(value) is not int or value < 0 for value in counts.values())):
            raise ValueError("failed or substituted allocation region")
    expected_checks = {"callbacks": 1, "overflow": 0, "lean_requests": 2, "lean_bytes": 64,
                       "mimalloc_requests": 2, "mimalloc_bytes": 56,
                       "gmp_requests": 2, "gmp_bytes": 160}
    cases = [("void*", "0x12345678u"), ("uint8_t", "0xabu"),
             ("uint64_t", "0xfedcba9876543210ULL")]
    if [(r["result_type"], r["returned_value"]) for r in meta["self_checks"]] != cases:
        raise ValueError("wrong allocation ABI self-checks")
    for number, row in enumerate(meta["self_checks"]):
        stem = f"self-check-{number}"
        log, dhat = raw[stem+".log"], raw[stem+".dhat.json"]
        if (digest(log) != row["log_sha256"] or digest(dhat) != row["dhat_sha256"] or
                driver.counters(log.decode()) != expected_checks or row["counters"] != expected_checks):
            raise ValueError("allocation self-check disagreement")
        command = next(c for c in meta["compile_commands"] if Path(c[-1]).name == stem)
        driver.check_events(expected_checks, json.loads(dhat), Path(command[-1]))
    if digest(raw["collect-nested-table-allocations.py"]) != nested["adapter_sha256"]:
        raise ValueError("allocation adapter hash disagreement")
    if set(meta["callbacks"]) != set(functions):
        raise ValueError("wrong allocation callbacks")
    for number, function in enumerate(functions):
        callback = meta["callbacks"][function]
        helper = "produce" if "runProduce" in function else "checkTree"
        symbol = "lp_Hex___private_HexSignDet_NestedTables_0__Hex_SignDetBench_NestedTables_"+helper
        if (callback["symbol"] != symbol or callback["result_type"] != "void*" or
                digest(raw[f"wrapper-{number}.so"]) != callback["wrapper_sha256"]):
            raise ValueError("allocation callback binding disagreement")
    supplement = manifest["supplement"]
    if supplement["binary_sha256"] != meta["binary_sha256"]:
        raise ValueError("allocation supplement changed binary identity")
    for name, expected_hash in supplement["files"].items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("supplement path escapes archive")
        if digest((directory/relative).read_bytes()) != expected_hash:
            raise ValueError("allocation supplement hash disagreement")
    for name, expected_hash in meta["collector_sha256"].items():
        if digest((directory/"supplement/collector-sources"/name).read_bytes()) != expected_hash:
            raise ValueError("stock collector hash disagreement")
    generated = gzip.decompress((directory/"supplement/NestedTables.c.gz").read_bytes())
    symbols = (directory/"supplement/helper-symbols.txt").read_text().splitlines()
    import re
    for callback in meta["callbacks"].values():
        if (digest(generated) != callback["generated_c_sha256"] or
                not re.search(rb"LEAN_EXPORT lean_object\* " + callback["symbol"].encode() +
                              rb"\(lean_object\*", generated) or
                not any(line.split()[-1] == callback["symbol"] for line in symbols)):
            raise ValueError("generated helper ABI or symbol disagreement")
    summary = {function: {str(size): {
        key: statistics.median(row["counters"][key] for row in samples
          if row["function"] == function and row["parameter"] == size)
        for key in samples[0]["counters"]} for size in [8, 32, 128]}
        for function in functions}
    if manifest["summary"] != summary:
        raise ValueError("allocation summary disagrees with original counters")
    return samples


def validate_sources(directory):
    """Reconstruct in an isolated Git index, without changing any checkout."""
    import os
    import subprocess
    directory = Path(directory).resolve()
    manifest = json.loads((directory/"archive.json").read_text())
    root = Path(__file__).resolve().parents[2]
    with tempfile.TemporaryDirectory() as temporary:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary)/"index"))
        def git(*arguments):
            return subprocess.check_output(["git", *arguments], cwd=root, env=env)
        git("read-tree", manifest["source_base"])
        git("apply", "--cached", str(directory/"whole-source.patch"))
        tree = git("write-tree").decode().strip()
        if tree != manifest["source_tree"]:
            raise ValueError("reconstructed source tree mismatch")
        maps = []
        for collection in manifest["timing_collections"]:
            binding = collection["files"]["metadata.json"]
            path = directory/binding["file"]
            raw = path.read_bytes()
            if path.suffix == ".gz": raw = gzip.decompress(raw)
            maps.append(json.loads(raw)["source_sha256"])
        allocation = json.loads((directory/"allocation/archive.json").read_text())
        for name in ("metadata.json", "nested-binding.json"):
            path = directory/"allocation"/allocation["files"][name]["file"]
            raw = path.read_bytes()
            if path.suffix == ".gz": raw = gzip.decompress(raw)
            maps.append(json.loads(raw)["source_sha256"])
        checked = set()
        for hashes in maps:
            for name, digest in hashes.items():
                if hashlib.sha256(git("show", tree+":"+name)).hexdigest() != digest:
                    raise ValueError("reconstructed source hash mismatch: "+name)
                checked.add(name)
    return tree, len(checked)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--reconstruct-source", action="store_true")
    args = parser.parse_args()
    validate(args.directory)
    validate_allocation(args.directory/"allocation")
    if args.reconstruct_source:
        print("Reconstructed source:", validate_sources(args.directory))
    print("Validated both timing collections and all 36 allocation regions")
