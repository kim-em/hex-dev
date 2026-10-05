"""Validate retained nested-table timing records without rewriting metadata."""
from pathlib import Path
import gzip
import hashlib
import json
import tempfile
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
    import statistics
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
    for row in samples:
        depth, size = int(row["function"][-1]), row["parameter"]
        key = "productionResultHash" if "runProduce" in row["function"] else "replayResultHash"
        counts = row["counters"]
        if (row["state"] != "complete" or row["exit_code"] != 0 or
                row["result_hash"] != hex(expected[depth, size][key]) or
                counts["callbacks"] != 1 or counts["overflow"] != 0 or
                any(type(value) is not int or value < 0 for value in counts.values())):
            raise ValueError("failed or substituted allocation region")
    summary = {function: {str(size): {
        key: statistics.median(row["counters"][key] for row in samples
          if row["function"] == function and row["parameter"] == size)
        for key in samples[0]["counters"]} for size in [8, 32, 128]}
        for function in functions}
    if manifest["summary"] != summary:
        raise ValueError("allocation summary disagrees with original counters")
    return samples
