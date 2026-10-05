#!/usr/bin/env python3
"""Package a completed memory collection without changing its metadata bytes."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_memory import validate_retained


def package(source, target):
    source, target = Path(source).resolve(), Path(target).resolve()
    if target.exists():
        raise ValueError("archive directory must be new")
    if target.is_relative_to(source):
        raise ValueError("archive must be outside the source collection")
    metadata_bytes = (source / "metadata.json").read_bytes()
    metadata = json.loads(metadata_bytes)
    if metadata.get("state") != "complete":
        raise ValueError("only complete collections can be packaged")
    names = set(metadata["file_sha256"]) | {"metadata.json"}
    if {p.name for p in source.iterdir() if p.is_file()} != names:
        raise ValueError("collection has missing or additional files")
    raw = {}
    for name in sorted(names):
        if Path(name).name != name:
            raise ValueError("capture filenames must stay in the directory")
        data = (source / name).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if name != "metadata.json" and digest != metadata["file_sha256"][name]:
            raise ValueError("original capture hash differs")
        raw[name] = data
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".hex-memory-", dir=target.parent) as temporary:
        staging = Path(temporary) / "archive"
        staging.mkdir()
        archive = {"schema": "hex-memory-archive-v1", "files": {}}
        for name, data in raw.items():
            stored = name if name == "metadata.json" else name + ".gz"
            payload = data if name == "metadata.json" else gzip.compress(data, mtime=0)
            (staging / stored).write_bytes(payload)
            archive["files"][name] = {"stored": stored,
                                      "raw_sha256": hashlib.sha256(data).hexdigest(),
                                      "stored_sha256": hashlib.sha256(payload).hexdigest()}
        (staging / "archive.json").write_text(json.dumps(archive, indent=2) + "\n")
        checked = validate_retained(staging)
        staging.rename(target)
        return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    metadata = package(args.source, args.target)
    print(f"Validated {len(metadata['runs'])} captures; original metadata preserved.")


if __name__ == "__main__":
    main()
