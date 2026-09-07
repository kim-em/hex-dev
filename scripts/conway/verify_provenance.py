#!/usr/bin/env python3
"""Verify recorded source hashes against a committed tree, without rebuilding.

An explicit --commit overrides matching_sources_commit / commit in each report.
Historical reports lacking dependency hashes verify only their recorded sources;
this does not reconstruct missing historical evidence. Artifact hashes are
checked against files in the current checkout, independently of the source tree.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def verify(path, commit=None, binary=None):
    data = json.loads(path.read_text())
    revision = commit or data.get("matching_sources_commit") or data.get("commit")
    if not revision:
        raise ValueError(f"{path}: no source revision; supply --commit")
    recorded = {**data.get("source_sha256", {}), **data.get("dependency_sha256", {})}
    if not recorded:
        raise ValueError(f"{path}: no source hashes")
    for name, expected in recorded.items():
        content = subprocess.check_output(["git", "show", f"{revision}:{name}"])
        if hashlib.sha256(content).hexdigest() != expected:
            raise ValueError(f"{path}: source differs at {revision}:{name}")
    if "artifact_sha256" in data:
        if (
            hashlib.sha256(Path(data["artifact"]).read_bytes()).hexdigest()
            != data["artifact_sha256"]
        ):
            raise ValueError(f"{path}: artifact differs at {data['artifact']}")
    if binary is not None:
        if hashlib.sha256(binary.read_bytes()).hexdigest() != data.get("binary_sha256"):
            raise ValueError(f"{path}: benchmark binary differs at {binary}")
    print(f"{path}: {len(recorded)} source hashes match {revision}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", nargs="+", type=Path)
    parser.add_argument("--commit")
    parser.add_argument(
        "--binary", type=Path, help="Also verify a rebuilt benchmark binary"
    )
    args = parser.parse_args()
    for path in args.reports:
        verify(path, args.commit, args.binary)


if __name__ == "__main__":
    main()
