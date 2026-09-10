#!/usr/bin/env python3
"""Persistent exact-domain determinant comparator, one JSON request per line.

The first request prepares the matrix; subsequent calls time determinant and
canonical serialization on that identical prepared matrix. LeanBench warms the
process before timing. ``kind: overhead`` measures framing and dispatch alone.
"""
import json
import sys
from functools import lru_cache

from matrix_carriers import prepare


@lru_cache(maxsize=128)
def prepared(line):
    record = json.loads(line)
    if record["kind"] != "det":
        raise ValueError("expected det record")
    return prepare(record)


def run(line):
    if json.loads(line).get("kind") == "overhead":
        return 0
    codec, matrix = prepared(line)
    return codec.encode(matrix.det())


def main():
    for line in sys.stdin:
        try:
            reply = {"ok": True, "result": run(line)}
        except Exception as error:
            reply = {"ok": False, "error": str(error)}
        print(json.dumps(reply, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
