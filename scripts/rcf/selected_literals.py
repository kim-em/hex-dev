#!/usr/bin/env python3
"""Render frozen selected-root JSON as shared Lean constructor data.

This converter performs no root or sign production. The conformance readers
and ordinary-kernel proofs independently check the recorded certificates.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HEADER = """/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSignDet.Codec.Json

/-! Shared constructor literals generated from
`conformance-fixtures/HexRCF/selected-root.json` by
`scripts/rcf/selected_literals.py`. No certificate producer is invoked. -/

open Hex.SignDet
"""


def render(module, records, subjects=False):
    namespace = f"Hex.RCF.SelectedRootTests.{module}"
    lines = [HEADER, f"namespace {namespace}"]
    seen = {}

    def value(node):
        if isinstance(node, list):
            key = json.dumps(node, separators=(",", ":"))
            if key in seen:
                return seen[key]
            items = [value(item) for item in node]
            name = f"j{len(seen)}"
            seen[key] = name
            tail = ".nil"
            for item in reversed(items):
                tail = f"(.cons ({item}) {tail})"
            lines.append(f"def {name} : Codec.Json := .array {tail}")
            return name
        if type(node) is int:
            return f".number ({node})"
        raise ValueError(f"unsupported literal: {node!r}")

    if subjects:
        names = ["lowerSubject", "lowerGraph", "upperSubject", "upperGraph", "rowPacket"]
        if len(records) != len(names):
            raise ValueError("expected exactly five source records")
        for name, record in zip(names, records):
            lines.append(f"def {name} : Codec.Json := {value(record)}")
    else:
        for index, (key, sign, graph) in enumerate(records):
            polynomial, evidence = value(key), value(graph)
            lines.append(f"def packet{index} : Codec.Json × Int × Codec.Json := "
                         f"({polynomial}, ({sign}), {evidence})")
        if module == "Packets":
            fields = ", ".join(f"packet{i}" for i in range(len(records)))
            lines.append(f"def packets : List (Codec.Json × Int × Codec.Json) := [{fields}]")
    lines.append(f"end {namespace}")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    fixtures = json.loads((ROOT / "conformance-fixtures/HexRCF/selected-root.json").read_text())
    directory = ROOT / "conformance/HexRCF/SelectedRoot"
    mappings = [("Literals", "subjects"), ("Packets", "packets"),
                ("Intermediates", "intermediates"), ("RowIntermediates", "row_intermediates")]
    for module, key in mappings:
        destination = directory / f"{module}.lean"
        output = render(module, fixtures[key], subjects=key == "subjects")
        if args.check:
            if destination.read_text() != output:
                raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
        else:
            destination.write_text(output)
    print("selected-root literals match" if args.check else "selected-root literals regenerated")


if __name__ == "__main__":
    main()
