#!/usr/bin/env python3
"""Render frozen selected-root JSON as shared Lean constructor data.

This converter performs no root or sign production. The conformance readers
and ordinary-kernel proofs independently check the recorded certificates.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COPYRIGHT = """/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
"""
HEADER = COPYRIGHT + """
module

public import HexSignDet.Codec.Json

@[expose] public section

/-! Shared constructor literals generated from
`conformance-fixtures/HexRCF/selected-root.json` by
`scripts/rcf/selected_literals.py`. No certificate producer is invoked. -/

open Hex.SignDet
"""

SUBJECT_NAMES = ["lowerSubject", "lowerGraph", "upperSubject", "upperGraph", "rowPacket"]


def render(module, records, subjects=False, packing=False):
    namespace = f"Hex.RCF.SelectedRootTests.{module}"
    header = HEADER if not packing else COPYRIGHT + """
module

public import HexSignDet.Codec.Json

@[expose] public section

/-! Constructor literals generated from
`conformance-fixtures/HexRCF/selected-packing.json` by
`scripts/rcf/selected_literals.py`. The scalar and joint readers check the
supplied evidence separately; no certificate producer is invoked. -/

open Hex.SignDet
"""
    lines = [header, f"namespace {namespace}"]
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
        names = SUBJECT_NAMES
        if len(records) != len(names):
            raise ValueError("expected exactly five source records")
        for name, record in zip(names, records):
            lines.append(f"def {name} : Codec.Json := {value(record)}")
    elif packing:
        keys = [json.dumps(record[0], separators=(",", ":"), sort_keys=True) for record in records]
        if len(set(keys)) != len(keys):
            raise ValueError("duplicate original packing literal")
        for index, (original, kept, sign, scalar, joint) in enumerate(records):
            if type(sign) is not int:
                raise ValueError(f"unsupported sign literal: {sign!r}")
            p, q, scalarGraph, jointGraph = map(value, (original, kept, scalar, joint))
            lines.append(f"def packet{index} : Codec.Json × Codec.Json × Int × Codec.Json × Codec.Json := "
                         f"({p}, {q}, ({sign}), {scalarGraph}, {jointGraph})")
        lines.append(f"def count : Nat := {len(records)}")
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


def byte_tokens(value):
    if type(value) is int:
        return [str(value)]
    if type(value) is not list:
        raise ValueError(f"unsupported byte literal: {value!r}")
    result = ["["]
    for index, child in enumerate(value):
        if index:
            result.append(",")
        result.extend(byte_tokens(child))
    return result + ["]"]


def render_bytes(value):
    """Propose bytes; ByteData.written independently checks the owner writer."""
    raw = (" ".join(byte_tokens(value)) + " ").encode("ascii")
    scalars = {byte: f"b{index}" for index, byte in enumerate(sorted(set(raw)))}
    lines = [COPYRIGHT.rstrip(), "",
             "module", "",
             "public import HexRCF.SelectedRoot.Literals", "public import HexSignDet.Codec.Bytes", "",
             "@[expose] public section", "",
             "/-! Constructor bytes proposed from the retained selected-root JSON fixture.",
             "The kernel checks their exact binding to the owner writer; no producer is called. -/",
             "", "namespace Hex.RCF.SelectedRootTests.ByteData",
             "section", "set_option maxRecDepth 65536"]
    lines.extend(f"def {name} : UInt8 := {byte}" for byte, name in scalars.items())
    count = (len(raw) + 255) // 256
    for index in reversed(range(count)):
        tail = ".nil" if index == count - 1 else f"t{index + 1}"
        for byte in reversed(raw[index * 256:(index + 1) * 256]):
            tail = f".cons {scalars[byte]} ({tail})"
        lines.append(f"def t{index} : List UInt8 := {tail}")
    lines.extend(["def literal : ByteArray := ⟨⟨t0⟩⟩", "end",
        "set_option maxRecDepth 65536 in",
        "set_option maxHeartbeats 8000000 in",
        "theorem written : Hex.RCF.SelectedRootTests.Literals.rowPacket.writeBytes = literal := by",
        "  apply ByteArray.ext", "  apply Array.toList_inj.mp",
        "  rw [Hex.SignDet.Codec.Json.Value.writeBytes_toList, Hex.SignDet.Codec.Json.Value.tokensLoop_spec]",
        "  decide +kernel",
        "set_option maxRecDepth 65536 in",
        "set_option maxHeartbeats 8000000 in",
        f"theorem size : literal.size = {len(raw)} := by decide +kernel",
        "end Hex.RCF.SelectedRootTests.ByteData"])
    return "\n".join(lines) + "\n"


def render_catalog(value):
    """Render the complete supplied root packet as shared constructor values."""
    namespace = "Hex.RCF.SelectedRootTests.CatalogData"
    lines = [COPYRIGHT, "module", "", "public import HexSignDet.Codec.Json", "",
             "@[expose] public section", "",
             "/-! Constructor data generated from `conformance-fixtures/HexRCF/selected-catalog.json`.",
             "The CatalogPacket.written proof checks the exact selected-root binding. -/", "",
             "open Hex.SignDet", f"namespace {namespace}"]
    seen = {}

    def emit(node):
        key = json.dumps(node, separators=(",", ":"))
        if key in seen:
            return seen[key]
        if type(node) is int:
            term = f".number ({node})"
        elif isinstance(node, list):
            children = [emit(child) for child in node]
            tail = ".nil"
            for child in reversed(children):
                tail = f"(.cons ({child}) {tail})"
            term = ".array " + tail
        else:
            raise ValueError(f"unsupported catalog literal: {node!r}")
        name = f"j{len(seen)}"
        seen[key] = name
        lines.append(f"def {name} : Codec.Json := {term}")
        return name

    packet = emit(value)
    lines.extend([f"def packet : Codec.Json := {packet}", f"end {namespace}"])
    return "\n".join(lines) + "\n"


def render_catalog_bytes(value):
    """Propose constructor bytes, checked independently against the owner writer."""
    namespace = "Hex.RCF.SelectedRootTests.CatalogByteData"
    raw = (" ".join(byte_tokens(value)) + " ").encode("ascii")
    names = {byte: f"b{index}" for index, byte in enumerate(sorted(set(raw)))}
    lines = [COPYRIGHT, "module", "", "public import HexSignDet.Codec.Bytes", "",
             "@[expose] public section", "",
             "/-! Constructor bytes generated from `conformance-fixtures/HexRCF/selected-catalog.json`.",
             "CatalogBytes.packetWritten checks the exact owner-writer output. -/", "",
             f"namespace {namespace}", "section", "set_option maxRecDepth 32768"]
    lines.extend(f"def {name} : UInt8 := {byte}" for byte, name in names.items())
    chunks = [raw[i:i + 256] for i in range(0, len(raw), 256)]
    for index in reversed(range(len(chunks))):
        tail = ".nil" if index == len(chunks) - 1 else f"t{index + 1}"
        for byte in reversed(chunks[index]):
            tail = f"(.cons {names[byte]} {tail})"
        lines.append(f"def t{index} : List UInt8 := {tail}")
    lines.extend(["def literal : ByteArray := ⟨⟨t0⟩⟩", "end", f"end {namespace}"])
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
    destination = directory / "ByteData.lean"
    output = render_bytes(fixtures["subjects"][SUBJECT_NAMES.index("rowPacket")])
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    destination = directory / "PackingData.lean"
    records = json.loads((ROOT / "conformance-fixtures/HexRCF/selected-packing.json").read_text())
    output = render("PackingData", records, packing=True)
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    value = json.loads((ROOT / "conformance-fixtures/HexRCF/selected-catalog.json").read_text())
    for module, output in [("CatalogData", render_catalog(value)),
                           ("CatalogByteData", render_catalog_bytes(value))]:
        destination = directory / f"{module}.lean"
        if args.check:
            if destination.read_text() != output:
                raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
        else:
            destination.write_text(output)
    print("selected-root literals match" if args.check else "selected-root literals regenerated")


if __name__ == "__main__":
    main()
