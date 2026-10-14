#!/usr/bin/env python3
"""Render frozen selected-root JSON as shared Lean constructor data.

This converter performs no root or sign production. The conformance readers
and ordinary-kernel proofs independently check the recorded certificates.
"""
import argparse
import copy
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
import HexSignDet.Codec.Json

/-! Shared constructor literals generated from
`conformance-fixtures/HexRCF/selected-root.json` by
`scripts/rcf/selected_literals.py`. No certificate producer is invoked. -/

open Hex.SignDet
"""

SUBJECT_NAMES = ["lowerSubject", "lowerGraph", "upperSubject", "upperGraph", "rowPacket"]


def render(module, records, subjects=False, packing=False, inverse=False, sample_root=False, root_fixture="native-sample-root.json", root_replay=False, root_names=None):
    namespace = f"Hex.RCF.SelectedRootTests.{module}"
    header = HEADER if not packing else COPYRIGHT + """
import HexSignDet.Codec.Json

/-! Constructor literals generated from
`conformance-fixtures/HexRCF/selected-packing.json` by
`scripts/rcf/selected_literals.py`. The scalar and joint readers check the
supplied evidence separately; no certificate producer is invoked. -/

open Hex.SignDet
"""
    if inverse:
        header = COPYRIGHT + """
import HexSignDet.Codec.Json

/-! Shared constructor literals from `conformance-fixtures/HexRCF/selected-inverse.json`.
The scalar, packing and supplied-inverse readers check the frozen evidence;
`scripts/rcf/selected_literals.py` performs no certificate production. -/

open Hex.SignDet
"""
    if sample_root or root_replay:
        namespace = f"Hex.RCF.RealCoefficients.{module}"
        header = COPYRIGHT + f"""module
public import HexSignDet.Codec.Json
/-! Shared constructor data from `conformance-fixtures/HexRCF/{root_fixture}`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section
"""
    lines = [header, f"namespace {namespace}"]
    if sample_root or root_replay:
        lines.append("open Hex.SignDet")
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
            prefix = "@[expose] " if sample_root or root_replay else ""
            lines.append(f"{prefix}def {name} : Codec.Json := .array {tail}")
            return name
        if node is None:
            return "Codec.Json.Value.null"
        if type(node) is int:
            return f".number ({node})"
        raise ValueError(f"unsupported literal: {node!r}")

    if root_replay:
        names = root_names or ["positive", "whole", "constant", "empty"]
        if len(records) != len(names):
            raise ValueError("unexpected frozen root-table graph count")
        for name, record in zip(names, records):
            lines.append(f"@[expose] def {name} : Codec.Json := {value(record)}")
    elif sample_root:
        if len(records) != 7:
            raise ValueError("expected exactly seven selected-root fields")
        lines.append(f"@[expose] def subject : Codec.Json := {value(records[:6])}")
        lines.append(f"@[expose] def graph : Codec.Json := {value(records[6])}")
    elif inverse:
        if len(records) != 6:
            raise ValueError("expected exactly six supplied-inverse fields")
        lines.append(f"def packet : Codec.Json := {value(records)}")
    elif subjects:
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


def render_guarded_matrix(check):
    """Render guard acceptance/refusal packets with shared constructor values."""
    directory = ROOT / "conformance/HexRCF/FiniteMatrix/Guards"
    packet = json.loads((ROOT / "conformance-fixtures/HexRCF/guarded-matrix.json").read_text())
    if len(packet) != 5 or [len(group) for group in packet[2:]] != [0, 0, 1]:
        raise ValueError("unexpected guarded-matrix packet shape")
    mutations = json.loads((ROOT / "conformance-fixtures/HexRCF/guarded-matrix-mutations.json").read_text())
    order, context, cycle = [copy.deepcopy(packet[0]) for _ in range(3)]
    order[2][0], order[2][1] = order[2][1], order[2][0]
    context[1][0] += 1
    root = cycle[4][1]
    cycle[4][2][root][1][0][0] = root
    if mutations != [order, context, cycle]:
        raise ValueError("guard mutations must change only query order, context or root dependency")
    for module, fixture, records, names, stem in [
        ("Literals", "guarded-matrix.json", packet[:2] + packet[4],
         ["positive", "zero", "extraSign"], "LiteralData"),
        ("Mutations", "guarded-matrix-mutations.json", mutations,
         ["order", "context", "cycle"], "MutationData"),
    ]:
        namespace = f"FiniteMatrixTests.Guards.{module}"
        output = render(namespace, records, root_replay=True,
                        root_fixture=fixture, root_names=names)
        lines = output.splitlines()
        first = next(i for i, line in enumerate(lines) if line.startswith("@[expose] def j0 "))
        header, body = "\n".join(lines[:first]) + "\n", lines[first:-1]
        chunks = [body[i:i + 250] for i in range(0, len(body), 250)]
        expected = {f"{stem}{i}.lean" for i in range(len(chunks) - 1)}
        if {path.name for path in directory.glob(f"{stem}*.lean")} - expected:
            raise ValueError(f"obsolete guarded-matrix {stem} modules")
        for i, chunk in enumerate(chunks):
            name = module if i == len(chunks) - 1 else f"{stem}{i}"
            prefix = header
            if i:
                prefix = prefix.replace("public import HexSignDet.Codec.Json",
                    "public import HexSignDet.Codec.Json\n"
                    f"public import HexRCF.FiniteMatrix.Guards.{stem}{i - 1}")
            output = prefix + "\n".join(chunk) + f"\nend Hex.RCF.RealCoefficients.{namespace}\n"
            destination = directory / f"{name}.lean"
            if len(output.splitlines()) > 300:
                raise ValueError(f"literal module exceeds 300 lines: {destination}")
            if check:
                if destination.read_text() != output:
                    raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
            else:
                destination.write_text(output)



def render_guarded_quotient(check):
    """Render supplied inverse evidence and its exact context mutation."""
    fixture = "guarded-quotient.json"
    values = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    if len(values) != 4 or len(values[1]) != 5 or values[1][0] != [[-1, 1], [-1, 1]]:
        raise ValueError("unexpected guarded-quotient packet shape")
    stale = copy.deepcopy(values[0])
    stale[2][stale[1]][0][0] += 1
    if values[3] != stale:
        raise ValueError("inverse context mutation must change only the root node context")
    output = render("FiniteMatrixTests.Guards.Quotient.Literals", values, root_replay=True,
                    root_fixture=fixture,
                    root_names=["inverseGraph", "packing", "alternateGraph", "staleGraph"])
    if len(output.splitlines()) > 300:
        raise ValueError("quotient literal module exceeds 300 lines")
    destination = ROOT / "conformance/HexRCF/FiniteMatrix/Guards/Quotient/Literals.lean"
    if check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)


def render_cell_replay(check):
    directory = ROOT / "conformance/HexRCF/CellReplay"
    positive = json.loads((ROOT / "conformance-fixtures/HexRCF/cell-replay.json").read_text())
    mutations = json.loads((ROOT / "conformance-fixtures/HexRCF/cell-replay-mutations.json").read_text())
    if len(positive) != 2 or len(positive[0]) != 2 or len(positive[1]) != 3:
        raise ValueError("unexpected complete-cell packet shape")
    middle = positive[1][1]
    expected = [copy.deepcopy(middle) for _ in range(5)]
    if middle[0] != [0, 0, 1]:
        raise ValueError("unexpected ordinary middle sample")
    expected[0][0][1] = 1
    graph = expected[1][5][4]
    graph[2][graph[1]][1][0][0] = graph[1]
    graph = expected[2][5][4]
    if graph[2][graph[1]][0][0] != [[], 0, []]:
        raise ValueError("unexpected rational context")
    graph[2][graph[1]][0][0][1] = 1
    expected[3][3] = copy.deepcopy(positive[1][2][3])
    expected[3][4] = copy.deepcopy(positive[1][2][4])
    graph = expected[4][5][4]
    if graph[2][graph[1]][0][10] != [1, [0], [0], 1, [[1]]]:
        raise ValueError("unexpected middle-row basis")
    graph[2][graph[1]][0][10] = [0, [], [], 1, []]
    if mutations != expected:
        raise ValueError("complete-cell mutations changed unlisted fields")
    for stem, fixture, records, names in [
        ("Literals", "cell-replay.json", positive, ["sections", "sectors"]),
        ("Mutations", "cell-replay-mutations.json", mutations,
         ["badPoint", "cycle", "stale", "otherRoot", "missingBasis"]),
    ]:
        output = render("CellReplayTests." + stem, records, root_replay=True,
                        root_fixture=fixture, root_names=names)
        lines = output.splitlines()
        first = next(i for i, line in enumerate(lines) if line.startswith("@[expose] def j0 "))
        header, body = "\n".join(lines[:first]) + "\n", lines[first:-1]
        chunks = [body[i:i + 250] for i in range(0, len(body), 250)]
        prefix = "LiteralData" if stem == "Literals" else "MutationData"
        expected_files = set()
        for index, chunk in enumerate(chunks):
            name = stem if index == len(chunks) - 1 else f"{prefix}{index}"
            expected_files.add(name + ".lean")
            imports = header
            if index:
                imports = imports.replace("public import HexSignDet.Codec.Json",
                    "public import HexSignDet.Codec.Json\n"
                    f"public import HexRCF.CellReplay.{prefix}{index - 1}")
            text = imports + "\n".join(chunk) + f"\nend Hex.RCF.RealCoefficients.CellReplayTests.{stem}\n"
            destination = directory / (name + ".lean")
            if check:
                if destination.read_text() != text:
                    raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
            else:
                destination.write_text(text)
        actual = {p.name for p in directory.glob(prefix + "*.lean")} | {stem + ".lean"}
        if actual != expected_files:
            raise ValueError(f"obsolete complete-cell {stem} modules")


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
             "import HexRCF.SelectedRoot.Literals", "import HexSignDet.Codec.Bytes",
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
    lines = [COPYRIGHT, "import HexSignDet.Codec.Json", "",
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
    lines = [COPYRIGHT, "import HexSignDet.Codec.Bytes", "",
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
    destination = directory / "InverseData.lean"
    records = json.loads((ROOT / "conformance-fixtures/HexRCF/selected-inverse.json").read_text())
    output = render("InverseData", records, inverse=True)
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
    value = json.loads((ROOT / "conformance-fixtures/HexRCF/native-sample-root.json").read_text())
    destination = ROOT / "conformance/HexRCF/NativeSampleModelLiterals.lean"
    output = render("NativeSampleModelLiterals", value, sample_root=True)
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    fixture = "native-selection-root.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    if len(value) != 2 or len(value[0]) != 6:
        raise ValueError("expected a complete selected-root subject and graph")
    destination = ROOT / "conformance/HexRCF/NativeSelectionLiterals.lean"
    output = render("NativeSelectionLiterals", value[0] + [value[1]],
                    sample_root=True, root_fixture=fixture)
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    fixture = "root-replay.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    destination = ROOT / "conformance/HexRCF/RootReplayLiterals.lean"
    output = render("RootReplayLiterals", value, root_replay=True, root_fixture=fixture)
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    fixture = "nested-root-table.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    destination = ROOT / "conformance/HexRCF/NestedRootLiterals.lean"
    output = render("NestedRootLiterals", [value], root_replay=True,
                    root_fixture=fixture, root_names=["positive"])
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    fixture = "root-transport.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    destination = ROOT / "conformance/HexRCF/RootTransportLiterals.lean"
    output = render("RootTransportLiterals", value, root_replay=True,
                    root_fixture=fixture,
                    root_names=["subject", "graph", "negativeSubject", "negativeGraph",
                                "wordSubject", "wordGraph"])
    if args.check:
        if destination.read_text() != output:
            raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
    else:
        destination.write_text(output)
    directory = ROOT / "conformance/HexRCF/NestedTransport"
    fixture = "nested-transport.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    output = render("Literals", value, root_replay=True, root_fixture=fixture,
                    root_names=["subject", "graph"]).replace(
        "Hex.RCF.RealCoefficients.Literals",
        "Hex.RCF.RealCoefficients.NestedTransportTests.Literals")
    outputs = [(directory / "Literals.lean", output)]
    fixture = "nested-transport-endpoint.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    output = render("EndpointLiterals", value, root_replay=True, root_fixture=fixture,
                    root_names=["subject", "graph"]).replace(
        "Hex.RCF.RealCoefficients.EndpointLiterals",
        "Hex.RCF.RealCoefficients.NestedTransportTests.EndpointLiterals")
    outputs.append((directory / "EndpointLiterals.lean", output))
    fixture = "nested-transport-signs.json"
    value = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    output = render("SignLiterals", value, root_replay=True, root_fixture=fixture,
                    root_names=["polynomials", "evidence"]).replace(
        "Hex.RCF.RealCoefficients.SignLiterals",
        "Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals")
    lines = output.splitlines()
    first = next(i for i, line in enumerate(lines) if line.startswith("@[expose] def j0 "))
    # Each constructor occupies one dependency-ordered line. Leave header room
    # below the repository's 300-line new-file limit.
    split = max(first + 1, 279)
    prefix = "\n".join(lines[:first]) + "\n"
    end = "end Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals\n"
    outputs.append((directory / "SignData.lean", prefix +
                    "\n".join(lines[first:split]) + "\n" + end))
    if "public import HexSignDet.Codec.Json" not in prefix:
        raise ValueError("literal header has no codec import")
    prefix = prefix.replace("public import HexSignDet.Codec.Json",
        "public import HexSignDet.Codec.Json\npublic import HexRCF.NestedTransport.SignData")
    outputs.append((directory / "SignLiterals.lean", prefix +
                    "\n".join(lines[split:]) + "\n"))
    for destination, output in outputs:
        if len(output.splitlines()) > 300:
            raise ValueError(f"literal module exceeds 300 lines: {destination}")
        if args.check:
            if destination.read_text() != output:
                raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
        else:
            destination.write_text(output)
    fixture = "finite-matrix.json"
    groups = json.loads((ROOT / "conformance-fixtures/HexRCF" / fixture).read_text())
    if len(groups) != 5 or [len(group) for group in groups[2:]] != [31, 43, 21]:
        raise ValueError("unexpected finite-matrix packet shape")
    values = groups[:2]
    names = ["canonical", "guarded"]
    for kind, group in zip(["scalar", "packing", "sign"], groups[2:]):
        values += group
        names += [f"{kind}{i}" for i in range(len(group))]
    output = render("FiniteMatrixTests.Literals", values, root_replay=True,
                    root_fixture=fixture, root_names=names)
    lines = output.splitlines()
    first = next(i for i, line in enumerate(lines) if line.startswith("@[expose] def j0 "))
    body = lines[first:-1]
    header = "\n".join(lines[:first]) + "\n"
    chunks = [body[i:i + 260] for i in range(0, len(body), 260)]
    directory = ROOT / "conformance/HexRCF/FiniteMatrix"
    expected = {f"LiteralData{i}.lean" for i in range(len(chunks) - 1)}
    obsolete = {path.name for path in directory.glob("LiteralData*.lean")} - expected
    if obsolete:
        raise ValueError(f"obsolete finite-matrix literal modules: {sorted(obsolete)}")
    for i, chunk in enumerate(chunks):
        name = "Literals" if i == len(chunks) - 1 else f"LiteralData{i}"
        prefix = header
        if i:
            prefix = prefix.replace("public import HexSignDet.Codec.Json",
                "public import HexSignDet.Codec.Json\n"
                f"public import HexRCF.FiniteMatrix.LiteralData{i - 1}")
        output = prefix + "\n".join(chunk) + "\nend Hex.RCF.RealCoefficients.FiniteMatrixTests.Literals\n"
        destination = directory / f"{name}.lean"
        if args.check:
            if destination.read_text() != output:
                raise SystemExit(f"stale generated literals: {destination.relative_to(ROOT)}")
        else:
            destination.write_text(output)
    render_guarded_matrix(args.check)
    render_guarded_quotient(args.check)
    render_cell_replay(args.check)
    print("selected-root literals match" if args.check else "selected-root literals regenerated")


if __name__ == "__main__":
    main()
