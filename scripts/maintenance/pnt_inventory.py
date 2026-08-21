#!/usr/bin/env python3
"""Generate and validate the source-pinned PNT+/LeanCert usage inventory.

Refresh mode reads an exact checkout of PrimeNumberTheoremAnd, masks Lean
comments and string literals without changing source offsets, and records:

* textual and executable ``interval_decide`` / ``interval_auto`` occurrences;
* direct LeanCert imports, qualified references, and the six imported public
  interface families that the migration must classify;
* executable textual ``native_decide`` occurrences (trust-audit candidates); and
* the generated FKS2 Table4Ext shard sizes plus named BKLNW tactic families.

Check mode is deliberately network-free.  It validates the committed JSONL's
pins, record digest, counts, ordering, classifications, and batch invariants.
Use ``--require-classified`` for a migration/release claim; the ordinary
pre-D8 structural check permits explicit ``pending`` migration decisions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[2]
PNT_COMMIT = "21998bb6196b56789f72a52656a781a75e134eb0"
LEANCERT_COMMIT = "58edbea59458e9b010262238eaca27b6e0240dae"
MATHLIB_COMMIT = "905b95818eb32af7874a58b427f50c1711a5e96c"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.32.2"
FORMAT_VERSION = 1
PNT_LEAN_SOURCE_DIGEST = "84b1cdfe1cae7b6ddc181aede13c35b276422a206f6815143c2a1c50c3c0b112"
PNT_LEAN_SOURCE_FILES = 232
# Digest of fixed record identity with editable migration decisions removed.
# It covers source locations plus reviewed interface/workload annotations; it
# is not described as if every annotation were mechanically source-derived.
PNT_AUDIT_RECORD_DIGEST = "6cfed911ea5dc11a114be8cadad83aaf1a68972a166700ceea894a7145e2d07d"

EXPECTED = {
    "interval_decide_actual": 280,
    "interval_decide_textual": 290,
    "interval_auto_actual": 60,
    "interval_auto_textual": 61,
    "native_decide_actual": 83,
    "leancert_import": 16,
    "leancert_reference": 107,
    "dependency_interface": 6,
    "fks2_cells": 13590,
    "fks2_shards": 14,
    "bklnw_table10_target_sites": 87,
    "bklnw_table10_a2_sites": 38,
    "bklnw_table12_checks": 130,
    "bklnw_table12_ordinary_rows": 24,
    "bklnw_table12_logarithmic_rows": 2,
}

DEPENDENCY_INTERFACES = {
    "LeanCert.ANT": (
        "whole-interval ANT expression checker used by the extended FKS2 table",
        "fks2-table4ext",
    ),
    "LeanCert.CertifiedBounds.BKLNW": (
        "certified exponential and power bounds used by the BKLNW sums",
        "bklnw-certified-bounds",
    ),
    "LeanCert.CertifiedBounds.Chebyshev": (
        "certified Chebyshev bounds used by Chebyshev, FKS2 floor, and Ramanujan proofs",
        "chebyshev-certified-bounds",
    ),
    "LeanCert.CertifiedBounds.Li2": (
        "Li(2) integrand, positivity, boundedness, value, and integral bounds",
        "li2-certified-bounds",
    ),
    "LeanCert.Tactic.IntervalAuto": (
        "interval_decide and interval_auto tactic entry points",
        "interval-tactics",
    ),
    "LeanCert.Validity.AffineCover": (
        "affine-cover certificate used by the small-x FKS2 floor",
        "affine-cover",
    ),
}

# Lexical qualified references are audit evidence, not separate migration
# obligations.  This table records which reviewed imported interface owns each
# namespace surface, including namespaces reached transitively by that import.
REFERENCE_PROVENANCE = {
    "LeanCert.ANT": ("LeanCert.ANT",),
    "LeanCert.CertifiedBounds.BKLNW": ("LeanCert.CertifiedBounds.BKLNW",),
    "LeanCert.CertifiedBounds.Chebyshev": (
        "LeanCert.CertifiedBounds.Chebyshev",
    ),
    "LeanCert.CertifiedBounds.Li2": ("LeanCert.CertifiedBounds.Li2",),
    "LeanCert.Core": ("LeanCert.ANT", "LeanCert.Validity.AffineCover"),
    "LeanCert.Validity": ("LeanCert.Validity.AffineCover",),
}

CLASSIFICATIONS = {
    "pending",
    "accepted-unchanged",
    "accepted-after-rewrite",
    "replaced-by-stronger-result",
    "retained-other-dependency",
    "expected-failure",
}

TOKEN_RE = {
    name: re.compile(rf"(?<![A-Za-z0-9_']){name}(?![A-Za-z0-9_'])")
    for name in ("interval_decide", "interval_auto", "native_decide")
}
IMPORT_RE = re.compile(r"^\s*import\s+(LeanCert(?:\.[A-Za-z0-9_']+)*)\s*$")
LEANCERT_REF_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])LeanCert(?:\.[A-Za-z0-9_']+)+"
)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|local|scoped|unsafe|partial|nonrec)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|instance|example)\b"
    r"(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?"
)
FKS_CELL_RE = re.compile(r"^\s*⟨")
FKS2_PROBE_SOURCE = (
    "PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4ExtData_11.lean"
)
FKS2_PROBE_PROVIDER = REPO_ROOT / "HexInterval/Experiment/PntFks2ShardData.lean"
FKS2_PROBE_CELLS = 1000
FKS2_FAMILY_PROVIDER = REPO_ROOT / "HexInterval/Experiment/PntFks2FamilyData.lean"
FKS2_FAMILY_DATA = REPO_ROOT / "HexInterval/Experiment"
FKS2_SHARD_COUNTS = tuple([1000] * 13 + [590])
FKS2_DIGEST_RE = re.compile(
    r'⟨(?P<shard>\d+),\s*(?P<cells>\d+),\s*"(?P<digest>[0-9a-f]{64})"⟩'
)
SMALL_PRIME_PROVIDER = (
    REPO_ROOT / "HexIntervalMathlib/Experiment/PntPrimeLogSmall.lean"
)
SMALL_PRIME_FAMILIES = {
    "PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RSPrimeLower.lean": (
        "nth_prime_gt_bound", "p_n_lower_small",
    ),
    "PrimeNumberTheoremAnd/IEANTN/TMEEMT.lean": ("key", "p_n_gt_1"),
}
SMALL_PRIME_SNIPPET_RE = re.compile(
    r"\b(?P<helper>nth_prime_gt_bound|key)\s+"
    r"(?P<n>\d+)\s+(?P<cut>\d+)\s+"
    r"count_prime_(?P<count_cut>\d+)_le_(?P<count>\d+)\s+"
    r"\(by\s+interval_auto\)"
)
DUSART_PROVIDER = REPO_ROOT / "HexInterval/Experiment/PntDusartExp.lean"
DUSART_ROWS = (
    (361, "proposition_5_4a", 0, 29, 1, 4000000000000000000, "upperLe"),
    (406, "proposition_5_4a", 1, 10, 1, 4000000000000000000, "upperLt"),
    (458, "proposition_5_4b", 2, 1283, 100, 370261, "lowerLe"),
    (463, "proposition_5_4b", 3, 1312, 100, 492113, "lowerLe"),
    (468, "proposition_5_4b", 4, 1452, 100, 2010733, "lowerLe"),
    (473, "proposition_5_4b", 5, 1666, 100, 17051707, "lowerLe"),
    (527, "proposition_5_4b", 6, 43, 1, 4000000000000000000, "lowerLe"),
)
DUSART_REPLACEMENT = (
    532, "proposition_5_4b", 22, 1, 117352333, "lowerLe",
)
DUSART_REPLACEMENT_NAME = (
    "Hex.Interval.Experiment.PntExpPoint.one_e9_le_exp_22, weakened by "
    "Hex.IntervalMathlib.PntDusartExpConformance.exp22Lower"
)
DUSART_SNIPPETS = (
    "have : exp (29 : ℝ) ≤ (4e18 : ℝ) := by interval_decide",
    "(lt_log_iff_exp_lt hx_pos).mpr (lt_of_lt_of_le (by interval_decide) hx)",
    "have hexp : (370261 : ℝ) ≤ exp (1283/100) := by interval_decide",
    "have hexp : (492113 : ℝ) ≤ exp (1312/100) := by interval_decide",
    "have hexp : (2010733 : ℝ) ≤ exp (1452/100) := by interval_decide",
    "have hexp : (17051707 : ℝ) ≤ exp (1666/100) := by interval_decide",
    "· have hexp43 : (4e18 : ℝ) ≤ exp 43 := by interval_decide",
    "have hexp22_lb : (117352333 : ℝ) ≤ exp 22 := by interval_decide",
)
DUSART_CONTEXT_SNIPPET = (
    "(lt_log_iff_exp_lt hx_pos).mpr "
    "(lt_of_lt_of_le (by interval_decide) hx)"
)
DUSART_UPPER_RE = re.compile(
    r"^have : exp \((?P<num>\d+) : ℝ\) ≤ "
    r"\((?P<coefficient>\d+)e(?P<exponent>\d+) : ℝ\) := by interval_decide$"
)
DUSART_LOWER_RATIONAL_RE = re.compile(
    r"^have hexp : \((?P<target>\d+) : ℝ\) ≤ exp "
    r"\((?P<num>\d+)/(?P<den>\d+)\) := by interval_decide$"
)
DUSART_LOWER_INTEGER_RE = re.compile(
    r"^(?:· )?have [A-Za-z0-9_]+ : "
    r"\((?P<target>\d+|\d+e\d+) : ℝ\) ≤ exp (?P<num>\d+) "
    r":= by interval_decide$"
)
DUSART_PROVIDER_ROW_RE = re.compile(
    r"⟨(?P<index>\d+),\s*(?P<num>\d+),\s*(?P<den>\d+),\s*"
    r"(?P<target>\d+),\s*\.(?P<relation>upperLe|upperLt|lowerLe),\s*64,\s*12⟩"
)


class InventoryError(RuntimeError):
    pass


@dataclass(frozen=True)
class Source:
    path: str
    text: str
    masked: str
    declarations: tuple[str | None, ...]


def mask_lean(text: str) -> str:
    """Mask comments and string literals, preserving offsets and newlines."""
    out = list(text)
    i = 0
    block_depth = 0
    state = "code"
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                out[i : i + 2] = "  "
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i : i + 2] = "  "
                block_depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            continue

        if state == "string":
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                ch = text[i]
                if ch != "\n":
                    out[i] = " "
                i += 1
                if ch == '"':
                    state = "code"
            continue

        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i : i + 2] = "  "
            block_depth = 1
            i += 2
        elif text[i] == "'":
            end = char_literal_end(text, i)
            if end is None:
                i += 1
            else:
                for pos in range(i, end):
                    out[pos] = " "
                i = end
        elif text[i] == '"':
            out[i] = " "
            state = "string"
            i += 1
        else:
            i += 1
    if block_depth:
        raise InventoryError("unterminated Lean block comment")
    if state == "string":
        raise InventoryError("unterminated Lean string literal")
    return "".join(out)


def char_literal_end(text: str, start: int) -> int | None:
    """Return the end offset of a syntactic Lean character literal, if any."""
    if start > 0 and (text[start - 1].isalnum() or text[start - 1] in "_'"):
        return None
    if start + 2 < len(text) and text[start + 1] not in {"\\", "\n"} \
            and text[start + 2] == "'":
        return start + 3
    if start + 3 < len(text) and text[start + 1] == "\\" \
            and text[start + 2] != "\n":
        # The byte immediately after the backslash is part of the escape.  In
        # particular, it is not the closing delimiter in the literal '\\''.
        end = start + 3
        while end < min(len(text), start + 16) and text[end] != "\n":
            if text[end] == "'":
                return end + 1
            end += 1
    return None


def declaration_map(masked: str) -> tuple[str | None, ...]:
    current: str | None = None
    result: list[str | None] = []
    for line_no, line in enumerate(masked.splitlines(), 1):
        match = DECL_RE.match(line)
        if match:
            kind = match.group("kind")
            name = match.group("name")
            current = name if name and kind != "example" else f"{kind}@{line_no}"
        result.append(current)
    return tuple(result)


def line_col(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    start = text.rfind("\n", 0, offset) + 1
    return line, offset - start + 1


def snippet(text: str, line: int) -> str:
    lines = text.splitlines()
    return lines[line - 1].strip() if 0 < line <= len(lines) else ""


def git_head(root: Path) -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if proc.returncode != 0:
        raise InventoryError(f"source is not a git checkout: {root}")
    return proc.stdout.strip()


def load_pins(root: Path) -> dict[str, str]:
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = {entry["name"]: entry["rev"] for entry in manifest["packages"]}
    return {
        "pnt": git_head(root),
        "leancert": packages.get("leancert", ""),
        "mathlib": packages.get("mathlib", ""),
        "lean_toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
    }


def require_pins(pins: dict[str, str]) -> None:
    expected = {
        "pnt": PNT_COMMIT,
        "leancert": LEANCERT_COMMIT,
        "mathlib": MATHLIB_COMMIT,
        "lean_toolchain": LEAN_TOOLCHAIN,
    }
    if pins != expected:
        raise InventoryError(f"upstream pins differ: expected {expected}, got {pins}")


def load_sources(root: Path) -> list[Source]:
    proc = subprocess.run(
        ["git", "ls-files", "--", "*.lean"], cwd=root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if proc.returncode != 0:
        raise InventoryError(f"cannot list pinned Lean sources: {proc.stderr.strip()}")
    paths = [root / line for line in proc.stdout.splitlines() if line]
    if not paths:
        raise InventoryError(f"no tracked Lean sources in {root}")
    sources: list[Source] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        masked = mask_lean(text)
        sources.append(Source(
            path=path.relative_to(root).as_posix(),
            text=text,
            masked=masked,
            declarations=declaration_map(masked),
        ))
    return sources


def fks_cell_rows(text: str) -> list[str]:
    """Return whitespace-insensitive source cell tuples, without trailing commas."""
    return [
        re.sub(r"\s+", "", line).removesuffix(",")
        for line in mask_lean(text).splitlines()
        if FKS_CELL_RE.match(line)
    ]


def require_fks2_shard_match(source_text: str, provider_text: str) -> None:
    """Require the retained provider table to equal pinned shard 11."""
    source_rows = fks_cell_rows(source_text)
    provider_rows = fks_cell_rows(provider_text)
    if len(source_rows) < FKS2_PROBE_CELLS:
        raise InventoryError(
            f"pinned FKS2 shard 11 has only {len(source_rows)} cells"
        )
    if len(provider_rows) != FKS2_PROBE_CELLS:
        raise InventoryError(
            "local FKS2 shard must contain exactly "
            f"{FKS2_PROBE_CELLS} cells, found {len(provider_rows)}"
        )
    for index, (source_row, provider_row) in enumerate(
            zip(source_rows[:FKS2_PROBE_CELLS], provider_rows, strict=True)):
        if source_row != provider_row:
            raise InventoryError(
                f"local FKS2 shard differs from pinned shard 11 at cell {index}"
            )


def require_fks2_probe_match(source_root: Path) -> None:
    source_path = source_root / FKS2_PROBE_SOURCE
    require_fks2_shard_match(
        source_path.read_text(encoding="utf-8"),
        FKS2_PROBE_PROVIDER.read_text(encoding="utf-8"),
    )


def fks_rows_digest(rows: list[str]) -> str:
    """Hash the exact normalized tuple stream used by the generated provider."""
    return hashlib.sha256(("\n".join(rows) + "\n").encode()).hexdigest()


def require_fks2_family_match(source_root: Path) -> None:
    """Require every generated shard and digest to match the pinned family."""
    records_text = FKS2_FAMILY_PROVIDER.read_text(encoding="utf-8")
    records = {
        int(match.group("shard")): (
            int(match.group("cells")), match.group("digest")
        )
        for match in FKS2_DIGEST_RE.finditer(records_text)
    }
    if len(records) != len(FKS2_SHARD_COUNTS):
        raise InventoryError(
            f"local FKS2 family must record 14 shard digests, found {len(records)}"
        )
    for shard, expected_count in enumerate(FKS2_SHARD_COUNTS):
        source_path = source_root / (
            "PrimeNumberTheoremAnd/IEANTN/FKS2Tables/"
            f"Table4ExtData_{shard:02}.lean"
        )
        provider_path = (
            FKS2_PROBE_PROVIDER if shard == 11 else
            FKS2_FAMILY_DATA / f"PntFks2FamilyData{shard:02}.lean"
        )
        source_rows = fks_cell_rows(source_path.read_text(encoding="utf-8"))
        provider_rows = fks_cell_rows(provider_path.read_text(encoding="utf-8"))
        if len(source_rows) != expected_count or len(provider_rows) != expected_count:
            raise InventoryError(
                f"FKS2 shard {shard:02} count mismatch: source {len(source_rows)}, "
                f"provider {len(provider_rows)}, expected {expected_count}"
            )
        for index, (source_row, provider_row) in enumerate(
                zip(source_rows, provider_rows, strict=True)):
            if source_row != provider_row:
                raise InventoryError(
                    f"local FKS2 family differs from pinned shard {shard:02} "
                    f"at cell {index}"
                )
        recorded_count, recorded_digest = records[shard]
        expected_digest = fks_rows_digest(source_rows)
        if recorded_count != expected_count or recorded_digest != expected_digest:
            raise InventoryError(
                f"local FKS2 shard {shard:02} digest record does not match source"
            )


def small_prime_provider_rows(provider_text: str) -> tuple[list[tuple[int, int]],
                                                            list[tuple[int, int]]]:
    """Read the literal ``sourceRows`` and ``sourceCut`` tables."""
    rows_match = re.search(
        r"\bdef\s+sourceRows\s*:\s*Array\s*\(Nat\s*×\s*Nat\)\s*:=\s*#\["
        r"(?P<body>.*?)\]",
        provider_text,
        re.DOTALL,
    )
    if rows_match is None:
        raise InventoryError("cannot locate the local small-prime sourceRows table")
    row_pairs = [
        (int(match.group(1)), int(match.group(2)))
        for match in re.finditer(r"\((\d+)\s*,\s*(\d+)\)", rows_match.group("body"))
    ]

    cut_match = re.search(
        r"\bdef\s+sourceCut\s*:\s*Nat\s*→\s*Nat(?P<body>.*?)"
        r"\bdef\s+sourceRows\b",
        provider_text,
        re.DOTALL,
    )
    if cut_match is None:
        raise InventoryError("cannot locate the local small-prime sourceCut table")
    cut_pairs = [
        (int(match.group(1)), int(match.group(2)))
        for match in re.finditer(
            r"^\s*\|\s*(\d+)\s*=>\s*(\d+)\s*$",
            cut_match.group("body"), re.MULTILINE,
        )
    ]
    if not re.search(
        r"^\s*\|\s*_\s*=>\s*0\s*$", cut_match.group("body"), re.MULTILINE,
    ):
        raise InventoryError("local small-prime sourceCut lacks its zero default")
    return row_pairs, cut_pairs


def require_small_prime_log_match(
    records: list[dict[str, Any]], provider_text: str | None = None,
) -> None:
    """Correlate all sixty committed snippets with both local source tables."""
    families: dict[str, list[tuple[int, int]]] = {
        path: [] for path in SMALL_PRIME_FAMILIES
    }
    for record in records:
        path = record.get("path")
        if path not in SMALL_PRIME_FAMILIES or record.get("kind") != "tactic-occurrence" \
                or record.get("tactic") != "interval_auto" or not record.get("actual"):
            continue
        helper, declaration = SMALL_PRIME_FAMILIES[path]
        if record.get("declaration") != declaration:
            raise InventoryError(
                f"small-prime source evidence in {path} has declaration "
                f"{record.get('declaration')!r}, expected {declaration!r}"
            )
        match = SMALL_PRIME_SNIPPET_RE.search(record.get("snippet", ""))
        if match is None:
            raise InventoryError(
                f"cannot parse small-prime source snippet at {path}:{record.get('line')}"
            )
        n = int(match.group("n"))
        cut = int(match.group("cut"))
        if match.group("helper") != helper:
            raise InventoryError(f"wrong small-prime helper at {path}:{record.get('line')}")
        if int(match.group("count_cut")) != cut or int(match.group("count")) != n - 1:
            raise InventoryError(
                f"small-prime counting evidence disagrees at {path}:{record.get('line')}"
            )
        families[path].append((n, cut))

    expected_coordinates: list[tuple[int, int]] | None = None
    for path, coordinates in families.items():
        if len(coordinates) != 30:
            raise InventoryError(
                f"small-prime family {path} must contain 30 coordinates, "
                f"found {len(coordinates)}"
            )
        if len(set(coordinates)) != len(coordinates):
            raise InventoryError(f"duplicate small-prime coordinate in {path}")
        if expected_coordinates is None:
            expected_coordinates = coordinates
        elif coordinates != expected_coordinates:
            raise InventoryError("the two small-prime theorem families have different coordinates")

    assert expected_coordinates is not None
    if provider_text is None:
        provider_text = SMALL_PRIME_PROVIDER.read_text(encoding="utf-8")
    source_rows, source_cut = small_prime_provider_rows(provider_text)
    for name, coordinates in (("sourceRows", source_rows), ("sourceCut", source_cut)):
        if len(set(coordinates)) != len(coordinates):
            raise InventoryError(f"duplicate coordinate in local small-prime {name}")
        if coordinates != expected_coordinates:
            raise InventoryError(
                f"local small-prime {name} differs from the committed source snippets"
            )


def require_dusart_exp_match(
    records: list[dict[str, Any]], provider_text: str | None = None,
) -> None:
    """Tie all eight committed Dusart sites to seven rows plus one replacement."""
    source_records = [
        row for row in records
        if row.get("kind") == "tactic-occurrence"
        and row.get("actual")
        and row.get("path") == "PrimeNumberTheoremAnd/IEANTN/Dusart.lean"
    ]
    expected_values = tuple(row[3:] for row in DUSART_ROWS) + (DUSART_REPLACEMENT[2:],)
    expected_sites = tuple((line, declaration) for line, declaration, *_ in DUSART_ROWS) + (
        DUSART_REPLACEMENT[:2],
    )
    observed = tuple((row.get("line"), row.get("declaration")) for row in source_records)
    if len(set(observed)) != len(observed):
        raise InventoryError("duplicate Dusart exponential source coordinate")
    if observed != expected_sites:
        raise InventoryError(
            f"Dusart exponential sites differ: {observed} != {expected_sites}"
        )
    if provider_text is None:
        provider_text = DUSART_PROVIDER.read_text(encoding="utf-8")
    provider_rows = tuple(
        (int(match.group("index")), int(match.group("num")),
         int(match.group("den")), int(match.group("target")),
         match.group("relation"))
        for match in DUSART_PROVIDER_ROW_RE.finditer(provider_text)
    )
    parsed_values = tuple(_parse_dusart_snippet(row.get("snippet", "")) for row in source_records)
    if parsed_values != expected_values:
        raise InventoryError(
            f"Dusart exponential snippets differ: {parsed_values} != {expected_values}"
        )
    replacement = source_records[-1].get("migration", {})
    if replacement.get("status") != "replaced-by-stronger-result" or \
            replacement.get("replacement") != DUSART_REPLACEMENT_NAME:
        raise InventoryError("Dusart exp 22 site lacks its explicit stronger replacement")
    expected_rows = tuple(row[2:] for row in DUSART_ROWS)
    if provider_rows != expected_rows:
        raise InventoryError(
            f"local Dusart sourceRows differ: {provider_rows} != {expected_rows}"
        )


def _scientific_value(value: str) -> int:
    if "e" not in value:
        return int(value)
    coefficient, exponent = value.split("e", maxsplit=1)
    return int(coefficient) * 10 ** int(exponent)


def _parse_dusart_snippet(snippet: str) -> tuple[int, int, int, str]:
    # This invocation text contains no numeric goal. Byte-pin its exact context
    # and correlate it with the separately audited expected provider row.
    if snippet == DUSART_CONTEXT_SNIPPET:
        return (10, 1, 4000000000000000000, "upperLt")
    match = DUSART_UPPER_RE.fullmatch(snippet)
    if match:
        target = int(match.group("coefficient")) * 10 ** int(match.group("exponent"))
        return (int(match.group("num")), 1, target, "upperLe")
    match = DUSART_LOWER_RATIONAL_RE.fullmatch(snippet)
    if match:
        return (int(match.group("num")), int(match.group("den")),
                int(match.group("target")), "lowerLe")
    match = DUSART_LOWER_INTEGER_RE.fullmatch(snippet)
    if match:
        return (int(match.group("num")), 1,
                _scientific_value(match.group("target")), "lowerLe")
    raise InventoryError(f"unrecognized Dusart exponential snippet: {snippet!r}")


def source_digest(sources: Iterable[Source]) -> str:
    digest = hashlib.sha256()
    for source in sources:
        digest.update(source.path.encode())
        digest.update(b"\0")
        digest.update(source.text.encode())
        digest.update(b"\0")
    return digest.hexdigest()


def classification() -> dict[str, str]:
    return {
        "status": "pending",
        "note": "D8 migration decision not yet assigned",
    }


def inventory_only() -> dict[str, str]:
    return {
        "status": "inventory-only",
        "note": "lexical audit evidence subsumed by imported-interface classification",
    }


def occurrence_record(source: Source, token: str, match: re.Match[str],
                      actual: bool) -> dict[str, Any]:
    line, column = line_col(source.text, match.start())
    declaration = (
        source.declarations[line - 1]
        if actual and line <= len(source.declarations) else None
    )
    return {
        "kind": "tactic-occurrence",
        "tactic": token,
        "actual": actual,
        "path": source.path,
        "line": line,
        "column": column,
        "declaration": declaration,
        "snippet": snippet(source.text, line),
        "migration": classification() if actual else {"status": "not-a-call"},
    }


def tactic_records(sources: Iterable[Source]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for source in sources:
        for token in ("interval_decide", "interval_auto"):
            actual_offsets = {m.start() for m in TOKEN_RE[token].finditer(source.masked)}
            for match in TOKEN_RE[token].finditer(source.text):
                records.append(occurrence_record(
                    source, token, match, match.start() in actual_offsets,
                ))
    return records


def import_records(sources: Iterable[Source]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for source in sources:
        for line_no, line in enumerate(source.masked.splitlines(), 1):
            match = IMPORT_RE.match(line)
            if match:
                records.append({
                    "kind": "leancert-import",
                    "module": match.group(1),
                    "path": source.path,
                    "line": line_no,
                    "migration": classification(),
                })
    return records


def dependency_records(imports: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Record audited public interfaces without pretending to name-resolve Lean.

    Qualified symbol occurrences are recorded separately.  Uses after ``open``
    cannot be resolved reliably by a lexer, so the durable obligation here is
    the imported interface family and its load-bearing role.  Migration work
    later classifies the exact replacement theorem(s).
    """
    imported = {row["module"] for row in imports}
    expected = set(DEPENDENCY_INTERFACES)
    if imported != expected:
        raise InventoryError(
            f"LeanCert import surface drifted: expected {sorted(expected)}, "
            f"got {sorted(imported)}"
        )
    result = []
    for module, (role, workload) in DEPENDENCY_INTERFACES.items():
        sites = [
            {"path": row["path"], "line": row["line"]}
            for row in imports if row["module"] == module
        ]
        result.append({
            "kind": "dependency-interface",
            "module": module,
            "role": role,
            "workload": workload,
            "import_sites": sites,
            "migration": classification(),
        })
    return result


def reference_records(sources: Iterable[Source], *, audited: bool = True) \
        -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for source in sources:
        import_lines = {
            index for index, line in enumerate(source.masked.splitlines(), 1)
            if IMPORT_RE.match(line)
        }
        for match in LEANCERT_REF_RE.finditer(source.masked):
            line, column = line_col(source.masked, match.start())
            if line in import_lines:
                continue
            try:
                provenance = reference_interfaces(match.group(0))
            except InventoryError:
                if audited:
                    raise
                provenance = []
            records.append({
                "kind": "leancert-reference",
                "symbol": match.group(0),
                "path": source.path,
                "line": line,
                "column": column,
                "declaration": source.declarations[line - 1],
                "interface_provenance": provenance,
                "migration": inventory_only(),
            })
    return records


def reference_interfaces(symbol: str) -> list[str]:
    matches = [
        (prefix, interfaces) for prefix, interfaces in REFERENCE_PROVENANCE.items()
        if symbol == prefix or symbol.startswith(prefix + ".")
    ]
    if not matches:
        raise InventoryError(f"qualified reference lacks interface provenance: {symbol}")
    _, interfaces = max(matches, key=lambda item: len(item[0]))
    unknown = set(interfaces) - set(DEPENDENCY_INTERFACES)
    if unknown:
        raise InventoryError(f"reference provenance names unknown interfaces: {sorted(unknown)}")
    return list(interfaces)


def native_records(sources: Iterable[Source]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for source in sources:
        for match in TOKEN_RE["native_decide"].finditer(source.masked):
            line, column = line_col(source.masked, match.start())
            records.append({
                "kind": "native-decide-occurrence",
                "mechanism": "native_decide",
                "path": source.path,
                "line": line,
                "column": column,
                "declaration": source.declarations[line - 1],
                "migration": classification(),
            })
    return records


def table_rows(masked: str, definition: str) -> list[str]:
    """Return the top-level tuple rows of one masked Lean list definition."""
    marker = re.compile(
        rf"\bnoncomputable\s+def\s+{re.escape(definition)}(?![A-Za-z0-9_'])"
    )
    matches = list(marker.finditer(masked))
    if len(matches) != 1:
        raise InventoryError(
            f"expected one pinned {definition} list definition, found {len(matches)}"
        )
    try:
        start = matches[0].start()
        assign = masked.index(":=", matches[0].end())
        opening = masked.index("[", assign + 2)
    except ValueError as exc:
        raise InventoryError(f"cannot locate the pinned {definition} list") from exc

    bracket_depth = 1
    paren_depth = 0
    row_start: int | None = None
    rows: list[str] = []
    index = opening + 1
    while index < len(masked) and bracket_depth:
        char = masked[index]
        if char == "[":
            bracket_depth += 1
        elif char == "]":
            bracket_depth -= 1
            if bracket_depth == 0:
                if paren_depth or row_start is not None:
                    raise InventoryError(f"unterminated tuple in {definition}")
                break
        elif bracket_depth == 1:
            if char == "(":
                if paren_depth == 0:
                    row_start = index
                paren_depth += 1
            elif char == ")":
                if paren_depth == 0:
                    raise InventoryError(f"unmatched ')' in {definition}")
                paren_depth -= 1
                if paren_depth == 0:
                    assert row_start is not None
                    rows.append(masked[row_start:index + 1])
                    row_start = None
        index += 1
    if bracket_depth:
        raise InventoryError(f"unterminated list in {definition}")
    return rows


def batch_records(sources: Iterable[Source],
                  tactic_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    source_list = list(sources)
    by_path = {source.path: source for source in source_list}
    shards: list[dict[str, Any]] = []
    for source in sorted(source_list, key=lambda item: item.path):
        if not re.search(r"/FKS2Tables/Table4ExtData_[^/]*\.lean$", source.path):
            continue
        count = sum(1 for line in source.masked.splitlines() if FKS_CELL_RE.match(line))
        shards.append({"path": source.path, "cells": count})

    table10_sites = [
        row for row in tactic_rows
        if row["tactic"] == "interval_decide" and row["actual"]
        and "/BKLNW/BKLNW_table10_rows" in row["path"]
    ]
    table10_targets = [
        row for row in table10_sites
        if str(row.get("declaration", "")).startswith("table_10_")
    ]
    table10_a2 = [
        row for row in table10_sites
        if str(row.get("declaration", "")).startswith("row")
        and str(row.get("declaration", "")).endswith("_a2_le")
    ]
    if len(table10_targets) + len(table10_a2) != len(table10_sites):
        raise InventoryError("unclassified BKLNW Table 10 source check site")
    bklnw_all = [
        row for row in tactic_rows
        if row["tactic"] == "interval_decide" and row["actual"]
        and "/BKLNW/" in row["path"]
    ]
    table12_path = "PrimeNumberTheoremAnd/IEANTN/BKLNW/BKLNW_tables.lean"
    try:
        table12_masked = by_path[table12_path].masked
    except KeyError as exc:
        raise InventoryError("pinned BKLNW Table 12 source is not tracked") from exc
    table12_rows = table_rows(table12_masked, "table_12")
    table12_log_rows = sum(row.lstrip().startswith("(Real.log") for row in table12_rows)
    table12_ordinary_rows = len(table12_rows) - table12_log_rows
    return [
        {
            "kind": "generated-family",
            "family": "fks2-table4ext",
            "source": "PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4ExtData_*.lean",
            "shards": shards,
            "cells": sum(item["cells"] for item in shards),
            "migration": classification(),
        },
        {
            "kind": "generated-family",
            "family": "bklnw-table10-source-sites",
            "source": "PrimeNumberTheoremAnd/IEANTN/BKLNW/BKLNW_table10_rows*.lean",
            "target_check_sites": len(table10_targets),
            "supporting_a2_check_sites": len(table10_a2),
            "declarations": [
                {"path": path, "declaration": declaration}
                for path, declaration in sorted({
                    (row["path"], row["declaration"])
                    for row in table10_sites if row["declaration"]
                })
            ],
            "migration": classification(),
        },
        {
            "kind": "generated-family",
            "family": "bklnw-all-source-checks",
            "source": "PrimeNumberTheoremAnd/IEANTN/BKLNW/*.lean",
            "actual_interval_decide": len(bklnw_all),
            "declarations": [
                {"path": path, "declaration": declaration}
                for path, declaration in sorted({
                    (row["path"], row["declaration"])
                    for row in bklnw_all if row["declaration"]
                })
            ],
            "migration": classification(),
        },
        {
            "kind": "generated-family",
            "family": "bklnw-table12-cells",
            "source": table12_path,
            "check_declaration": "table_12_check",
            "rows": len(table12_rows),
            "ordinary_rows": table12_ordinary_rows,
            "logarithmic_rows": table12_log_rows,
            "checks_per_row": 5,
            "expanded_checks": (table12_ordinary_rows + table12_log_rows) * 5,
            "annotation_provenance": (
                "pinned BKLNW_tables.lean row count plus reviewed five-column "
                "expansion; false rows from PNT+ PR #1405"
            ),
            "false_original_boundary_rows": [
                "log(5e10)", "25", "log(3.2e13)", "32",
            ],
            "migration": classification(),
        },
    ]


def record_sort_key(record: dict[str, Any]) -> tuple[Any, ...]:
    return (
        record["kind"], record.get("path", ""), record.get("line", -1),
        record.get("column", -1), record.get("tactic", ""),
        record.get("symbol", ""), record.get("module", ""),
        record.get("family", ""),
        json.dumps(
            {name: value for name, value in record.items() if name != "migration"},
            sort_keys=True, separators=(",", ":"),
        ),
    )


def record_digest(records: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for record in records:
        digest.update(json.dumps(record, sort_keys=True, separators=(",", ":")).encode())
        digest.update(b"\n")
    return digest.hexdigest()


def audit_record_digest(records: list[dict[str, Any]]) -> str:
    return record_digest(audit_records(records))


def audit_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    result = []
    for record in records:
        audit_record = dict(record)
        audit_record.pop("migration", None)
        result.append(audit_record)
    return result


def carry_migrations(
    previous: list[dict[str, Any]], generated: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], int, int]:
    def key(record: dict[str, Any]) -> str:
        return json.dumps(
            {name: value for name, value in record.items() if name != "migration"},
            sort_keys=True, separators=(",", ":"),
        )

    previous_by_key: dict[str, dict[str, Any]] = {}
    for record in previous:
        identity = key(record)
        if identity in previous_by_key:
            raise InventoryError("previous inventory has duplicate audit-record identity")
        previous_by_key[identity] = record

    carried = 0
    result = []
    generated_keys = set()
    for record in generated:
        identity = key(record)
        generated_keys.add(identity)
        old = previous_by_key.get(identity)
        if old is not None:
            if record.get("migration", {}).get("status") \
                    not in {"not-a-call", "inventory-only"}:
                record = dict(record)
                record["migration"] = old["migration"]
                carried += 1
        result.append(record)

    removed = [
        record for identity, record in previous_by_key.items()
        if identity not in generated_keys
    ]
    classified_removed = [
        record for record in removed
        if record.get("migration", {}).get("status")
        not in {"pending", "not-a-call", "inventory-only"}
    ]
    if classified_removed:
        raise InventoryError(
            f"refresh would discard {len(classified_removed)} classified records; "
            "reconcile them explicitly before refreshing"
        )
    return result, carried, len(removed)


def summarize(records: list[dict[str, Any]]) -> dict[str, int]:
    tactic = [row for row in records if row["kind"] == "tactic-occurrence"]
    fks = next((row for row in records
                if row["kind"] == "generated-family" and row["family"] == "fks2-table4ext"), None)
    table10 = next((row for row in records
                    if row["kind"] == "generated-family"
                    and row["family"] == "bklnw-table10-source-sites"), None)
    table12 = next((row for row in records
                    if row["kind"] == "generated-family"
                    and row["family"] == "bklnw-table12-cells"), None)
    return {
        "interval_decide_actual": sum(
            row["tactic"] == "interval_decide" and row["actual"] for row in tactic),
        "interval_decide_textual": sum(row["tactic"] == "interval_decide" for row in tactic),
        "interval_auto_actual": sum(
            row["tactic"] == "interval_auto" and row["actual"] for row in tactic),
        "interval_auto_textual": sum(row["tactic"] == "interval_auto" for row in tactic),
        "leancert_import": sum(row["kind"] == "leancert-import" for row in records),
        "leancert_reference": sum(row["kind"] == "leancert-reference" for row in records),
        "dependency_interface": sum(
            row["kind"] == "dependency-interface" for row in records),
        "native_decide_actual": sum(
            row["kind"] == "native-decide-occurrence" for row in records),
        "fks2_cells": fks["cells"] if fks else 0,
        "fks2_shards": len(fks["shards"]) if fks else 0,
        "bklnw_table10_target_sites": table10["target_check_sites"] if table10 else 0,
        "bklnw_table10_a2_sites": table10["supporting_a2_check_sites"] if table10 else 0,
        "bklnw_table12_checks": table12["expanded_checks"] if table12 else 0,
        "bklnw_table12_ordinary_rows": table12["ordinary_rows"] if table12 else 0,
        "bklnw_table12_logarithmic_rows": (
            table12["logarithmic_rows"] if table12 else 0
        ),
        "records": len(records),
    }


def require_workload_partitions(records: list[dict[str, Any]]) -> None:
    tactics = [row for row in records if row["kind"] == "tactic-occurrence"]
    decide = [row for row in tactics if row["tactic"] == "interval_decide"]

    def partition(predicate: Any) -> tuple[int, int]:
        rows = [row for row in decide if predicate(row)]
        return len(rows), sum(row["actual"] for row in rows)

    log_tables = partition(lambda row: row["path"].endswith("/LogTables.lean"))
    bklnw = partition(lambda row: "/BKLNW/" in row["path"])
    remaining = partition(
        lambda row: not row["path"].endswith("/LogTables.lean")
        and "/BKLNW/" not in row["path"]
    )
    expected = {
        "LogTables": (141, 136),
        "BKLNW": (132, 128),
        "remaining": (17, 16),
    }
    actual = {"LogTables": log_tables, "BKLNW": bklnw, "remaining": remaining}
    if actual != expected:
        raise InventoryError(f"PNT+ interval_decide partitions drifted: {actual} != {expected}")
    bklnw_paths = {row["path"] for row in decide if "/BKLNW/" in row["path"]}
    log_paths = {row["path"] for row in decide if row["path"].endswith("/LogTables.lean")}
    if len(bklnw_paths) != 9:
        raise InventoryError(
            f"BKLNW interval_decide file count drifted: expected 9, got {len(bklnw_paths)}"
        )
    if log_paths != {"PrimeNumberTheoremAnd/IEANTN/LogTables.lean"}:
        raise InventoryError(f"LogTables interval_decide path drifted: {sorted(log_paths)}")

    paths = {row["path"] for row in decide}
    if len(paths) != 15:
        raise InventoryError(f"interval_decide file count drifted: expected 15, got {len(paths)}")
    remaining_paths = {
        "PrimeNumberTheoremAnd/IEANTN/Dusart.lean",
        "PrimeNumberTheoremAnd/IEANTN/FKS2.lean",
        "PrimeNumberTheoremAnd/IEANTN/FKS2Cor23Cor14Tail.lean",
        "PrimeNumberTheoremAnd/IEANTN/FKS2Floor/Cor22Floor.lean",
        "PrimeNumberTheoremAnd/IEANTN/Goldbach.lean",
    }
    actual_remaining_paths = {
        row["path"] for row in decide
        if "/BKLNW/" not in row["path"]
        and not row["path"].endswith("/LogTables.lean")
    }
    if actual_remaining_paths != remaining_paths:
        raise InventoryError(
            "remaining interval_decide file set drifted: "
            f"{sorted(actual_remaining_paths)} != {sorted(remaining_paths)}"
        )

    interval_auto = [row for row in tactics if row["tactic"] == "interval_auto"]
    actual_auto = [row for row in interval_auto if row["actual"]]
    auto_counts = Counter(row["path"] for row in actual_auto)
    expected_auto_counts = Counter({
        "PrimeNumberTheoremAnd/IEANTN/TMEEMT.lean": 30,
        "PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RSPrimeLower.lean": 30,
    })
    if auto_counts != expected_auto_counts:
        raise InventoryError(
            f"interval_auto executable file partition drifted: {auto_counts} "
            f"!= {expected_auto_counts}"
        )


def generate(root: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    pins = load_pins(root)
    require_pins(pins)
    sources = load_sources(root)
    if len(sources) != PNT_LEAN_SOURCE_FILES:
        raise InventoryError(
            f"pinned Lean-source file count drifted: expected {PNT_LEAN_SOURCE_FILES}, "
            f"got {len(sources)}"
        )
    tree_digest = source_digest(sources)
    if tree_digest != PNT_LEAN_SOURCE_DIGEST:
        raise InventoryError(
            "pinned checkout contents differ from the audited Lean-source digest: "
            f"expected {PNT_LEAN_SOURCE_DIGEST}, got {tree_digest}"
        )
    tactics = tactic_records(sources)
    imports = import_records(sources)
    records = tactics + imports + dependency_records(imports) + reference_records(sources)
    records += native_records(sources) + batch_records(sources, tactics)
    records.sort(key=record_sort_key)
    counts = summarize(records)
    require_workload_partitions(records)
    for name, expected in EXPECTED.items():
        if counts.get(name) != expected:
            raise InventoryError(
                f"upstream {name} drifted: expected {expected}, got {counts.get(name)}"
            )
    meta = {
        "kind": "meta",
        "format": FORMAT_VERSION,
        "pins": pins,
        "lean_source_digest": tree_digest,
        "lean_source_files": len(sources),
        "audit_record_digest": audit_record_digest(records),
        "record_digest": record_digest(records),
        "counts": counts,
    }
    return meta, records


def inspect_source(root: Path) -> dict[str, Any]:
    """Report observed pin-bump inputs without accepting them as audited."""
    pins = load_pins(root)
    sources = load_sources(root)
    tactics = tactic_records(sources)
    imports = import_records(sources)
    references = reference_records(sources, audited=False)
    native = native_records(sources)
    batch_error = None
    try:
        batches = batch_records(sources, tactics)
    except InventoryError as exc:
        batches = []
        batch_error = str(exc)
    provisional = tactics + imports + references + native + batches
    provisional.sort(key=record_sort_key)
    counts = summarize(provisional)
    counts["dependency_interface"] = len({row["module"] for row in imports})
    counts.pop("records", None)
    return {
        "pins": pins,
        "lean_source_files": len(sources),
        "lean_source_digest": source_digest(sources),
        "observed_counts": counts,
        "leancert_import_modules": sorted({row["module"] for row in imports}),
        "generated_families": [
            {key: value for key, value in row.items() if key != "migration"}
            for row in batches
        ],
        "generated_family_error": batch_error,
        "warning": (
            "inspection is not an accepted audit; review interfaces, workload "
            "partitions, constants, SPEC, and fixture before --refresh"
        ),
    }


def write_inventory(path: Path, meta: dict[str, Any], records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as stream:
        for row in [meta, *records]:
            stream.write(json.dumps(row, sort_keys=True, separators=(",", ":")))
            stream.write("\n")


def read_inventory(path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as stream:
        for line_no, line in enumerate(stream, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise InventoryError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(row, dict):
                raise InventoryError(f"{path}:{line_no}: inventory row must be an object")
            rows.append(row)
    if not rows or rows[0].get("kind") != "meta":
        raise InventoryError("inventory must start with one meta row")
    return rows[0], rows[1:]


def migration_statuses(record: dict[str, Any]) -> Iterable[str]:
    migration = record.get("migration")
    if migration and migration.get("status") not in {"not-a-call", "inventory-only"}:
        yield migration.get("status", "")


def require_migrations(records: list[dict[str, Any]]) -> None:
    for index, record in enumerate(records):
        migration = record.get("migration")
        if not isinstance(migration, dict):
            raise InventoryError(f"record {index}: migration must be an object")
        status = migration.get("status")
        raw_tactic = record.get("kind") == "tactic-occurrence" and not record.get("actual")
        audit_reference = record.get("kind") == "leancert-reference"
        if raw_tactic:
            if status != "not-a-call":
                raise InventoryError(
                    f"record {index}: non-executable textual occurrence must be not-a-call"
                )
        elif audit_reference:
            if status != "inventory-only":
                raise InventoryError(
                    f"record {index}: lexical reference must be inventory-only"
                )
            expected_provenance = reference_interfaces(record.get("symbol", ""))
            if record.get("interface_provenance") != expected_provenance:
                raise InventoryError(
                    f"record {index}: lexical reference provenance drifted"
                )
        elif status not in CLASSIFICATIONS:
            raise InventoryError(
                f"record {index}: executable/imported record has invalid migration {status!r}"
            )
        else:
            note = migration.get("note")
            if not isinstance(note, str) or not note.strip():
                raise InventoryError(f"record {index}: migration requires a nonempty note")
            evidence = migration.get("evidence")
            if evidence is not None:
                if not isinstance(evidence, list) or not evidence or not all(
                    isinstance(item, str) and item.strip() for item in evidence
                ):
                    raise InventoryError(
                        f"record {index}: evidence must be a nonempty string list"
                    )
                for item in evidence:
                    reference = item.split(":", 1)[0]
                    if "/" not in reference:
                        continue
                    path = Path(reference)
                    if path.is_absolute() or ".." in path.parts \
                            or not (REPO_ROOT / path).is_file():
                        raise InventoryError(
                            f"record {index}: evidence path does not exist: {reference}"
                        )
            if status == "pending":
                continue
            if not isinstance(evidence, list) or not evidence or not all(
                isinstance(item, str) and item.strip() for item in evidence
            ):
                raise InventoryError(
                    f"record {index}: {status} requires nonempty evidence entries"
                )
            if status == "accepted-after-rewrite":
                if not isinstance(migration.get("rewrite"), str) \
                        or not migration["rewrite"].strip():
                    raise InventoryError(
                        f"record {index}: accepted-after-rewrite requires rewrite and evidence"
                    )
            elif status == "replaced-by-stronger-result":
                replacement = migration.get("replacement")
                if not isinstance(replacement, str) or not replacement.strip():
                    raise InventoryError(
                        f"record {index}: replacement theorem/result is required"
                    )
            elif status == "retained-other-dependency":
                dependency = migration.get("dependency")
                if not isinstance(dependency, str) or not dependency.strip():
                    raise InventoryError(
                        f"record {index}: retained dependency is required"
                    )


def validate_inventory(
    meta: dict[str, Any], records: list[dict[str, Any]],
    require_classified: bool, require_record_digest: bool = True,
) -> None:
    if meta.get("format") != FORMAT_VERSION:
        raise InventoryError(f"unsupported inventory format {meta.get('format')}")
    require_pins(meta.get("pins", {}))
    if meta.get("lean_source_digest") != PNT_LEAN_SOURCE_DIGEST:
        raise InventoryError("inventory Lean-source digest does not match the pinned PNT+ tree")
    if meta.get("lean_source_files") != PNT_LEAN_SOURCE_FILES:
        raise InventoryError("inventory Lean-source file count does not match the pinned PNT+ tree")
    if meta.get("audit_record_digest") != PNT_AUDIT_RECORD_DIGEST:
        raise InventoryError(
            "inventory audit-record digest does not match the pinned audit surface: "
            f"expected {PNT_AUDIT_RECORD_DIGEST}, got {meta.get('audit_record_digest')}"
        )
    if records != sorted(records, key=record_sort_key):
        raise InventoryError("inventory records are not in canonical order")
    if require_record_digest and meta.get("record_digest") != record_digest(records):
        raise InventoryError("inventory record digest does not match contents")
    if meta.get("audit_record_digest") != audit_record_digest(records):
        raise InventoryError("inventory audit-record digest does not match record contents")
    require_migrations(records)
    counts = summarize(records)
    require_workload_partitions(records)
    require_small_prime_log_match(records)
    require_dusart_exp_match(records)
    if meta.get("counts") != counts:
        raise InventoryError(f"inventory counts disagree: {meta.get('counts')} != {counts}")
    for name, expected in EXPECTED.items():
        if counts.get(name) != expected:
            raise InventoryError(f"{name}: expected {expected}, got {counts.get(name)}")

    statuses = Counter(status for row in records for status in migration_statuses(row))
    unknown = set(statuses) - CLASSIFICATIONS
    if unknown:
        raise InventoryError(f"unknown migration classifications: {sorted(unknown)}")
    if require_classified and statuses["pending"]:
        raise InventoryError(
            f"migration inventory still has {statuses['pending']} pending decisions"
        )


def check_inventory(path: Path, require_classified: bool) -> None:
    meta, records = read_inventory(path)
    validate_inventory(meta, records, require_classified)


def update_classifications(path: Path) -> None:
    meta, records = read_inventory(path)
    validate_inventory(meta, records, require_classified=False, require_record_digest=False)
    meta["record_digest"] = record_digest(records)
    validate_inventory(meta, records, require_classified=False)
    write_inventory(path, meta, records)


def require_source_match(
    committed_meta: dict[str, Any], committed_records: list[dict[str, Any]],
    generated_meta: dict[str, Any], generated_records: list[dict[str, Any]],
) -> None:
    fixed_meta = {
        "kind", "format", "pins", "lean_source_digest", "lean_source_files",
        "audit_record_digest", "counts",
    }
    if any(committed_meta.get(key) != generated_meta.get(key) for key in fixed_meta) \
            or audit_records(committed_records) != audit_records(generated_records):
        raise InventoryError("committed inventory differs from pinned source regeneration")


def default_fixture() -> Path:
    return REPO_ROOT / (
        "conformance-fixtures/HexIntervalMathlib/pnt-inventory.jsonl"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--refresh", action="store_true", help="regenerate from --source")
    mode.add_argument("--verify-source", action="store_true",
                      help="regenerate from --source and compare with --output")
    mode.add_argument("--check", action="store_true",
                      help="validate the committed fixture without network/source access")
    mode.add_argument(
        "--update-classifications", action="store_true",
        help="validate edited migration fields and refresh only the record digest",
    )
    mode.add_argument(
        "--inspect-source", action="store_true",
        help="print observed pin/count inputs without accepting or writing them",
    )
    parser.add_argument("--source", type=Path,
                        help="exact PrimeNumberTheoremAnd checkout for refresh/verify")
    parser.add_argument("--output", type=Path, default=default_fixture())
    parser.add_argument("--require-classified", action="store_true",
                        help="reject pending migration decisions")
    args = parser.parse_args()

    try:
        if args.require_classified and not args.check:
            parser.error("--require-classified is valid only with --check")
        if args.check:
            check_inventory(args.output, args.require_classified)
            print(f"pnt inventory: {args.output} is valid")
            return 0
        if args.update_classifications:
            update_classifications(args.output)
            print(f"pnt inventory: validated classifications in {args.output}")
            return 0
        if args.source is None:
            parser.error("--source is required with source-reading modes")
        if args.inspect_source:
            print(json.dumps(inspect_source(args.source.resolve()), indent=2, sort_keys=True))
            return 0
        source_root = args.source.resolve()
        meta, records = generate(source_root)
        require_fks2_probe_match(source_root)
        require_fks2_family_match(source_root)
        if args.refresh:
            carried = 0
            removed = 0
            if args.output.exists():
                _, previous = read_inventory(args.output)
                records, carried, removed = carry_migrations(previous, records)
            meta["record_digest"] = record_digest(records)
            validate_inventory(meta, records, require_classified=False)
            write_inventory(args.output, meta, records)
            print(
                f"pnt inventory: wrote {len(records)} records to {args.output}; "
                f"carried {carried} migration decisions, removed {removed} pending/raw records"
            )
            return 0
        committed_meta, committed_records = read_inventory(args.output)
        validate_inventory(committed_meta, committed_records, require_classified=False)
        require_source_match(committed_meta, committed_records, meta, records)
        print(f"pnt inventory: {args.output} matches {args.source}")
        return 0
    except (InventoryError, OSError, KeyError, TypeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
