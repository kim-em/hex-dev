#!/usr/bin/env python3
"""Unit tests for the source-pinned PNT+ migration inventory."""

import copy
import json
import tempfile
import unittest
from pathlib import Path

from scripts.maintenance import pnt_inventory as inventory


class MaskLeanTests(unittest.TestCase):
    def test_masks_comments_and_strings_but_not_identifiers(self) -> None:
        source = """theorem check' : True := by
  interval_decide
  -- interval_decide
  /- outer interval_auto /- nested interval_decide -/ done -/
  let s := "interval_auto"
  let c := 'x'
  let escaped := '\\x41'
  let quote := '\\"'
  interval_auto
"""
        masked = inventory.mask_lean(source)

        self.assertIn("check'", masked)
        self.assertEqual(len(source), len(masked))
        self.assertEqual(source.count("\n"), masked.count("\n"))
        self.assertEqual(len(list(inventory.TOKEN_RE["interval_decide"].finditer(masked))), 1)
        self.assertEqual(len(list(inventory.TOKEN_RE["interval_auto"].finditer(masked))), 1)
        self.assertEqual(
            len(list(inventory.TOKEN_RE["interval_decide"].finditer("interval_decide'"))),
            0,
        )

    def test_rejects_unterminated_comment_and_string(self) -> None:
        with self.assertRaisesRegex(inventory.InventoryError, "block comment"):
            inventory.mask_lean("/- unfinished")
        with self.assertRaisesRegex(inventory.InventoryError, "string literal"):
            inventory.mask_lean('"unfinished')

    def test_masks_escaped_single_quote_character(self) -> None:
        literal = r"'\''"
        self.assertEqual(inventory.char_literal_end(literal, 0), len(literal))
        masked = inventory.mask_lean(f"let apostrophe := {literal}\ninterval_auto\n")
        self.assertEqual(len(list(inventory.TOKEN_RE["interval_auto"].finditer(masked))), 1)

    def test_escaped_character_cannot_consume_a_newline(self) -> None:
        source = "let broken := '\\\ninterval_auto\n'\n"
        masked = inventory.mask_lean(source)
        self.assertEqual(source.count("\n"), masked.count("\n"))
        self.assertEqual(len(list(inventory.TOKEN_RE["interval_auto"].finditer(masked))), 1)

    def test_table_rows_include_first_tuple_on_opening_line(self) -> None:
        source = (
            "noncomputable def table_12_aux := [(0, 0)]\n"
            "noncomputable def table_12 := [(1, f (2)),\n  (3, 4)]\n"
            "def later := []\n"
        )
        rows = inventory.table_rows(inventory.mask_lean(source), "table_12")
        self.assertEqual(rows, ["(1, f (2))", "(3, 4)"])

    def test_fks2_probe_requires_exact_shard(self) -> None:
        source = "def cells_11 := [\n  ⟨1, 2, 3/4, 5/6, 7/8⟩,\n  ⟨2, 3, 4/5, 6/7, 8/9⟩\n]\n"
        provider = "def cells11 := [\n⟨1,2,3/4,5/6,7/8⟩,\n⟨2,3,4/5,6/7,8/9⟩\n]\n"
        old_count = inventory.FKS2_PROBE_CELLS
        inventory.FKS2_PROBE_CELLS = 2
        self.addCleanup(setattr, inventory, "FKS2_PROBE_CELLS", old_count)
        inventory.require_fks2_shard_match(source, provider)
        with self.assertRaisesRegex(inventory.InventoryError, "cell 1"):
            inventory.require_fks2_shard_match(
                source, provider.replace("8/9", "9/10")
            )

    def test_fks2_family_requires_every_digest_and_tuple(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        source_dir = root / "source/PrimeNumberTheoremAnd/IEANTN/FKS2Tables"
        provider_dir = root / "provider"
        source_dir.mkdir(parents=True)
        provider_dir.mkdir()
        records = []
        for shard in range(14):
            row = f"⟨{shard}, {shard + 1}, 3/4, 5/6, 7/8⟩"
            (source_dir / f"Table4ExtData_{shard:02}.lean").write_text(
                f"def cells := [\n  {row}\n]\n", encoding="utf-8"
            )
            provider = provider_dir / f"PntFks2FamilyData{shard:02}.lean"
            provider.write_text(f"def cells := [\n  {row}\n]\n", encoding="utf-8")
            normalized = [row.replace(" ", "")]
            records.append(
                f'⟨{shard}, 1, "{inventory.fks_rows_digest(normalized)}"⟩'
            )
        aggregate = root / "family.lean"
        aggregate.write_text("\n".join(records), encoding="utf-8")
        old_counts = inventory.FKS2_SHARD_COUNTS
        old_family = inventory.FKS2_FAMILY_PROVIDER
        old_data = inventory.FKS2_FAMILY_DATA
        old_probe = inventory.FKS2_PROBE_PROVIDER
        inventory.FKS2_SHARD_COUNTS = tuple([1] * 14)
        inventory.FKS2_FAMILY_PROVIDER = aggregate
        inventory.FKS2_FAMILY_DATA = provider_dir
        inventory.FKS2_PROBE_PROVIDER = provider_dir / "PntFks2FamilyData11.lean"
        self.addCleanup(setattr, inventory, "FKS2_SHARD_COUNTS", old_counts)
        self.addCleanup(setattr, inventory, "FKS2_FAMILY_PROVIDER", old_family)
        self.addCleanup(setattr, inventory, "FKS2_FAMILY_DATA", old_data)
        self.addCleanup(setattr, inventory, "FKS2_PROBE_PROVIDER", old_probe)
        inventory.require_fks2_family_match(root / "source")
        bad = provider_dir / "PntFks2FamilyData12.lean"
        bad.write_text(bad.read_text().replace("7/8", "8/9"), encoding="utf-8")
        with self.assertRaisesRegex(inventory.InventoryError, "shard 12 at cell 0"):
            inventory.require_fks2_family_match(root / "source")

    def test_declaration_map_tracks_enclosing_declaration(self) -> None:
        masked = inventory.mask_lean(
            "theorem first : True := by\n  trivial\n\nexample : True := by\n  trivial\n"
        )
        declarations = inventory.declaration_map(masked)
        self.assertEqual(declarations[1], "first")
        self.assertEqual(declarations[4], "example@4")


class InventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = inventory.default_fixture()
        cls.meta, cls.records = inventory.read_inventory(cls.fixture)

    def write_rows(self, meta: dict, records: list[dict]) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "inventory.jsonl"
        inventory.write_inventory(path, meta, records)
        return path

    def test_committed_inventory_is_valid_but_not_yet_classified(self) -> None:
        inventory.check_inventory(self.fixture, require_classified=False)
        with self.assertRaisesRegex(inventory.InventoryError, "pending decisions"):
            inventory.check_inventory(self.fixture, require_classified=True)

    def test_classification_edits_do_not_change_audit_identity(self) -> None:
        meta = copy.deepcopy(self.meta)
        records = copy.deepcopy(self.records)
        row = next(row for row in records if row.get("migration", {}).get("status") == "pending")
        row["migration"] = {
            "status": "accepted-after-rewrite",
            "note": "unit-test classification",
            "rewrite": "factor the repeated bound through one shared theorem",
            "evidence": [
                "conformance/HexIntervalMathlib/PntLogTableConformance.lean"
            ],
        }
        path = self.write_rows(meta, records)
        inventory.update_classifications(path)
        inventory.check_inventory(path, require_classified=False)

    def test_source_verification_ignores_valid_migration_edits(self) -> None:
        committed_meta = copy.deepcopy(self.meta)
        committed_records = copy.deepcopy(self.records)
        generated_meta = copy.deepcopy(self.meta)
        generated_records = copy.deepcopy(self.records)
        row = next(
            row for row in committed_records
            if row.get("migration", {}).get("status") == "pending"
        )
        row["migration"]["note"] = "classification work may change this note"
        committed_meta["record_digest"] = inventory.record_digest(committed_records)
        inventory.require_source_match(
            committed_meta, committed_records, generated_meta, generated_records,
        )

    def test_refresh_carries_classifications_by_audit_identity(self) -> None:
        previous = copy.deepcopy(self.records)
        generated = copy.deepcopy(self.records)
        previous[0]["migration"]["note"] = "preserved migration note"
        carried_records, carried, removed = inventory.carry_migrations(previous, generated)
        expected_carried = sum(
            row["migration"]["status"] not in {"not-a-call", "inventory-only"}
            for row in self.records
        )
        self.assertEqual((carried, removed), (expected_carried, 0))
        self.assertEqual(carried_records[0]["migration"]["note"], "preserved migration note")

    def test_refresh_does_not_report_fixed_audit_labels_as_carried(self) -> None:
        previous = [{"kind": "leancert-reference", "migration": inventory.inventory_only()}]
        generated = copy.deepcopy(previous)
        _, carried, removed = inventory.carry_migrations(previous, generated)
        self.assertEqual((carried, removed), (0, 0))

    def test_refresh_refuses_to_drop_classified_record(self) -> None:
        previous = copy.deepcopy(self.records[:1])
        previous[0]["migration"] = {
            "status": "accepted-unchanged",
            "note": "classified",
            "evidence": ["HexIntervalMathlib.PNT.example"],
        }
        with self.assertRaisesRegex(inventory.InventoryError, "discard 1 classified"):
            inventory.carry_migrations(previous, [])

    def test_source_field_tamper_is_rejected_even_with_updated_record_digest(self) -> None:
        meta = copy.deepcopy(self.meta)
        records = copy.deepcopy(self.records)
        row = next(row for row in records if "path" in row)
        row["path"] += ".tampered"
        records.sort(key=inventory.record_sort_key)
        meta["record_digest"] = inventory.record_digest(records)
        meta["counts"] = inventory.summarize(records)
        path = self.write_rows(meta, records)
        with self.assertRaisesRegex(inventory.InventoryError, "audit-record digest"):
            inventory.check_inventory(path, require_classified=False)

    def test_noncanonical_order_is_rejected(self) -> None:
        meta = copy.deepcopy(self.meta)
        records = copy.deepcopy(self.records)
        records[0], records[1] = records[1], records[0]
        meta["record_digest"] = inventory.record_digest(records)
        path = self.write_rows(meta, records)
        with self.assertRaisesRegex(inventory.InventoryError, "canonical order"):
            inventory.check_inventory(path, require_classified=False)

    def test_missing_migration_classification_is_rejected(self) -> None:
        meta = copy.deepcopy(self.meta)
        records = copy.deepcopy(self.records)
        row = next(row for row in records if row.get("migration", {}).get("status") == "pending")
        row.pop("migration")
        meta["record_digest"] = inventory.record_digest(records)
        path = self.write_rows(meta, records)
        with self.assertRaisesRegex(inventory.InventoryError, "migration must be an object"):
            inventory.check_inventory(path, require_classified=False)

    def test_malformed_migration_is_reported_as_inventory_error(self) -> None:
        record = {"kind": "dependency-interface", "migration": "pending"}
        with self.assertRaisesRegex(inventory.InventoryError, "migration must be an object"):
            inventory.require_migrations([record])

    def test_lexical_reference_is_audit_evidence_not_release_obligation(self) -> None:
        record = {
            "kind": "leancert-reference",
            "symbol": "LeanCert.Core",
            "interface_provenance": [
                "LeanCert.ANT", "LeanCert.Validity.AffineCover",
            ],
            "migration": inventory.inventory_only(),
        }
        inventory.require_migrations([record])
        self.assertEqual(list(inventory.migration_statuses(record)), [])

    def test_unowned_lexical_reference_is_rejected(self) -> None:
        with self.assertRaisesRegex(inventory.InventoryError, "lacks interface provenance"):
            inventory.reference_interfaces("LeanCert.Unreviewed.API")

    def test_finished_classification_requires_structured_evidence(self) -> None:
        record = {
            "kind": "dependency-interface",
            "migration": {
                "status": "replaced-by-stronger-result",
                "note": "ported",
                "evidence": ["HexIntervalMathlib.PNT.bklnwBounds"],
            },
        }
        with self.assertRaisesRegex(inventory.InventoryError, "replacement theorem"):
            inventory.require_migrations([record])
        record["migration"]["replacement"] = "PNT.Hex.bklnwBounds"
        inventory.require_migrations([record])

    def test_finished_classification_requires_existing_evidence_path(self) -> None:
        record = {
            "kind": "dependency-interface",
            "migration": {
                "status": "accepted-unchanged",
                "note": "ported",
                "evidence": ["conformance/HexIntervalMathlib/Missing.lean"],
            },
        }
        with self.assertRaisesRegex(inventory.InventoryError, "evidence path"):
            inventory.require_migrations([record])

    def test_pending_classification_validates_supplied_evidence_path(self) -> None:
        record = {
            "kind": "generated-family",
            "migration": {
                "status": "pending",
                "note": "partial probe",
                "evidence": ["conformance/HexIntervalMathlib/Missing.lean"],
            },
        }
        with self.assertRaisesRegex(inventory.InventoryError, "evidence path"):
            inventory.require_migrations([record])

    def test_dependency_surface_must_match_all_six_interfaces(self) -> None:
        imports = [
            {"module": module, "path": "X.lean", "line": index + 1}
            for index, module in enumerate(inventory.DEPENDENCY_INTERFACES)
        ]
        rows = inventory.dependency_records(imports)
        self.assertEqual({row["module"] for row in rows}, set(inventory.DEPENDENCY_INTERFACES))
        with self.assertRaisesRegex(inventory.InventoryError, "import surface drifted"):
            inventory.dependency_records(imports[:-1])

    def test_fks2_family_has_exact_shard_partition(self) -> None:
        family = next(
            row for row in self.records
            if row.get("kind") == "generated-family"
            and row.get("family") == "fks2-table4ext"
        )
        sizes = sorted(shard["cells"] for shard in family["shards"])
        self.assertEqual(sizes, [590] + [1000] * 13)
        self.assertEqual(sum(sizes), 13590)

    def test_bklnw_generated_families_expand_outer_source_forms(self) -> None:
        families = {
            row["family"]: row for row in self.records
            if row.get("kind") == "generated-family"
        }
        table10 = families["bklnw-table10-source-sites"]
        self.assertEqual(table10["target_check_sites"], 87)
        self.assertEqual(table10["supporting_a2_check_sites"], 38)
        table12 = families["bklnw-table12-cells"]
        self.assertEqual(
            (table12["rows"], table12["ordinary_rows"], table12["logarithmic_rows"]),
            (26, 24, 2),
        )
        self.assertEqual(table12["checks_per_row"], 5)
        self.assertEqual(table12["expanded_checks"], 130)
        self.assertEqual(len(table12["false_original_boundary_rows"]), 4)

    def test_headline_source_counts_are_pinned_independently(self) -> None:
        self.assertEqual(self.meta["lean_source_files"], 232)
        self.assertEqual(self.meta["counts"], {
            "bklnw_table10_a2_sites": 38,
            "bklnw_table10_target_sites": 87,
            "bklnw_table12_checks": 130,
            "bklnw_table12_logarithmic_rows": 2,
            "bklnw_table12_ordinary_rows": 24,
            "dependency_interface": 6,
            "fks2_cells": 13590,
            "fks2_shards": 14,
            "interval_auto_actual": 60,
            "interval_auto_textual": 61,
            "interval_decide_actual": 280,
            "interval_decide_textual": 290,
            "leancert_import": 16,
            "leancert_reference": 107,
            "native_decide_actual": 83,
            "records": 567,
        })


if __name__ == "__main__":
    unittest.main()
