"""Reject memory captures with mismatched source, operation or measurement mode."""
import json
import unittest

from scripts.bench.sign_det_memory import child_record, page_peak


class MemoryRecords(unittest.TestCase):
    def setUp(self):
        self.row = {"schema_version": 1, "kind": "parametric", "function": "f",
                    "param": 3, "inner_repeats": 1, "cache_mode": "cold",
                    "status": "ok", "error": None, "profile_kernel": True,
                    "env": {"git_commit": "revision", "git_dirty": False},
                    "peak_rss_kb": 100, "result_hash": "0xb"}

    def check(self, row):
        return child_record(json.dumps(row), "f", 3, "revision")

    def test_wrong_subject_and_source(self):
        self.check(self.row)
        for key, value in (("function", "other"), ("param", 7),
                           ("env", {"git_commit": "other", "git_dirty": False}),
                           ("env", {"git_commit": "revision", "git_dirty": True})):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                self.check(dict(self.row, **{key: value}))

    def test_failed_or_repeated_callback(self):
        for key, value in (("status", "error"), ("error", "failed"),
                           ("inner_repeats", 2), ("cache_mode", "warm"),
                           ("profile_kernel", False), ("result_hash", None)):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                self.check(dict(self.row, **{key: value}))

    def test_missing_memory_and_duplicate_rows(self):
        for value in (None, 0, -1, True):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.check(dict(self.row, peak_rss_kb=value))
        with self.assertRaises(ValueError):
            child_record(json.dumps(self.row) + "\n" + json.dumps(self.row), "f", 3, "revision")

    def test_page_peak_uses_all_retained_snapshots(self):
        text = "desc: --pages-as-heap=yes\ntime_unit: B\n"
        for i, size in enumerate((100, 500, 200)):
            text += (f"snapshot={i}\ntime={i * 1000}\nmem_heap_B={size}\n"
                     "mem_heap_extra_B=0\nmem_stacks_B=0\nheap_tree=empty\n")
        self.assertEqual(page_peak(text), {"mapped_page_peak_bytes": 500, "snapshots": 3})
        for changed in (text.replace("--pages-as-heap=yes", "--pages-as-heap=no"),
                        text.replace("mem_heap_B=500", "mem_heap_B=-500"),
                        text.replace("mem_heap_extra_B=0", "mem_heap_extra_B=1"),
                        text.replace("mem_stacks_B=0\n", "")):
            with self.subTest(text=changed), self.assertRaises(ValueError):
                page_peak(changed)
        with self.assertRaises(ValueError):
            page_peak("desc: --pages-as-heap=yes\ntime_unit: B\n")
