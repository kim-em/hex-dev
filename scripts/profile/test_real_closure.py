"""Validate retained benchmark rows before profiling attribution."""
import unittest
from scripts.profile.real_closure import measurement_rows, validate_measurement

class MeasurementTests(unittest.TestCase):
    def test_schema_string_hash_and_clean_commit(self):
        row = {"status": "ok", "result_hash": "0x1", "env": {"git_commit": "abc", "git_dirty": False}}
        self.assertIs(validate_measurement([row], "abc"), row)
        self.assertEqual(measurement_rows('noise\n{"status":"ok"}\n'), [{"status": "ok"}])
        for update in ({"result_hash": 1}, {"result_hash": "0x0"}, {"status": "error"},
                       {"env": {"git_commit": "other", "git_dirty": False}},
                       {"env": {"git_commit": "abc", "git_dirty": True}}):
            with self.subTest(update=update), self.assertRaises(RuntimeError):
                validate_measurement([{**row, **update}], "abc")
        for rows in ([], [row, row]):
            with self.assertRaises(RuntimeError):
                validate_measurement(rows, "abc")

if __name__ == "__main__":
    unittest.main()
