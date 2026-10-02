"""Reject false conformance answers and malformed oracle expectations."""
import unittest
from scripts.oracle.sign_det_json_bytes import check_answer, corpus


class JsonByteOracleTests(unittest.TestCase):
    def test_changed_integer_rejects(self):
        with self.assertRaisesRegex(ValueError, "changed"):
            check_answer({"bytes": list(b"[-123]"), "accept": True}, ["ok", "[123]"])

    def test_false_rejection_rejects(self):
        with self.assertRaisesRegex(ValueError, "valid input rejected"):
            check_answer({"bytes": list(b"null"), "accept": True}, ["error"])

    def test_false_acceptance_rejects(self):
        with self.assertRaisesRegex(ValueError, "accepted"):
            check_answer({"bytes": list(b"[1,]"), "accept": False}, ["ok", "[1]"])

    def test_lone_surrogate_rejects(self):
        with self.assertRaisesRegex(ValueError, "accepted"):
            check_answer({"bytes": list(b'"\\ud800"'), "accept": False}, ["ok", '"x"'])

    def test_wrong_fixture_expectation_rejects(self):
        with self.assertRaisesRegex(ValueError, "valid negative"):
            check_answer({"bytes": list(b"[]"), "accept": False}, ["error"])
        with self.assertRaisesRegex(ValueError, "invalid positive"):
            check_answer({"bytes": list(b"\xff"), "accept": True}, ["error"])

    def test_duplicate_fields_semantics(self):
        check_answer({"bytes": list(b'{"x":1,"x":2}'), "accept": True},
                     ["ok", '{"x":1,"x":2}'])

    def test_corpus_expectations(self):
        for record in corpus():
            raw = bytes(record["bytes"])
            check_answer(record, ["ok", raw.decode("utf-8")] if record["accept"] else ["error"])


if __name__ == "__main__":
    unittest.main()
