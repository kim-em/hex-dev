"""Reject false conformance answers and malformed oracle expectations."""
import json
import unittest
from scripts.oracle.sign_det_json_bytes import check_answer, corpus, expected


def answer(text):
    return ["ok", text, json.loads(json.dumps(expected(text.encode("utf-8"))))]


class JsonByteOracleTests(unittest.TestCase):
    def test_changed_integer_rejects(self):
        with self.assertRaisesRegex(ValueError, "changed"):
            check_answer({"bytes": list(b"[-123]"), "accept": True}, answer("[123]"))

    def test_false_rejection_rejects(self):
        with self.assertRaisesRegex(ValueError, "valid input rejected"):
            check_answer({"bytes": list(b"null"), "accept": True}, ["error"])

    def test_false_acceptance_rejects(self):
        with self.assertRaisesRegex(ValueError, "accepted"):
            check_answer({"bytes": list(b"[1,]"), "accept": False}, answer("[1]"))

    def test_lone_surrogate_rejects(self):
        with self.assertRaisesRegex(ValueError, "accepted"):
            check_answer({"bytes": list(b'"\\ud800"'), "accept": False}, answer('"x"'))

    def test_wrong_fixture_expectation_rejects(self):
        with self.assertRaisesRegex(ValueError, "valid negative"):
            check_answer({"bytes": list(b"[]"), "accept": False}, ["error"])
        with self.assertRaisesRegex(ValueError, "invalid positive"):
            check_answer({"bytes": list(b"\xff"), "accept": True}, ["error"])

    def test_duplicate_fields_preserved(self):
        record = {"bytes": list(b'{"x":1,"x":2}'), "accept": True}
        check_answer(record, answer('{"x":1,"x":2}'))
        for wrong in ['{"x":2}', '{"x":2,"x":1}']:
            with self.assertRaisesRegex(ValueError, "changed"):
                check_answer(record, answer(wrong))

    def test_boolean_integer_confusion_rejects(self):
        for original, wrong in [(b"true", "1"), (b"false", "0"), (b"1", "true")]:
            with self.assertRaisesRegex(ValueError, "changed"):
                check_answer({"bytes": list(original), "accept": True}, answer(wrong))

    def test_field_order_preserved(self):
        with self.assertRaisesRegex(ValueError, "changed"):
            check_answer({"bytes": list(b'{"a":1,"b":2}'), "accept": True},
                         answer('{"b":2,"a":1}'))

    def test_wrong_constructor_with_correct_print_rejects(self):
        result = answer("true")
        result[2] = ["int", 1]
        with self.assertRaisesRegex(ValueError, "constructors changed"):
            check_answer({"bytes": list(b"true"), "accept": True}, result)

    def test_corpus_expectations(self):
        for record in corpus():
            raw = bytes(record["bytes"])
            check_answer(record, answer(raw.decode("utf-8")) if record["accept"] else ["error"])


if __name__ == "__main__":
    unittest.main()
