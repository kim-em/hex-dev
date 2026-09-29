"""Check retention and output paths for the nested-field sweep."""
import unittest

from scripts.bench import sign_det_nested_kernel as runner
from scripts.bench import test_sign_det_semantics as retention


class NestedOutputTests(retention.OutputTests):
    runner = runner


if __name__ == "__main__":
    unittest.main()
