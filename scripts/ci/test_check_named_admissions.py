"""Small lexer regressions for the optional proof-admission audit."""

import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import check_named_admissions as audit
from check_named_admissions import ADMISSION, IMPORT, code_only


class AdmissionScannerTests(unittest.TestCase):
    def test_imports_behind_comments_and_on_one_line(self):
        source = 'public import Foo.Bar /- note -/ import Baz.Qux\n'
        self.assertEqual([m.group(1) for m in IMPORT.finditer(code_only(source))],
                         ["Foo.Bar", "Baz.Qux"])

    def test_quoted_character_does_not_hide_admission(self):
        self.assertIsNotNone(ADMISSION.search(code_only('def c := \'"\'\ntheorem bad : False := by sorry\n')))
        self.assertIsNone(ADMISSION.search(code_only('def c := \'"\'\ndef s := "sorry"\n')))

    def test_raw_string_does_not_hide_next_line(self):
        self.assertIsNotNone(ADMISSION.search(code_only('def s := r"\\"\ntheorem bad : False := by sorry\n')))
        self.assertIsNotNone(ADMISSION.search(code_only('def s := r#"\\"#\ntheorem bad : False := by sorry\n')))

    def test_other_admissions(self):
        for token in ("mkSorry", "mkSyntheticSorry", "exceptionToSorry",
                      "admitGoal", "sorryAx", "axiom bad : False",
                      "@[simp] axiom bad : False", "private axiom bad : False",
                      "constant bad : False", "theorem h : True := by stop",
                      "stop simp"):
            with self.subTest(token=token):
                self.assertIsNotNone(ADMISSION.search(code_only(token)))
        self.assertIsNone(ADMISSION.search(code_only("rw [Array.foldl_push_eq_append (stop := n) rfl]")))

    def test_interpolated_admission_fails_closed(self):
        for prefix in ("s!", "m!", "f!"):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                code_only(f'def x := {prefix}"{{(by sorry : Nat)}}"')
        with self.assertRaises(ValueError):
            code_only('def x := m!"{\"quoted\" ++ (by sorry : String)}"')

    def test_prime_before_character_literal(self):
        source = 'def x := f x\' \'"\'\ntheorem bad : False := by sorry\n'
        self.assertIsNotNone(ADMISSION.search(code_only(source)))

    def test_import_cone_and_present_adapter(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            entry = root / "adapters/HexRCF/RealCoefficients.lean"
            bridge = root / "adapters/HexRealRootsMathlib/TarskiSoundness.lean"
            sign = root / "adapters/HexSignDetMathlib/RootProducer.lean"
            conformance = root / "conformance/HexSignDetMathlib/SelectedProducerConformance.lean"
            completion = root / "conformance/HexSignDetMathlib/CompletionConformance.lean"
            handle = root / "conformance/HexSignDetMathlib/QueryHandleConformance.lean"
            tables = root / "conformance/HexSignDetMathlib/TableConformance.lean"
            reencoding = root / "conformance/HexSignDetMathlib/ReencodingConformance.lean"
            roots = root / "conformance/HexSignDetMathlib/RootListConformance.lean"
            refinement = root / "conformance/HexSignDetMathlib/RefinementConformance.lean"
            conversion = root / "conformance/HexSignDetMathlib/ConvertConformance.lean"
            bisection = root / "HexRealClosure/BisectionTests.lean"
            model = root / "adapters/HexRealClosureMathlib/Bisection.lean"
            partition = root / "adapters/HexRealClosureMathlib/BisectionRoots.lean"
            deflation = root / "conformance/HexRealClosure/DeflationConformance.lean"
            frontier = root / "conformance/HexRealClosure/BisectionFrontierTests.lean"
            traversal = root / "adapters/HexRealClosureMathlib/BisectionFrontier.lean"
            counts = root / "adapters/HexRealClosureMathlib/BisectionCounts.lean"
            isolation = root / "adapters/HexRealClosureMathlib/Isolation.lean"
            isolation_tests = root / "conformance/HexRealClosure/IsolationTests.lean"
            factor = root / "adapters/HexRealClosureMathlib/BisectionFactor.lean"
            isolation_factor = root / "adapters/HexRealClosureMathlib/IsolationFactor.lean"
            isolation_roots = root / "adapters/HexRealClosureMathlib/IsolationRoots.lean"
            isolation_conformance = root / "conformance/HexRealClosure/IsolationConformance.lean"
            root_order = root / "adapters/HexRealClosureMathlib/RootOrder.lean"
            root_order_tests = root / "HexRealClosure/RootOrderTests.lean"
            root_factors = root / "HexRealClosure/RootFactorsTests.lean"
            factor_model = root / "adapters/HexRealClosureMathlib/RootFactors.lean"
            dependency = root / "HexExtra/SelectedField.lean"
            for path in (entry, bridge, sign, conformance, completion, handle, tables, reencoding, roots, refinement, conversion, bisection, model, partition, deflation, frontier, traversal, counts, isolation, isolation_tests, factor, isolation_factor, isolation_roots, isolation_conformance, root_order, root_order_tests, root_factors, factor_model, dependency):
                path.parent.mkdir(parents=True, exist_ok=True)
            entry.write_text("public import HexRealRootsMathlib.TarskiSoundness\n", encoding="utf-8")
            bridge.write_text("theorem check_rootSum : True := by trivial\n", encoding="utf-8")
            sign.write_text("public import HexRCF.RealCoefficients\n", encoding="utf-8")
            conformance.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            completion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            handle.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            tables.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            reencoding.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            roots.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            refinement.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            conversion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            bisection.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            model.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            partition.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            deflation.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            frontier.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            traversal.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            counts.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            isolation.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            isolation_tests.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            factor.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            isolation_factor.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            isolation_roots.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            isolation_conformance.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            root_order.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            root_order_tests.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            root_factors.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            factor_model.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            dependency.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
            with patch.object(audit, "ROOT", root), redirect_stdout(StringIO()):
                audit.check()
                refinement.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                refinement.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/RefinementConformance"):
                    audit.check()
                refinement.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                for probe in (isolation_roots, isolation_conformance):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*Isolation"):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                for probe in (root_order, root_order_tests, root_factors, factor_model):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*Root(Order|Factors)"):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                conversion.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                conversion.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/ConvertConformance"):
                    audit.check()
                conversion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                deflation.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                deflation.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexRealClosure/DeflationConformance"):
                    audit.check()
                deflation.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                handle.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                handle.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/QueryHandleConformance"):
                    audit.check()
                handle.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                bridge.write_text("theorem check_rootSum : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in adapters/HexRealRootsMathlib"):
                    audit.check()
                bridge.write_text("theorem check_rootSum : True := by trivial\n", encoding="utf-8")
                dependency.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in HexExtra/SelectedField"):
                    audit.check()
                dependency.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                completion.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/CompletionConformance"):
                    audit.check()
                completion.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                completion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")

                additional = root / "conformance/HexSignDetMathlib/Nested/AnotherConformance.lean"
                additional.parent.mkdir()
                additional.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/Nested/AnotherConformance"):
                    audit.check()
                additional.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                shadow = root / "adapters/HexSignDetMathlib/Nested/AnotherConformance.lean"
                shadow.parent.mkdir(parents=True, exist_ok=True)
                shadow.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "conformance module .* is shadowed"):
                    audit.check()
                shadow.unlink()
                additional.unlink()
                adapter_shadow = root / "HexSignDetMathlib/RootProducer.lean"
                adapter_shadow.parent.mkdir(parents=True, exist_ok=True)
                adapter_shadow.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "adapter module .* is shadowed"):
                    audit.check()
                adapter_shadow.unlink()
                nested_adapter = root / "adapters/HexSignDetMathlib/Nested/AnotherAdapter.lean"
                nested_adapter.parent.mkdir(exist_ok=True)
                nested_adapter.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in adapters/HexSignDetMathlib/Nested/AnotherAdapter"):
                    audit.check()
                nested_adapter.unlink()
                tables.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/TableConformance"):
                    audit.check()
                tables.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                tables.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                sign.write_text("public import HexRCF.RealCoefficients\ntheorem bad : True := by stop\n",
                                encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission"):
                    audit.check()
                sign.write_text("public import Unknown.Local\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()


if __name__ == "__main__":
    unittest.main()
