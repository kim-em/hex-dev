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

    def test_constant_record_fields(self):
        source = "structure Settings where\n  constant : Nat\ndef settings : Settings where\n  constant := 1\n"
        self.assertIsNone(ADMISSION.search(code_only(source)))
        for declaration in ("constant bad : False", "  constant bad : False",
                            "private constant bad : False", "constant\n  bad : False"):
            with self.subTest(declaration=declaration):
                self.assertIsNotNone(ADMISSION.search(code_only(declaration)))

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
            base = root / "HexRealClosure/BaseTests.lean"
            model = root / "HexRealClosureMathlib/BaseTests.lean"
            catalog = root / "HexRealClosure/BaseCatalogTests.lean"
            deflation = root / "conformance/HexRealClosure/DeflationConformance.lean"
            specialize = root / "adapters/HexRealClosureMathlib/Specialize.lean"
            specialize_tests = root / "adapters/HexRealClosureMathlib/SpecializeTests.lean"
            specialize_polynomial = root / "adapters/HexRealClosureMathlib/SpecializePolynomial.lean"
            specialize_regular = root / "adapters/HexRealClosureMathlib/SpecializeRegular.lean"
            specialize_query = root / "adapters/HexRealClosureMathlib/SpecializeQuery.lean"
            specialize_tarski = root / "adapters/HexRealClosureMathlib/SpecializeTarski.lean"
            specialize_reduction = root / "adapters/HexRealClosureMathlib/SpecializeReduction.lean"
            specialize_moment = root / "adapters/HexRealClosureMathlib/SpecializeMoment.lean"
            specialize_replay = root / "adapters/HexRealClosureMathlib/SpecializeReplay.lean"
            specialize_sample = root / "adapters/HexRealClosureMathlib/SpecializeSample.lean"
            specialize_selected = root / "adapters/HexRealClosureMathlib/SpecializeSelected.lean"
            specialize_descriptor = root / "adapters/HexRealClosureMathlib/SpecializeDescriptor.lean"
            transport_polynomial = root / "adapters/HexRealClosureMathlib/TransportPolynomial.lean"
            transport_product = root / "adapters/HexRealClosureMathlib/TransportProduct.lean"
            transport_arithmetic = root / "adapters/HexRealClosureMathlib/TransportArithmetic.lean"
            transport_query = root / "adapters/HexRealClosureMathlib/TransportQuery.lean"
            transport_tests = root / "adapters/HexRealClosureMathlib/TransportTests.lean"
            transport_ring = root / "adapters/HexRealClosureMathlib/TransportRing.lean"
            transport_power = root / "adapters/HexRealClosureMathlib/TransportPower.lean"
            transport_tarski = root / "adapters/HexRealClosureMathlib/TransportTarski.lean"
            transport_closed = root / "adapters/HexRealClosureMathlib/TransportClosed.lean"
            transport_closed_query = root / "adapters/HexRealClosureMathlib/TransportClosedQuery.lean"
            transport_regular = root / "adapters/HexRealClosureMathlib/TransportRegular.lean"
            transport_reduction = root / "adapters/HexRealClosureMathlib/TransportReduction.lean"
            transport_closed_reduction = root / "adapters/HexRealClosureMathlib/TransportClosedReduction.lean"
            transport_preparation = root / "adapters/HexRealClosureMathlib/TransportPreparation.lean"
            transport_moment = root / "adapters/HexRealClosureMathlib/TransportMoment.lean"
            transport_replay = root / "adapters/HexRealClosureMathlib/TransportReplay.lean"
            transport_sample = root / "adapters/HexRealClosureMathlib/TransportSample.lean"
            transport_descriptor = root / "adapters/HexRealClosureMathlib/TransportDescriptor.lean"
            transport_selected = root / "adapters/HexRealClosureMathlib/TransportSelected.lean"
            union = root / "adapters/HexRealClosureMathlib/Union.lean"
            union_tests = root / "adapters/HexRealClosureMathlib/UnionTests.lean"
            dependency = root / "HexExtra/SelectedField.lean"
            for path in (entry, bridge, sign, conformance, completion, handle, tables, reencoding, roots, refinement, conversion, base, model, catalog, deflation, specialize, specialize_tests, specialize_polynomial, specialize_regular, specialize_query, specialize_tarski, specialize_reduction, specialize_moment, specialize_replay, specialize_sample, specialize_selected, specialize_descriptor, transport_polynomial, transport_product, transport_arithmetic, transport_query, transport_tests, transport_ring, transport_power, transport_tarski, transport_closed, transport_closed_query, transport_regular, transport_reduction, transport_closed_reduction, transport_preparation, transport_moment, transport_replay, transport_sample, transport_descriptor, transport_selected, union, union_tests, dependency):
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
            base.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            model.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            catalog.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            deflation.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_tests.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_polynomial.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_regular.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_query.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_tarski.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_reduction.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_moment.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_replay.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_sample.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_selected.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            specialize_descriptor.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            transport_polynomial.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            transport_product.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            for path in (transport_arithmetic, transport_query, transport_tests, transport_ring, transport_power, transport_tarski, transport_closed, transport_closed_query, transport_regular, transport_reduction, transport_closed_reduction, transport_preparation, transport_moment, transport_replay, transport_sample, transport_descriptor, transport_selected):
                path.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            union.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            union_tests.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            dependency.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
            with patch.object(audit, "ROOT", root), redirect_stdout(StringIO()):
                audit.check()
                for probe in (union, union_tests):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*Union"):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                refinement.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                refinement.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/RefinementConformance"):
                    audit.check()
                refinement.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                conversion.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                conversion.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDetMathlib/ConvertConformance"):
                    audit.check()
                conversion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                for probe in (specialize, specialize_tests, specialize_polynomial, specialize_regular, specialize_query, specialize_tarski, specialize_reduction, specialize_moment, specialize_replay, specialize_sample, specialize_selected, specialize_descriptor, transport_polynomial, transport_product, transport_arithmetic, transport_query, transport_tests, transport_ring, transport_power, transport_tarski, transport_closed, transport_closed_query, transport_regular, transport_reduction, transport_closed_reduction, transport_preparation, transport_moment, transport_replay, transport_sample, transport_descriptor, transport_selected):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*(Specialize|Transport)"):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                for probe in (base, model, catalog):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*Base(Catalog)?Tests"):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
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
