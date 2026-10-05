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

    def test_expression_admission_detector(self):
        for source in ("proof.hasSorry", "Expr.hasSorry proof", "type.hasSorry"):
            with self.subTest(source=source):
                self.assertEqual(audit.find_admissions(code_only(source)), [])
        for source in ("hasSorry", "proof.mkSorry", "Expr.mkSyntheticSorry",
                       "Lean.sorryAx", "proof.hasSorry || sorryAx", "by sorry",
                       "proof.hasSorry && admitGoal"):
            with self.subTest(source=source):
                self.assertTrue(audit.find_admissions(code_only(source)))

    def test_constant_record_fields(self):
        source = "structure Settings where\n  constant : Nat\ndef settings : Settings where\n  constant := 1\n"
        self.assertIsNone(ADMISSION.search(code_only(source)))
        for declaration in ("constant bad : False", "  constant bad : False",
                            "private constant bad : False", "constant\n  bad : False"):
            with self.subTest(declaration=declaration):
                self.assertIsNotNone(ADMISSION.search(code_only(declaration)))
    def test_constant_field_assignment(self):
        self.assertIsNone(ADMISSION.search(code_only("theorem width : Bounds where\n  constant := h\n")))
        self.assertIsNone(ADMISSION.search(code_only("structure Approximation where\n  constant : Rat → Bounds\n")))
        self.assertIsNotNone(ADMISSION.search(code_only("private constant hidden : False\n")))

    def test_interpolated_admission_fails_closed(self):
        for prefix in ("s!", "m!", "f!"):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                code_only(f'def x := {prefix}"{{(by sorry : Nat)}}"')
        with self.assertRaises(ValueError):
            code_only('def x := m!"{\"quoted\" ++ (by sorry : String)}"')

    def test_prime_before_character_literal(self):
        source = 'def x := f x\' \'"\'\ntheorem bad : False := by sorry\n'
        self.assertIsNotNone(ADMISSION.search(code_only(source)))

    def test_overlapping_cyclic_roots_and_fresh_source(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "Local").mkdir()
            sources = {
                "Local/Left.lean": "import Local.Shared\n",
                "Local/Right.lean": "public import Local.Shared\n",
                "Local/Shared.lean": "import Local.Left\ntheorem h : True := by trivial\n",
            }
            for name, source in sources.items():
                (root / name).write_text(source)
            with patch.object(audit, "ROOT", root), patch.object(
                audit, "code_only", wraps=code_only
            ) as mask:
                paths = audit.import_cones(["Local.Left", "Local.Right"])
                self.assertEqual(paths, set(map(Path, sources)))
                self.assertEqual(mask.call_count, 3)
                # A shared dependency must be reread on the next audit.
                (root / "Local/Shared.lean").write_text("import Local.Missing\n")
                with self.assertRaisesRegex(ValueError, "missing local import Local.Missing"):
                    audit.import_cones(["Local.Left", "Local.Right"])
                (root / "Local/Shared.lean").write_text(sources["Local/Shared.lean"])
                with self.assertRaisesRegex(ValueError, "missing local import Local.Absent"):
                    audit.import_cones(["Local.Left", "Local.Absent"])

    def test_import_cone_and_present_adapter(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            entry = root / "adapters/HexRCF/RealCoefficients.lean"
            bridge = root / "HexRealRootsMathlib/TarskiSoundness.lean"
            sign = root / "adapters/HexSignDetMathlib/RootProducer.lean"
            conformance = root / "conformance/HexSignDetMathlib/FieldConformance.lean"
            completion = root / "conformance/HexSignDet/FieldChecks.lean"
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
            transport_finite_tests = root / "adapters/HexRealClosureMathlib/TransportFiniteTests.lean"
            algebraic_transport = root / "adapters/HexRealClosureMathlib/AlgebraicTransport.lean"
            algebraic_yun = root / "adapters/HexRealClosureMathlib/AlgebraicYun.lean"
            algebraic_reencode = root / "adapters/HexRealClosureMathlib/AlgebraicReencode.lean"
            algebraic_reencode_tests = root / "HexRealClosure/AlgebraicReencodeTests.lean"
            algebraic_roots = root / "adapters/HexRealClosureMathlib/AlgebraicRoots.lean"
            union = root / "adapters/HexRealClosureMathlib/Union.lean"
            union_tests = root / "adapters/HexRealClosureMathlib/UnionTests.lean"
            root_probes = [root / name for name in (
                "examples/RealClosureConsumer/Query.lean",
                "examples/RealClosureConsumer/Sign.lean",
                "examples/RealClosureConsumer/Ordered.lean",
                "examples/RealClosureConsumer/Tower.lean",
                "HexRealClosure/TowerCatalog.lean",
                "HexRealClosure/TowerTests.lean",
                "HexRealClosure/RootFrame.lean",
                "HexRealClosure/RootFrameTests.lean",
                "HexRealClosure/FrameFormat.lean",
                "HexRealClosure/FrameFormatTests.lean",
                "HexRealClosure/TowerOrder.lean",
                "HexRealClosure/TowerOrderTests.lean",
                "adapters/HexRealClosureMathlib/TowerModel.lean",
                "adapters/HexRealClosureMathlib/TowerModelTests.lean",
                "adapters/HexRealClosureMathlib/TowerAlgebraic.lean",
                "adapters/HexRealClosureMathlib/TowerYun.lean",
                "HexRealClosure/TowerYunTests.lean",
                "HexRealClosure/TowerPolynomial.lean",
                "HexRealClosure/TowerRefinement.lean",
                "HexRealClosure/TowerRefinementTests.lean",
                "adapters/HexRealClosureMathlib/TowerRefinement.lean",
                "HexRealClosure/TowerTransport.lean",
                "HexRealClosure/TowerReuse.lean",
                "adapters/HexRealClosureMathlib/TowerReuse.lean",
                "HexRealClosure/TowerTransportTests.lean",
                "HexRealClosure/BaseInclusion.lean",
                "HexRealClosure/BaseInclusionTests.lean",
                "HexRealClosureMathlib/BaseInterpretation.lean",
                "HexRealClosureMathlib/BaseRealization.lean",
                "HexRealClosureMathlib/BaseStagedRealization.lean",
                "HexRealClosureMathlib/BaseProvider.lean",
                "HexRealClosure/BaseSubsequence.lean",
                "HexRealClosureMathlib/BaseSubsequence.lean",
                "HexRealClosureMathlib/BaseSubsequenceTests.lean",
                "HexRealClosureMathlib/BaseMap.lean",
                "HexRealClosureMathlib/BaseSubsequenceModels.lean",
                "HexRealClosureMathlib/BaseStagedSubsequence.lean",
                "adapters/HexRealClosureMathlib/BaseModel.lean",
                "HexRealClosureMathlib/BasePrefixModels.lean",
                "HexRealClosureMathlib/BaseModels.lean",
                "adapters/HexRealClosureMathlib/BaseFactory.lean",
                "adapters/HexRealClosureMathlib/BaseFactoryTests.lean",
                "adapters/HexRealClosureMathlib/BaseGatherTests.lean",
                "adapters/HexRealClosureMathlib/ContextModel.lean",
                "adapters/HexRealClosureMathlib/CacheModels.lean",
                "adapters/HexRealClosureMathlib/CacheRebuild.lean",
                "adapters/HexRealClosureMathlib/CacheGather.lean",
                "adapters/HexRealClosureMathlib/GatherTests.lean",
                "adapters/HexRealClosureMathlib/SpecializeNested.lean",
                "adapters/HexRealClosureMathlib/MonicEvaluation.lean",
                "adapters/HexRealClosureMathlib/RegularEvaluation.lean",
                "adapters/HexRealClosureMathlib/ModelEvaluation.lean",
                "adapters/HexRealClosureMathlib/AlgebraicEvaluation.lean",
                "adapters/HexRealClosureMathlib/SpecializeFractionRing.lean",
                "adapters/HexRealClosureMathlib/CoefficientMap.lean",
                "adapters/HexRealClosureMathlib/CoefficientQuery.lean",
                "adapters/HexRealClosureMathlib/CoefficientTarski.lean",
                "adapters/HexRealClosureMathlib/CoefficientEmbeddingTests.lean",
                "adapters/HexRealClosureMathlib/CoefficientEmbedding.lean",
                "adapters/HexRealClosureMathlib/CoefficientSelected.lean",
                "adapters/HexRealClosureMathlib/CoefficientDescriptor.lean",
                "adapters/HexRealClosureMathlib/CoefficientReplay.lean",
                "adapters/HexRealClosureMathlib/CoefficientMoment.lean",
                "adapters/HexRealClosureMathlib/CoefficientReduction.lean",
                "adapters/HexRealClosureMathlib/SharedPresentation.lean",
                "adapters/HexRealClosureMathlib/SharedPresentationTests.lean",
                "adapters/HexRealClosureMathlib/BaseOrder.lean",
                "adapters/HexRealClosureMathlib/BaseMapModel.lean",
                "HexRealClosure/TowerInclusion.lean",
                "HexRealClosure/LiveContext.lean",
                "HexRealClosure/LiveContextTests.lean",
                "adapters/HexRealClosureMathlib/TowerInclusion.lean",
                "adapters/HexRealClosureMathlib/LiveContext.lean",
                "HexRealClosure/TowerConversionTests.lean",
                "HexRealClosure/TowerPresentationTests.lean",
                "HexRealClosure/QueryReductionTests.lean",
                "adapters/HexRealClosureMathlib/TowerTransport.lean",
                "adapters/HexRealClosureMathlib/TowerTransportTests.lean",
                "HexRealClosure/BisectionTests.lean",
                "adapters/HexRealClosureMathlib/Bisection.lean",
                "adapters/HexRealClosureMathlib/BisectionRoots.lean",
                "conformance/HexRealClosure/BisectionFrontierTests.lean",
                "adapters/HexRealClosureMathlib/BisectionFrontier.lean",
                "adapters/HexRealClosureMathlib/BisectionCounts.lean",
                "adapters/HexRealClosureMathlib/Isolation.lean",
                "conformance/HexRealClosure/IsolationTests.lean",
                "adapters/HexRealClosureMathlib/BisectionFactor.lean",
                "adapters/HexRealClosureMathlib/IsolationFactor.lean",
                "adapters/HexRealClosureMathlib/IsolationRoots.lean",
                "conformance/HexRealClosure/RootPolicyConformance.lean",
                "conformance/HexRealClosure/IsolationConformance.lean",
                "conformance/HexRealClosureMathlib/CoefficientSignsConformance.lean",
                "adapters/HexRealClosureMathlib/RootOrder.lean",
                "HexRealClosure/RootOrderTests.lean",
                "HexRealClosure/RootFactorsTests.lean",
                "HexRealClosure/CompleteRoots.lean",
                "HexRealClosure/RootPolicyTests.lean",
                "adapters/HexRealClosureMathlib/TowerRootPolicy.lean",
                "adapters/HexRealClosureMathlib/RootPolicy.lean",
                "adapters/HexRealClosureMathlib/IsolationPolicy.lean",
                "adapters/HexRealClosureMathlib/IsolationTotal.lean",
                "adapters/HexRealClosureMathlib/RootTotal.lean",
                "HexRealClosure/Trivial.lean",
                "HexRealClosure/TrivialTests.lean",
                "adapters/HexRealClosureMathlib/Trivial.lean",
                "HexRealClosure/TrivialTower.lean",
                "HexRealClosure/TrivialTowerTests.lean",
                "HexRealClosure/TrivialChecks.lean",
                "conformance/HexRealClosure/TrivialConformance.lean",
                "adapters/HexRealClosureMathlib/TrivialTower.lean",
                "adapters/HexRealClosureMathlib/TrivialTowerTests.lean",
                "HexRealClosure/TowerRoots.lean",
                "HexRealClosure/TowerRootsTests.lean",
                "adapters/HexRealClosureMathlib/TowerRoots.lean",
                "HexRealClosure/RootTransport.lean",
                "HexRealClosure/RootCollection.lean",
                "HexRealClosure/RootCollectionTests.lean",
                "HexRealClosure/Sample.lean",
                "HexRealClosure/SampleTests.lean",
                "HexRealClosure/LocalSampleTests.lean",
                "conformance/HexRealClosure/SampleConformance.lean",
                "adapters/HexRealClosureMathlib/Sample.lean",
                "adapters/HexRealClosureMathlib/SampleTests.lean",
                "adapters/HexRealClosureMathlib/RootTransport.lean",
                "adapters/HexRealClosureMathlib/RootCollection.lean",
                "adapters/HexRealClosureMathlib/TowerCoverage.lean",
                "adapters/HexRealClosureMathlib/TowerNaturality.lean",
                "adapters/HexRealClosureMathlib/TowerEnlargeOrder.lean",
                "adapters/HexRealClosureMathlib/TowerEnlargeOrderTests.lean",
                "HexRealClosure/TowerEnlargeOrderTests.lean",
                "HexRealClosure/TowerEnlargement.lean",
                "adapters/HexRealClosureMathlib/RootFactors.lean",
                "HexRealClosure/NumberField.lean",
                "adapters/HexRealClosureMathlib/NumberField.lean",
                "conformance/HexRealClosure/NumberFieldConformance.lean",
                "HexRealClosure/NumberFieldTower.lean",
                "adapters/HexRealClosureMathlib/NumberFieldTower.lean",
                "conformance/HexRealClosure/NumberFieldSamples.lean")]
            qadjoin = root / "adapters/HexRealClosureMathlib/QAdjoin.lean"
            qadjoin_tests = root / "HexRealClosure/QAdjoinTests.lean"
            dependency = root / "HexExtra/SelectedField.lean"
            arithmetic = [root / f"adapters/HexRealClosureMathlib/{name}.lean"
                          for name in ("Algebraic", "AlgebraicClean", "AlgebraicValue",
                                       "BaseClean", "AlgebraicTower")]
            for path in root_probes:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            for path in (entry, bridge, sign, conformance, completion, base, model, catalog,
                         deflation, specialize, specialize_tests, specialize_polynomial,
                         specialize_regular, specialize_query, specialize_tarski,
                         specialize_reduction, specialize_moment, specialize_replay,
                         specialize_sample, specialize_selected, specialize_descriptor,
                         transport_polynomial, transport_product, transport_arithmetic,
                         transport_query, transport_tests, transport_ring, transport_power,
                         transport_tarski, transport_closed, transport_closed_query,
                         transport_regular, transport_reduction, transport_closed_reduction,
                         transport_preparation, transport_moment, transport_replay,
                         transport_sample, transport_descriptor, transport_selected, transport_finite_tests,
                         algebraic_transport, algebraic_yun, algebraic_reencode,
                         algebraic_reencode_tests, algebraic_roots,
                         union, union_tests,
                         qadjoin, qadjoin_tests, dependency, *arithmetic):
                path.parent.mkdir(parents=True, exist_ok=True)
            for path in arithmetic:
                path.write_text("public import HexRCF.RealCoefficients\n", encoding="utf-8")
            entry.write_text("public import HexRealRootsMathlib.TarskiSoundness\n", encoding="utf-8")
            bridge.write_text("theorem check_rootSum : True := by trivial\n", encoding="utf-8")
            sign.write_text("public import HexRCF.RealCoefficients\n", encoding="utf-8")
            conformance.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            completion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
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
            for path in (transport_arithmetic, transport_query, transport_tests, transport_ring, transport_power, transport_tarski, transport_closed, transport_closed_query, transport_regular, transport_reduction, transport_closed_reduction, transport_preparation, transport_moment, transport_replay, transport_sample, transport_descriptor, transport_selected, transport_finite_tests, algebraic_transport, algebraic_yun, algebraic_reencode, algebraic_reencode_tests, algebraic_roots):
                path.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            union.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            union_tests.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            qadjoin.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            qadjoin_tests.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
            dependency.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
            live_probes = []
            for module in ("HexRealClosure.LiveRequest", "HexRealClosure.LiveRequestTests",
                           "HexRealClosureMathlib.LiveRequest", "HexRealClosureMathlib.LiveRequestTests",
                           "HexRealClosureMathlib.SharedRealization", "HexRealClosureMathlib.SharedRealizationTests"):
                directory = root / ("adapters" if "Mathlib" in module else "")
                path = directory / (module.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                live_probes.append(path)
            with patch.object(audit, "ROOT", root), redirect_stdout(StringIO()):
                audit.check()
                for probe in (union, union_tests, qadjoin, qadjoin_tests, *live_probes):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*" + probe.stem):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                for probe in root_probes:
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission"):
                        audit.check()
                    probe.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")
                for probe in (specialize, specialize_tests, specialize_polynomial, specialize_regular, specialize_query, specialize_tarski, specialize_reduction, specialize_moment, specialize_replay, specialize_sample, specialize_selected, specialize_descriptor, transport_polynomial, transport_product, transport_arithmetic, transport_query, transport_tests, transport_ring, transport_power, transport_tarski, transport_closed, transport_closed_query, transport_regular, transport_reduction, transport_closed_reduction, transport_preparation, transport_moment, transport_replay, transport_sample, transport_descriptor, transport_selected, transport_finite_tests, algebraic_transport, algebraic_yun, algebraic_reencode, algebraic_reencode_tests, algebraic_roots):
                    probe.unlink()
                    with self.assertRaisesRegex(ValueError, "missing local import"):
                        audit.check()
                    probe.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in .*(Specialize|Transport|AlgebraicYun|AlgebraicReencode|AlgebraicRoots)"):
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
                bridge.write_text("theorem check_rootSum : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in HexRealRootsMathlib"):
                    audit.check()
                bridge.write_text("theorem check_rootSum : True := by trivial\n", encoding="utf-8")
                dependency.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in HexExtra/SelectedField"):
                    audit.check()
                dependency.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                completion.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/HexSignDet/FieldChecks"):
                    audit.check()
                completion.unlink()
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()
                completion.write_text("public import HexExtra.SelectedField\n", encoding="utf-8")

                for library in ("HexSignDetMathlib", "HexRealClosureMathlib"):
                    additional = root / "conformance" / library / "Nested/AnotherConformance.lean"
                    additional.parent.mkdir(parents=True, exist_ok=True)
                    additional.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in conformance/" + library):
                        audit.check()
                    additional.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                    for prefix in (root / "adapters", root):
                        shadow = prefix / library / "Nested/AnotherConformance.lean"
                        shadow.parent.mkdir(parents=True, exist_ok=True)
                        shadow.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                        with self.assertRaisesRegex(ValueError, "conformance module " + library + ".* is shadowed"):
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
                sign.write_text("public import HexRCF.RealCoefficients\ntheorem bad : True := by stop\n",
                                encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission"):
                    audit.check()
                sign.write_text("public import Unknown.Local\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "missing local import"):
                    audit.check()


if __name__ == "__main__":
    unittest.main()
