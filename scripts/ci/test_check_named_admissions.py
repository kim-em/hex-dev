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
            bridge = root / "HexRealRootsTheory/TarskiSoundness.lean"
            sign = root / "adapters/HexSignDetTheory/RootProducer.lean"
            conformance = root / "conformance/HexRCF/SignDetFieldProofs.lean"
            completion = root / "conformance/HexSignDet/FieldChecks.lean"
            base = root / "HexRealClosure/BaseTests.lean"
            model = root / "HexRealClosureTheory/BaseTests.lean"
            catalog = root / "HexRealClosure/BaseCatalogTests.lean"
            deflation = root / "conformance/HexRealClosure/DeflationConformance.lean"
            specialize = root / "adapters/HexRealClosureTheory/Specialize.lean"
            specialize_tests = root / "adapters/HexRealClosureTheory/SpecializeTests.lean"
            specialize_polynomial = root / "adapters/HexRealClosureTheory/SpecializePolynomial.lean"
            specialize_regular = root / "adapters/HexRealClosureTheory/SpecializeRegular.lean"
            specialize_query = root / "adapters/HexRealClosureTheory/SpecializeQuery.lean"
            specialize_tarski = root / "adapters/HexRealClosureTheory/SpecializeTarski.lean"
            specialize_reduction = root / "adapters/HexRealClosureTheory/SpecializeReduction.lean"
            specialize_moment = root / "adapters/HexRealClosureTheory/SpecializeMoment.lean"
            specialize_replay = root / "adapters/HexRealClosureTheory/SpecializeReplay.lean"
            specialize_sample = root / "adapters/HexRealClosureTheory/SpecializeSample.lean"
            specialize_selected = root / "adapters/HexRealClosureTheory/SpecializeSelected.lean"
            specialize_descriptor = root / "adapters/HexRealClosureTheory/SpecializeDescriptor.lean"
            transport_polynomial = root / "adapters/HexRealClosureTheory/TransportPolynomial.lean"
            transport_product = root / "adapters/HexRealClosureTheory/TransportProduct.lean"
            transport_arithmetic = root / "adapters/HexRealClosureTheory/TransportArithmetic.lean"
            transport_query = root / "adapters/HexRealClosureTheory/TransportQuery.lean"
            transport_tests = root / "adapters/HexRealClosureTheory/TransportTests.lean"
            transport_ring = root / "adapters/HexRealClosureTheory/TransportRing.lean"
            transport_power = root / "adapters/HexRealClosureTheory/TransportPower.lean"
            transport_tarski = root / "adapters/HexRealClosureTheory/TransportTarski.lean"
            transport_closed = root / "adapters/HexRealClosureTheory/TransportClosed.lean"
            transport_closed_query = root / "adapters/HexRealClosureTheory/TransportClosedQuery.lean"
            transport_regular = root / "adapters/HexRealClosureTheory/TransportRegular.lean"
            transport_reduction = root / "adapters/HexRealClosureTheory/TransportReduction.lean"
            transport_closed_reduction = root / "adapters/HexRealClosureTheory/TransportClosedReduction.lean"
            transport_preparation = root / "adapters/HexRealClosureTheory/TransportPreparation.lean"
            transport_moment = root / "adapters/HexRealClosureTheory/TransportMoment.lean"
            transport_replay = root / "adapters/HexRealClosureTheory/TransportReplay.lean"
            transport_sample = root / "adapters/HexRealClosureTheory/TransportSample.lean"
            transport_descriptor = root / "adapters/HexRealClosureTheory/TransportDescriptor.lean"
            transport_selected = root / "adapters/HexRealClosureTheory/TransportSelected.lean"
            transport_finite_tests = root / "adapters/HexRealClosureTheory/TransportFiniteTests.lean"
            algebraic_transport = root / "adapters/HexRealClosureTheory/AlgebraicTransport.lean"
            algebraic_yun = root / "adapters/HexRealClosureTheory/AlgebraicYun.lean"
            algebraic_reencode = root / "adapters/HexRealClosureTheory/AlgebraicReencode.lean"
            algebraic_reencode_tests = root / "HexRealClosure/AlgebraicReencodeTests.lean"
            algebraic_roots = root / "adapters/HexRealClosureTheory/AlgebraicRoots.lean"
            union = root / "adapters/HexRealClosureTheory/Union.lean"
            union_tests = root / "adapters/HexRealClosureTheory/UnionTests.lean"
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
                "adapters/HexRealClosureTheory/TowerModel.lean",
                "adapters/HexRealClosureTheory/TowerModelTests.lean",
                "adapters/HexRealClosureTheory/TowerAlgebraic.lean",
                "adapters/HexRealClosureTheory/TowerYun.lean",
                "HexRealClosure/TowerYunTests.lean",
                "HexRealClosure/TowerPolynomial.lean",
                "HexRealClosure/TowerRefinement.lean",
                "HexRealClosure/TowerRefinementTests.lean",
                "adapters/HexRealClosureTheory/TowerRefinement.lean",
                "HexRealClosure/TowerTransport.lean",
                "HexRealClosure/TowerReuse.lean",
                "adapters/HexRealClosureTheory/TowerReuse.lean",
                "HexRealClosure/TowerTransportTests.lean",
                "HexRealClosure/BaseInclusion.lean",
                "HexRealClosure/BaseInclusionTests.lean",
                "HexRealClosureTheory/BaseInterpretation.lean",
                "HexRealClosureTheory/BaseRealization.lean",
                "HexRealClosureTheory/BaseStagedRealization.lean",
                "HexRealClosureTheory/BaseProvider.lean",
                "HexRealClosure/BaseSubsequence.lean",
                "HexRealClosureTheory/BaseSubsequence.lean",
                "HexRealClosureTheory/BaseSubsequenceTests.lean",
                "HexRealClosureTheory/BaseMap.lean",
                "HexRealClosureTheory/BaseSubsequenceModels.lean",
                "HexRealClosureTheory/BaseStagedSubsequence.lean",
                "adapters/HexRealClosureTheory/BaseModel.lean",
                "HexRealClosureTheory/BasePrefixModels.lean",
                "HexRealClosureTheory/BaseModels.lean",
                "adapters/HexRealClosureTheory/BaseFactory.lean",
                "adapters/HexRealClosureTheory/BaseFactoryTests.lean",
                "adapters/HexRealClosureTheory/BaseGatherTests.lean",
                "adapters/HexRealClosureTheory/ContextModel.lean",
                "adapters/HexRealClosureTheory/CacheModels.lean",
                "adapters/HexRealClosureTheory/CacheRebuild.lean",
                "adapters/HexRealClosureTheory/CacheGather.lean",
                "adapters/HexRealClosureTheory/GatherTests.lean",
                "adapters/HexRealClosureTheory/SpecializeNested.lean",
                "adapters/HexRealClosureTheory/MonicEvaluation.lean",
                "adapters/HexRealClosureTheory/RegularEvaluation.lean",
                "adapters/HexRealClosureTheory/ModelEvaluation.lean",
                "adapters/HexRealClosureTheory/AlgebraicEvaluation.lean",
                "adapters/HexRealClosureTheory/SpecializeFractionRing.lean",
                "adapters/HexRealClosureTheory/CoefficientMap.lean",
                "adapters/HexRealClosureTheory/CoefficientQuery.lean",
                "adapters/HexRealClosureTheory/CoefficientTarski.lean",
                "adapters/HexRealClosureTheory/CoefficientEmbeddingTests.lean",
                "adapters/HexRealClosureTheory/CoefficientEmbedding.lean",
                "adapters/HexRealClosureTheory/CoefficientSelected.lean",
                "adapters/HexRealClosureTheory/CoefficientDescriptor.lean",
                "adapters/HexRealClosureTheory/CoefficientReplay.lean",
                "adapters/HexRealClosureTheory/CoefficientMoment.lean",
                "adapters/HexRealClosureTheory/CoefficientReduction.lean",
                "adapters/HexRealClosureTheory/SharedPresentation.lean",
                "adapters/HexRealClosureTheory/SharedPresentationTests.lean",
                "adapters/HexRealClosureTheory/BaseOrder.lean",
                "adapters/HexRealClosureTheory/BaseMapModel.lean",
                "HexRealClosure/TowerInclusion.lean",
                "HexRealClosure/LiveContext.lean",
                "HexRealClosure/LiveContextTests.lean",
                "adapters/HexRealClosureTheory/TowerInclusion.lean",
                "adapters/HexRealClosureTheory/LiveContext.lean",
                "HexRealClosure/TowerConversionTests.lean",
                "HexRealClosure/TowerPresentationTests.lean",
                "HexRealClosure/QueryReductionTests.lean",
                "adapters/HexRealClosureTheory/TowerTransport.lean",
                "adapters/HexRealClosureTheory/TowerTransportTests.lean",
                "HexRealClosure/BisectionTests.lean",
                "adapters/HexRealClosureTheory/Bisection.lean",
                "adapters/HexRealClosureTheory/BisectionRoots.lean",
                "conformance/HexRealClosure/BisectionFrontierTests.lean",
                "adapters/HexRealClosureTheory/BisectionFrontier.lean",
                "adapters/HexRealClosureTheory/BisectionCounts.lean",
                "adapters/HexRealClosureTheory/Isolation.lean",
                "conformance/HexRealClosure/IsolationTests.lean",
                "adapters/HexRealClosureTheory/BisectionFactor.lean",
                "adapters/HexRealClosureTheory/IsolationFactor.lean",
                "adapters/HexRealClosureTheory/IsolationRoots.lean",
                "conformance/HexRealClosure/RootPolicyConformance.lean",
                "conformance/HexRealClosure/IsolationConformance.lean",
                "conformance/HexRealClosureTheory/CoefficientSignsConformance.lean",
                "adapters/HexRealClosureTheory/RootOrder.lean",
                "HexRealClosure/RootOrderTests.lean",
                "HexRealClosure/RootFactorsTests.lean",
                "HexRealClosure/CompleteRoots.lean",
                "HexRealClosure/RootPolicyTests.lean",
                "adapters/HexRealClosureTheory/TowerRootPolicy.lean",
                "adapters/HexRealClosureTheory/RootPolicy.lean",
                "adapters/HexRealClosureTheory/IsolationPolicy.lean",
                "adapters/HexRealClosureTheory/IsolationTotal.lean",
                "adapters/HexRealClosureTheory/RootTotal.lean",
                "HexRealClosure/Trivial.lean",
                "HexRealClosure/TrivialTests.lean",
                "adapters/HexRealClosureTheory/Trivial.lean",
                "HexRealClosure/TrivialTower.lean",
                "HexRealClosure/TrivialTowerTests.lean",
                "HexRealClosure/TrivialChecks.lean",
                "conformance/HexRealClosure/TrivialConformance.lean",
                "adapters/HexRealClosureTheory/TrivialTower.lean",
                "adapters/HexRealClosureTheory/TrivialTowerTests.lean",
                "HexRealClosure/TowerRoots.lean",
                "HexRealClosure/TowerRootsTests.lean",
                "adapters/HexRealClosureTheory/TowerRoots.lean",
                "HexRealClosure/RootTransport.lean",
                "HexRealClosure/RootCollection.lean",
                "HexRealClosure/RootCollectionTests.lean",
                "HexRealClosure/Sample.lean",
                "HexRealClosure/SampleTests.lean",
                "HexRealClosure/LocalSampleTests.lean",
                "conformance/HexRealClosure/SampleConformance.lean",
                "adapters/HexRealClosureTheory/Sample.lean",
                "adapters/HexRealClosureTheory/SampleTests.lean",
                "adapters/HexRealClosureTheory/RootTransport.lean",
                "adapters/HexRealClosureTheory/RootCollection.lean",
                "adapters/HexRealClosureTheory/TowerCoverage.lean",
                "adapters/HexRealClosureTheory/TowerNaturality.lean",
                "adapters/HexRealClosureTheory/TowerEnlargeOrder.lean",
                "adapters/HexRealClosureTheory/TowerEnlargeOrderTests.lean",
                "HexRealClosure/TowerEnlargeOrderTests.lean",
                "HexRealClosure/TowerEnlargement.lean",
                "adapters/HexRealClosureTheory/RootFactors.lean",
                "HexRealClosure/TowerBytes.lean",
                "HexRealClosure/FrameRoundtrip.lean",
                "HexRealClosure/RootFormat.lean",
                "HexRealClosure/RootBytes.lean",
                "conformance/HexRealClosure/RootFormatConformance.lean",
                "conformance/HexRealClosure/BytesConformance.lean",
                "HexRealClosure/NumberField.lean",
                "adapters/HexRealClosureTheory/NumberField.lean",
                "conformance/HexRealClosure/NumberFieldConformance.lean",
                "HexRealClosure/NumberFieldTower.lean",
                "adapters/HexRealClosureTheory/NumberFieldTower.lean",
                "conformance/HexRealClosure/NumberFieldSamples.lean",
                "conformance/HexRealClosure/BasicConformance.lean")]
            qadjoin = root / "adapters/HexRealClosureTheory/QAdjoin.lean"
            qadjoin_tests = root / "HexRealClosure/QAdjoinTests.lean"
            dependency = root / "HexExtra/SelectedField.lean"
            arithmetic = [root / f"adapters/HexRealClosureTheory/{name}.lean"
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
            entry.write_text("public import HexRealRootsTheory.TarskiSoundness\n", encoding="utf-8")
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
                           "HexRealClosureTheory.LiveRequest", "HexRealClosureTheory.LiveRequestTests",
                           "HexRealClosureTheory.SharedRealization", "HexRealClosureTheory.SharedRealizationTests"):
                directory = root / ("adapters" if "Theory" in module else "")
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
                with self.assertRaisesRegex(ValueError, "unapproved admission in HexRealRootsTheory"):
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

                for library in ("HexSignDetTheory", "HexRealClosureTheory"):
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
                proof = root / "bench/HexSignDetTheory/ProofProbe/Injected.lean"
                proof.parent.mkdir(parents=True, exist_ok=True)
                proof.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                audit.check()
                proof.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in bench/HexSignDetTheory/ProofProbe"):
                    audit.check()
                for tactic in ("native_decide", "ofReduceBool"):
                    proof.write_text("theorem bad : True := by " + tactic + "\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unapproved admission in bench/HexSignDetTheory/ProofProbe"):
                        audit.check()
                proof.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                proof_shadow = root / "adapters/HexSignDetTheory/ProofProbe/Injected.lean"
                proof_shadow.parent.mkdir(parents=True, exist_ok=True)
                proof_shadow.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "proof-probe module .* is shadowed"):
                    audit.check()
                proof_shadow.unlink()
                proof.unlink()
                adapter_shadow = root / "HexSignDetTheory/RootProducer.lean"
                adapter_shadow.parent.mkdir(parents=True, exist_ok=True)
                adapter_shadow.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "adapter module .* is shadowed"):
                    audit.check()
                adapter_shadow.unlink()
                nested_adapter = root / "adapters/HexSignDetTheory/Nested/AnotherAdapter.lean"
                nested_adapter.parent.mkdir(exist_ok=True)
                nested_adapter.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unapproved admission in adapters/HexSignDetTheory/Nested/AnotherAdapter"):
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
