#!/usr/bin/env python3
"""Audit adapter, sign-determination and real-closure companion conformance cones.

RCF conformance (including intentional negative admission probes) and Sturm
semantic replay conformance remain kernel-checked tests outside this source
scan; the message below reports only the scanned cones.
"""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BRIDGE = Path("HexRealRootsTheory/TarskiSoundness.lean")
ADMISSION = re.compile(
    r"\b[A-Za-z_]*[sS]orry[A-Za-z_]*\b|\b(?:admit|admitGoal|axiom|native_decide|ofReduceBool)\b|^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*constant\b(?!\s*:)|(?<!\.)\bstop\b(?!\s*:=)",
    re.MULTILINE,
)
IMPORT = re.compile(r"\bimport\s+(?:all\s+)?(\S+)")
EXTERNAL = {"Batteries", "Mathlib", "Lean", "Init", "Std", "Lake", "Qq", "Verso", "TauCeti"}


def code_only(source: str) -> str:
    """Mask Lean comments and strings while retaining source positions."""
    result: list[str] = []
    depth = 0
    quoted = False
    raw = False
    i = 0
    while i < len(source):
        pair = source[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\" and not raw and i + 1 < len(source):
                result.extend("  ")
                i += 2
            elif source[i] == '"':
                quoted = False
                raw = False
                result.append(" ")
                i += 1
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                result.extend(" " * (len(source) - i))
                break
            result.extend(" " * (end - i))
            i = end
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif source[i] == "'":
            if i > 0 and (source[i - 1].isalnum() or source[i - 1] == "_"):
                result.append(source[i])
                i += 1
                continue
            # Lean character literals include escaped quotes such as '\"'.
            end = i + 1
            if end < len(source) and source[end] == "\\":
                end += 1
            if end + 1 < len(source) and source[end + 1] == "'":
                result.extend(" " * (end + 2 - i))
                i = end + 2
            else:
                result.append(source[i])
                i += 1
        elif source[i] == '"':
            hash_start = i - 1
            while hash_start >= 0 and source[hash_start] == "#":
                hash_start -= 1
            if hash_start < i - 1 and hash_start >= 0 and source[hash_start] == "r" and (
                hash_start == 0 or not source[hash_start - 1].isalnum()
            ):
                delimiter = '"' + source[hash_start + 1:i]
                end = source.find(delimiter, i + 1)
                if end < 0:
                    raise ValueError("unterminated raw string")
                result.extend("\n" if c == "\n" else " " for c in source[i:end + len(delimiter)])
                i = end + len(delimiter)
                continue
            if i > 0 and source[i - 1] == "!":
                # Interpolation can elaborate arbitrary terms. Scan the whole
                # literal, including braces and nested strings, before masking.
                end = interpolation_end(source, i)
                if re.search(r"(?i)sorry|admit|\bstop\b|\baxiom\b", source[i + 1:end]):
                    raise ValueError("admission inside an interpolated string")
                result.extend("\n" if c == "\n" else " " for c in source[i:end + 1])
                i = end + 1
                continue
            quoted = True
            raw = i > 0 and source[i - 1] == "r" and (i == 1 or not source[i - 2].isalnum())
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def interpolation_end(source: str, quote: int) -> int:
    """Find the outer quote, respecting escapes and nested interpolation text."""
    braces = 0
    inner = False
    i = quote + 1
    while i < len(source):
        c = source[i]
        if c == "\\":
            i += 2
            continue
        if c == '"':
            if braces == 0:
                return i
            inner = not inner
        elif not inner:
            if c == "{":
                braces += 1
            elif c == "}" and braces:
                braces -= 1
        i += 1
    raise ValueError("unterminated interpolated string")


def module_file(module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "adapters", ROOT / "conformance", ROOT / "bench",
                 ROOT / "experiments", ROOT / "examples"):
        candidate = base / relative
        if candidate.is_file():
            return candidate
    return None


def import_cones(starts: list[str]) -> set[Path]:
    """Traverse a union once; shared dependencies retain all audit obligations."""
    pending = list(starts)
    seen: set[str] = set()
    paths: set[Path] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_file(module)
        if path is None:
            if module.split(".", 1)[0] not in EXTERNAL:
                raise ValueError(f"missing local import {module}")
            continue
        paths.add(path.relative_to(ROOT))
        pending.extend(match.group(1) for match in IMPORT.finditer(
            code_only(path.read_text(encoding="utf-8"))))
    return paths


def find_admissions(source: str) -> list[re.Match[str]]:
    """Do not mistake Expr's admission detector for an admission constructor.

    The dotted `hasSorry` detector and `Term.withoutErrToSorry` guard do not
    produce admissions. The latter disables conversion of elaboration errors
    to admissions. Admission-producing APIs and bare identifiers stay forbidden.
    """
    return [match for match in ADMISSION.finditer(source) if not (
        (match.group() == "hasSorry" and match.start() > 0
         and source[match.start() - 1] == ".") or
        (match.group() == "withoutErrToSorry" and
         re.search(r"(?:^|[^A-Za-z0-9_.])(?:Lean\.Elab\.)?Term\.$", source[:match.start()]))
    )]


def check() -> None:
    if module_file("HexRCF.RealCoefficients") is None:
        raise ValueError("the optional rcf adapter module is missing")
    roots = ["HexRealClosureTheory.FiniteData", "HexRealClosureTheory.FiniteSupport",
             "HexRealClosureTheory.FiniteOperands", "HexRealClosureTheory.FiniteLift",
             "HexRealClosureTheory.FiniteScalars", "HexRealClosureTheory.FiniteBase",
             "HexRealClosureTheory.FiniteDependencies", "HexRealClosureTheory.FiniteConditions",
             "HexRealClosureTheory.FiniteReconstruction", "KernelReplay.FiniteReconstruction",
             "KernelReplay.FiniteThomWitness", "KernelReplay.FiniteThomJoint",
             "HexRealClosureTheory.FiniteChain", "KernelReplay.FiniteChain",
             "HexRealClosureTheory.NativePackets", "KernelReplay.NativePackets",
             "HexRealClosureTheory.NativeModels", "KernelReplay.NativeModels",
             "HexRealClosureTheory.SignReplay", "HexRealClosure.RecordOperations",
             "HexRealClosureTheory.NativeReplay", "KernelReplay.NativeReplay",
             "HexRealClosure.RecordQueries", "HexRealClosure.InversePackets", "HexRealClosureTheory.NativeValues",
             "HexRealClosureTheory.NativeRecords", "HexRealClosureTheory.NativeFactory",
             "KernelReplay.NativeValues", "KernelReplay.NativeFactory",
             "HexRealClosure.ChildPackets", "HexRealClosureTheory.NativeCodecs",
             "KernelReplay.NativeChildren",
             "HexRealClosure.RecordReaders", "HexRealClosure.QueryOperations",
             "HexRealClosureTheory.NativeReaders", "KernelReplay.NativeReaders",
             "HexRealClosureTheory.NativeAssembly", "HexRealClosureTheory.NativeAssemblyModels",
             "KernelReplay.NativeAssembly", "KernelReplay.NativeAssemblyModels",
             "KernelReplay.NativeAssemblyStaged", "KernelReplay.NativeAssemblyUse",
             "KernelReplay.FiniteDependencies",
             "KernelReplay.LookupReplay",
             "KernelReplay.ProofAudit",
             "KernelReplay.AxiomClosure", "KernelReplay.AxiomClosureTest",
             "KernelReplay.AxiomClosureImports", "KernelReplay.SupportAudit",
             "KernelReplay.FiniteRange",
             "KernelReplay.CoefficientMembers", "KernelReplay.CoefficientEntry",
             "KernelReplay.FiniteBase", "KernelReplay.BaseLookup", "KernelReplay.FiniteLift", "KernelReplay.FiniteOperands",
             "KernelReplay.FiniteSupport", "KernelReplay.FiniteData", "KernelReplay.FiniteWitness", "KernelReplay.FiniteJoint",
             "RealClosureConsumer.Query", "RealClosureConsumer.Sign",
             "RealClosureConsumer.Ordered", "RealClosureConsumer.Tower",
             "HexRCF.RealCoefficients", "HexRCF.SignDetFieldProofs",
             "HexSignDet.FieldChecks", "HexSignDetTheory", "HexRealClosure.BaseTests",
             "HexRealClosure.QAdjoinTests", "HexRealClosure.NumberField",
             "HexRealClosureTheory.NumberField", "HexRealClosure.NumberFieldConformance",
             "HexRealClosure.NumberFieldTower", "HexRealClosureTheory.NumberFieldTower",
             "HexRealClosure.NumberFieldSamples", "HexRealClosure.BasicConformance",
             "HexRealClosure.RiobooConformance",
             "HexRealClosure.StrzConformance",
             "HexRealClosure.TowerCatalog", "HexRealClosure.TowerTests",
             "HexRealClosure.TowerBytes", "HexRealClosure.BytesConformance",
             "HexRealClosure.FrameRoundtrip", "HexRealClosure.RootFormat",
             "HexRealClosure.RootBytes", "HexRealClosure.RootFormatConformance",
             "HexRealClosure.ReprFormat", "HexRealClosure.TowerRepr",
             "HexRealClosure.ReprConformance", "HexRealClosure.ReprChecks",
             "HexRealClosure.RootFrame", "HexRealClosure.RootFrameTests",
             "HexRealClosure.FrameFormat", "HexRealClosure.FrameFormatTests",
             "HexRealClosure.TowerOrder", "HexRealClosure.TowerOrderTests",
             "HexRealClosureTheory.TowerModel", "HexRealClosureTheory.TowerModelTests",
             "HexRealClosureTheory.TowerAlgebraic",
             "HexRealClosureTheory.TowerYun", "HexRealClosure.TowerYunTests",
             "HexRealClosureTheory.TowerRefinement", "HexRealClosure.TowerRefinement",
             "HexRealClosure.TowerPolynomial", "HexRealClosure.TowerRefinementTests",
             "HexRealClosure.TowerTransport", "HexRealClosure.TowerTransportTests",
             "HexRealClosure.TowerReuse", "HexRealClosureTheory.TowerReuse",
             "HexRealClosure.BaseInclusion", "HexRealClosure.BaseInclusionTests",
             "HexRealClosure.TowerInclusion", "HexRealClosure.LiveContext",
             "HexRealClosure.LiveContextTests",
             "HexRealClosure.LiveRequest", "HexRealClosure.LiveRequestTests",
             "HexRealClosureTheory.LiveRequest", "HexRealClosureTheory.LiveRequestTests",
             "HexRealClosureTheory.SharedRealization", "HexRealClosureTheory.SharedRealizationTests",
             "HexRealClosureTheory.TowerInclusion", "HexRealClosureTheory.LiveContext",
             "HexRealClosure.TowerConversionTests", "HexRealClosure.TowerPresentationTests",
             "HexRealClosure.QueryReductionTests",
             "HexRealClosureTheory.TowerTransport", "HexRealClosureTheory.TowerTransportTests",
             "HexRealClosureTheory.BaseTests", "HexRealClosure.BaseCatalogTests",
             "HexRealClosureTheory.ReprProviderData", "HexRealClosureTheory.ReprProviderTests",
             "HexRealClosureTheory.BaseInterpretation", "HexRealClosureTheory.BaseRealization",
             "HexRealClosureTheory.BaseStagedRealization",
             "HexRealClosureTheory.BaseProvider",
             "HexRealClosure.BaseSubsequence", "HexRealClosureTheory.BaseSubsequence",
             "HexRealClosure.BaseEvaluate", "HexRealClosure.BaseEvaluateTests",
             "HexRealClosure.BaseTower", "HexRealClosure.BasePresentation",
             "HexRealClosure.BasePermutation", "HexRealClosure.BasePermutationTotal",
             "HexRealClosure.BaseReconciliation", "HexRealClosureTheory.BaseReconciliationModel",
             "HexRealClosureTheory.BaseReconstruction", "HexRealClosureTheory.BaseReconstructionTests",
             "HexRealClosure.BaseReconciliationTests",
             "HexRealClosure.BasePermutationTests", "HexRealClosure.BaseStagedReorder",
             "HexRealClosureTheory.BaseStagedReorder",
             "HexRealClosureTheory.BaseStagedReorderTests",
             "HexRealClosureTheory.BasePermutation",
             "HexRealClosureTheory.BaseSubsequenceTests",
             "HexRealClosureTheory.BaseMap", "HexRealClosureTheory.BaseSubsequenceModels",
             "HexRealClosureTheory.BaseStagedSubsequence",
             "HexRealClosureTheory.BaseModel",
             "HexRealClosureTheory.BasePrefixModels", "HexRealClosureTheory.BaseModels",
             "HexRealClosureTheory.BaseFactory", "HexRealClosureTheory.ContextModel",
             "HexRealClosureTheory.BaseFactoryTests", "HexRealClosureTheory.BaseGatherTests",
             "HexRealClosureTheory.CacheModels", "HexRealClosureTheory.CacheRebuild",
             "HexRealClosureTheory.CacheGather", "HexRealClosureTheory.GatherTests",
             "HexRealClosure.ReconciledGather", "HexRealClosure.ReconciledGatherTests",
             "HexRealClosureTheory.ReconciledContext", "HexRealClosureTheory.OwnerReader",
             "HexRealClosureTheory.ReconciledGatherModel", "HexRealClosureTheory.ReconciledGatherTests",
             "HexRealClosure.ReconciledLive", "HexRealClosureTheory.ReconciledLive",
             "HexRealClosureTheory.ReconciledEnlargementTests",
             "HexRealClosureTheory.ReconciledRealization", "HexRealClosureTheory.ReconciledRealizationTests",
             "HexRealClosure.ReconciledBase", "HexRealClosure.ReconciledBaseTests",
             "HexRealClosureTheory.ReconciledCatalog", "HexRealClosureTheory.ReconciledCatalogTests",
             "HexRealClosureTheory.SharedPresentation", "HexRealClosureTheory.SharedPresentationTests",
             "HexRealClosureTheory.BaseOrder", "HexRealClosureTheory.BaseMapModel",
             "HexRealClosure.BisectionTests", "HexRealClosure.DeflationConformance",
             "HexRealClosure.BisectionFrontierTests", "HexRealClosure.IsolationTests",
             "HexRealClosure.RootPolicyConformance", "HexRealClosure.IsolationConformance", "HexRealClosure.RootOrderTests",
             "HexRealClosure.RootFactorsTests", "HexRealClosureTheory.Bisection",
             "HexRealClosureTheory.BisectionRoots", "HexRealClosureTheory.BisectionFrontier",
             "HexRealClosureTheory.BisectionCounts", "HexRealClosureTheory.Isolation",
             "HexRealClosureTheory.BisectionFactor", "HexRealClosureTheory.IsolationFactor",
             "HexRealClosureTheory.IsolationRoots", "HexRealClosureTheory.RootOrder",
             "HexRealClosureTheory.RootFactors", "HexRealClosure.CompleteRoots",
             "HexRealClosure.RootPolicyTests", "HexRealClosureTheory.TowerRootPolicy", "HexRealClosureTheory.RootPolicy", "HexRealClosureTheory.IsolationPolicy", "HexRealClosureTheory.IsolationTotal", "HexRealClosureTheory.RootTotal",
             "HexRealClosure.Trivial", "HexRealClosure.TrivialTests",
             "HexRealClosureTheory.Trivial", "HexRealClosure.TrivialTower",
             "HexRealClosure.TrivialChecks", "HexRealClosure.TrivialTowerTests", "HexRealClosure.TrivialConformance", "HexRealClosureTheory.TrivialTower",
             "HexRealClosureTheory.TrivialTowerTests",
             "HexRealClosure.TowerRoots", "HexRealClosure.TowerRootsTests",
             "HexRealClosureTheory.TowerRoots",
             "HexRealClosure.RootTransport", "HexRealClosureTheory.RootTransport",
             "HexRealClosure.RootCollection", "HexRealClosureTheory.RootCollection",
             "HexRealClosure.RootCollectionTests",
             "HexRealClosure.Sample", "HexRealClosure.SampleTests", "HexRealClosureTheory.Sample",
             "HexRealClosureTheory.SampleTests", "HexRealClosure.LocalSampleTests",
             "HexRealClosure.SampleConformance",
             "HexRealClosureTheory.TowerCoverage",
             "HexRealClosureTheory.TowerNaturality",
             "HexRealClosureTheory.TowerEnlargeOrder",
             "HexRealClosureTheory.TowerEnlargeOrderTests",
             "HexRealClosure.TowerEnlargeOrderTests",
             "HexRealClosure.TowerEnlargement",
             "HexRealClosureTheory.Specialize",
             "HexRealClosureTheory.SpecializePolynomial",
             "HexRealClosureTheory.SpecializeRegular", "HexRealClosureTheory.SpecializeQuery", "HexRealClosureTheory.SpecializeTarski",
             "HexRealClosureTheory.SpecializeReduction", "HexRealClosureTheory.SpecializeMoment",
             "HexRealClosureTheory.SpecializeReplay", "HexRealClosureTheory.SpecializeSample", "HexRealClosureTheory.SpecializeSelected", "HexRealClosureTheory.SpecializeDescriptor",
             "HexRealClosureTheory.SpecializeNested",
             "HexRealClosureTheory.MonicEvaluation",
             "HexRealClosureTheory.RegularEvaluation",
             "HexRealClosureTheory.ModelEvaluation",
             "HexRealClosureTheory.AlgebraicEvaluation",
             "HexRealClosureTheory.SpecializeFractionRing",
             "HexRealClosureTheory.CoefficientMap",
             "HexRealClosureTheory.CoefficientQuery",
             "HexRealClosureTheory.CoefficientTarski",
             "HexRealClosureTheory.CoefficientEmbeddingTests",
             "HexRealClosureTheory.CoefficientEmbedding",
             "HexRealClosureTheory.CoefficientSelected",
             "HexRealClosureTheory.CoefficientDescriptor",
             "HexRealClosureTheory.CoefficientReplay",
             "HexRealClosureTheory.CoefficientMoment",
             "HexRealClosureTheory.CoefficientReduction",
             "HexRealClosureTheory.TransportPolynomial", "HexRealClosureTheory.TransportProduct",
             "HexRealClosureTheory.TransportArithmetic", "HexRealClosureTheory.TransportQuery", "HexRealClosureTheory.TransportTests",
             "HexRealClosureTheory.TransportRing", "HexRealClosureTheory.TransportPower",
             "HexRealClosureTheory.TransportTarski", "HexRealClosureTheory.TransportClosed",
             "HexRealClosureTheory.TransportClosedQuery", "HexRealClosureTheory.TransportClosedReduction",
             "HexRealClosureTheory.TransportPreparation", "HexRealClosureTheory.TransportMoment",
             "HexRealClosureTheory.TransportReplay", "HexRealClosureTheory.TransportSample", "HexRealClosureTheory.TransportDescriptor",
             "HexRealClosureTheory.TransportSelected", "HexRealClosureTheory.TransportFiniteTests", "HexRealClosureTheory.TransportRegular",
             "HexRealClosureTheory.TransportReduction",
             "HexRealClosureTheory.SpecializeTests", "HexRealClosureTheory.Algebraic",
             "HexRealClosureTheory.AlgebraicClean", "HexRealClosureTheory.AlgebraicValue",
             "HexRealClosureTheory.AlgebraicTransport", "HexRealClosureTheory.PackingQuery", "HexRealClosureTheory.PackingMoment", "HexRealClosureTheory.PackingReduction", "HexRealClosureTheory.PackingReplay", "HexRealClosureTheory.FiniteRead", "HexRealClosureTheory.BaseFinite", "HexRealClosureTheory.PackingInventory", "HexRealClosureTheory.BaseFiniteReplay", "HexRealClosureTheory.PackingNext", "HexRealClosureTheory.AlgebraicYun",
             "HexRealClosureTheory.AlgebraicReencode",
             "HexRealClosureTheory.CoefficientSignsConformance",
             "HexRealClosure.AlgebraicReencodeTests",
             "HexRealClosureTheory.AlgebraicRoots",
             "HexRealClosureTheory.BaseClean", "HexRealClosureTheory.AlgebraicTower",
             "HexRealClosureTheory.Union", "HexRealClosureTheory.UnionTests",
             "HexRealClosure.InverseEquation", "HexRealClosureTheory.InverseEquation",
             "HexRealClosureTheory.SuppliedInverse",
             "HexRealClosureTheory.QAdjoin", "HexRCF.GatherCellsConformance",
             "HexRCF.AlgebraicCellsConformance", "HexRCF.AlgebraicPreparationConformance",
             "HexRCF.AlgebraicCellsStress"] + [
        ".".join(path.relative_to(ROOT / "adapters").with_suffix("").parts)
        for path in sorted((ROOT / "adapters").rglob("*.lean"))] + [
        ".".join(path.relative_to(ROOT / "conformance").with_suffix("").parts)
        for library in ("HexRCF/NestedTransport", "HexRCF/FiniteMatrix", "HexRCF/CellReplay", "HexSignDetTheory", "HexRealClosureTheory")
        for path in sorted((ROOT / "conformance" / library).rglob("*.lean"))] + [
        ".".join(path.relative_to(ROOT / "bench").with_suffix("").parts)
        for path in sorted((ROOT / "bench" / "HexSignDetTheory" / "ProofProbe").rglob("*.lean"))]
    # Named roots remain mandatory; the glob also audits unnamed conformance
    # modules, including their own declarations and imported dependencies.
    roots = list(dict.fromkeys(roots))
    for path in sorted((ROOT / "adapters").rglob("*.lean")):
        module = ".".join(path.relative_to(ROOT / "adapters").with_suffix("").parts)
        if module_file(module) != path:
            raise ValueError(f"adapter module {module} is shadowed by another source file")
    for library in ("HexRCF/NestedTransport", "HexRCF/FiniteMatrix", "HexRCF/CellReplay", "HexSignDetTheory", "HexRealClosureTheory"):
        for path in sorted((ROOT / "conformance" / library).rglob("*.lean")):
            module = ".".join(path.relative_to(ROOT / "conformance").with_suffix("").parts)
            if module_file(module) != path:
                raise ValueError(f"conformance module {module} is shadowed by another source file")
    for path in sorted((ROOT / "bench" / "HexSignDetTheory" / "ProofProbe").rglob("*.lean")):
        module = ".".join(path.relative_to(ROOT / "bench").with_suffix("").parts)
        if module_file(module) != path:
            raise ValueError(f"proof-probe module {module} is shadowed by another source file")
    paths = import_cones(roots)
    if BRIDGE not in paths:
        raise ValueError(f"the optional adapter no longer imports {BRIDGE}")
    for relative in sorted(paths):
        source = code_only((ROOT / relative).read_text(encoding="utf-8"))
        admissions = find_admissions(source)
        if admissions:
            line = source.count("\n", 0, admissions[0].start()) + 1
            raise ValueError(f"unapproved admission in {relative}:{line}")
    print(f"{len(roots)} scanned adapter/conformance import cones: "
          f"{len(paths)} local modules, no admissions in these cones")


if __name__ == "__main__":
    try:
        check()
    except ValueError as error:
        raise SystemExit(str(error)) from error
