#!/usr/bin/env python3
"""Exercise ordinary-kernel replay on the actual serialized fixture and mutations."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
EXE = ["lake", "env", ".lake/build/bin/hexsigndet_kernel_replay_probe"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    args = parser.parse_args()
    results = args.results.resolve()
    results.mkdir(parents=True, exist_ok=True)
    outcomes = []
    started = time.monotonic()

    def run(label: str, arguments: list[str], *, code: int = 0,
            contains: tuple[str, ...] = (), absent: tuple[str, ...] = ()) -> None:
        process = subprocess.run(EXE + arguments, cwd=ROOT, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        (results / f"{label}.log").write_text(process.stdout)
        if process.returncode != code:
            raise RuntimeError(f"{label}: exit {process.returncode}, expected {code}; "
                               f"see {results / (label + '.log')}")
        if not all(marker in process.stdout for marker in contains):
            raise RuntimeError(f"{label}: missing expected diagnostic")
        if any(marker in process.stdout for marker in absent):
            raise RuntimeError(f"{label}: unexpected diagnostic")
        outcomes.append({"control": label, "exit_code": process.returncode})
        print(f"{label}: passed", flush=True)

    run("root", ["root"],
        contains=("rootLaws=2AuditedTheorems", "rootReconstructed=kernelAccepted children=2",
                  "rootReconstructedPackets=kernelAccepted",
                  "rootMissingStoredFacts=kernelRejected", "rootRejected=staleContext",
                  "rootRejected=copiedDerivatives", "rootRejected=unusedCount"))
    run("fact-operations", ["fact-operations"],
        contains=("factOperationsLaws=9AuditedTheorems",
                  "factOperations=kernelAccepted children=1",
                  "factOperationsPackets=kernelAccepted", "factOperationsMissing=lowerContext",
                  "factArithmetic=kernelAccepted children=5",
                  "factArithmeticPackets=kernelAccepted", "factArithmeticIncomplete=5MissingChildren",
                  "factMonic=kernelAccepted children=3", "factMonicPackets=kernelAccepted",
                  "factMonicMissing=3ExactLowerKeys",
                  "factMonicPacking=kernelAcceptedReducedRemainder", "factNonconstant=kernelAccepted",
                  "factNonconstantMissing=upperContextAndKey"))
    run("nested", ["nested"],
        contains=("nestedSelections=kernelAccepted children=2",
                  "nestedPacketReplay=kernelAccepted", "nestedMissingChild=unproved",
                  "nestedIncompleteChildren=unproved",
                  "nestedRejected=Hex.RealClosure.Algebraic.KernelReplay.Nested.wrongSign",
                  "nestedRejected=Hex.RealClosure.Algebraic.KernelReplay.Nested.wrongContext",
                  "nestedRejected=Hex.RealClosure.Algebraic.KernelReplay.Nested.wrongQuery",
                  "nestedRejected=Hex.RealClosure.Algebraic.KernelReplay.Nested.wrongCount",
                  "nestedChildProofs=theoremReferences", "nestedMalformedProof=kernelRejected",
                  "nestedIncompleteProof=rejected", "nestedRegistrationRollback=kernelRejected",
                  "nestedRejected=Hex.RealClosure.Algebraic.KernelReplay.Nested.wrongSelectedContext",
                  "nestedRejected=Hex.RealClosure.Algebraic.KernelReplay.Nested.wrongSelectedCount"))
    run("generated", ["generated"],
        contains=("generated=2 kernelAccepted=true", "generatedWrongSigns=kernelRejected",
                  "generatedDifferentQuery=kernelRejected", "generatedStaleContext=kernelRejected",
                  "generatedForgedCount=kernelRejected", "productionNanos=", "packetCheckNanos=",
                  "packetReplay=kernelAccepted", "forgedPacketReplay=normalRejection"))
    run("collect", ["collect"],
        contains=("collected=2 kernelAccepted=true", "incompleteInventory=missingEndpoint",
                  "zeroFuel=normalRejection", "irrelevantSupplier=boundedRejection",
                  "oneFuel=missingEndpoint", "falseGraph=checkedFalse",
                  "extraReorderedInventory=twoFacts", "malformedFact=kernelRejected",
                  "incompleteFact=rejected"))
    graph = results / "graph.json"
    run("emit", ["emit", str(graph)])
    if len(graph.read_bytes()) != 4093 or hashlib.sha256(graph.read_bytes()).hexdigest() != \
            "f2715c4e52f116270b4189cc5e1010cc69363d8438892d38c3073d976f5a9604":
        raise RuntimeError("serialized fixture changed")
    run("exact-record", ["bytes-equal", str(graph)],
        contains=("kernelAccepted=true", "result=true"))
    run("full", ["bytes", str(graph), "full", "true"],
        contains=("kernelAccepted=true", "result=true"))
    run("full-bound", ["bytes-bound", str(graph), "full", "true"],
        contains=("inputBinding=proved", "inputBinding=used decoderEquation=used",
                  "kernelAccepted=true", "result=true"))
    run("missing", ["bytes-bound", str(graph), "missing", "unproved"],
        contains=("inputBinding=proved", "inputBinding=used decoderEquation=used",
                  "missingRedex=", "result=unproved"))

    encoded = json.loads(graph.read_text())
    if encoded[:2] != [1, 1] or len(encoded[2]) != 2 or encoded[2][0][0][6][2] != [1]:
        raise RuntimeError("unexpected fixture count layout")
    encoded[2][0][0][6][2][0] = 2
    bad_count = results / "bad-count.json"
    bad_count.write_text(json.dumps(encoded, separators=(",", ":")))
    run("count-decodes", ["bytes-read", str(bad_count), "full", "true"],
        contains=("kernelAccepted=true", "result=true"))
    run("count-rejected", ["bytes", str(bad_count), "full", "false"],
        contains=("kernelAccepted=true", "result=false"))
    run("binding-rejected", ["bytes-bound", str(bad_count), "missing", "unproved"],
        code=1, contains=("literal input binding failed",),
        absent=("inputBinding=proved", "result=unproved"))

    encoded = json.loads(graph.read_text())
    if encoded[2][0][0][0] != 8:
        raise RuntimeError("unexpected fixture context layout")
    encoded[2][0][0][0] = 9
    stale = results / "stale-context.json"
    stale.write_text(json.dumps(encoded, separators=(",", ":")))
    run("context-rejected", ["bytes", str(stale), "full", "false"],
        contains=("kernelAccepted=true", "result=false"))
    run("unknown-control", ["complete", "unknown"], code=1,
        contains=("unknown control name",))
    (results / "results.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    print(f"harness_seconds={time.monotonic() - started:.3f}", flush=True)


if __name__ == "__main__":
    main()
