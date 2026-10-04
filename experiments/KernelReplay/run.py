#!/usr/bin/env python3
"""Exercise ordinary-kernel replay on the actual serialized fixture and mutations."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
EXE = ["lake", "env", ".lake/build/bin/hexsigndet_kernel_replay_probe"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    args = parser.parse_args()
    results = args.results.resolve()
    results.mkdir(parents=True, exist_ok=True)
    outcomes = []

    def run(label: str, arguments: list[str], *, code: int = 0,
            contains: tuple[str, ...] = ()) -> None:
        process = subprocess.run(EXE + arguments, cwd=ROOT, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (results / f"{label}.log").write_text(process.stdout)
        if process.returncode != code:
            raise RuntimeError(f"{label}: exit {process.returncode}, expected {code}; "
                               f"see {results / (label + '.log')}")
        if not all(marker in process.stdout for marker in contains):
            raise RuntimeError(f"{label}: missing expected diagnostic")
        outcomes.append({"control": label, "exit_code": process.returncode})
        print(f"{label}: passed", flush=True)

    graph = results / "graph.json"
    run("emit", ["emit", str(graph)])
    run("controls", [], contains=("result=true", "result=false", "missingRedex="))
    run("exact-record", ["bytes-equal", str(graph)],
        contains=("kernelAccepted=true", "result=true"))
    run("full", ["bytes", str(graph), "full", "true"],
        contains=("kernelAccepted=true", "result=true"))
    run("missing", ["bytes-bound", str(graph), "missing", "unproved"],
        contains=("inputBinding=proved", "missingRedex=", "result=unproved"))

    encoded = json.loads(graph.read_text())
    assert encoded[:2] == [1, 1] and len(encoded[2]) == 2
    assert encoded[2][0][0][6][2] == [1]
    encoded[2][0][0][6][2][0] = 2
    bad_count = results / "bad-count.json"
    bad_count.write_text(json.dumps(encoded, separators=(",", ":")))
    run("count-decodes", ["bytes-read", str(bad_count), "full", "true"],
        contains=("kernelAccepted=true", "result=true"))
    run("count-rejected", ["bytes", str(bad_count), "full", "false"],
        contains=("kernelAccepted=true", "result=false"))
    run("binding-rejected", ["bytes-bound", str(bad_count), "missing", "unproved"],
        code=1)

    encoded = json.loads(graph.read_text())
    assert encoded[2][0][0][0] == 8
    encoded[2][0][0][0] = 9
    stale = results / "stale-context.json"
    stale.write_text(json.dumps(encoded, separators=(",", ":")))
    run("context-rejected", ["bytes", str(stale), "full", "false"],
        contains=("kernelAccepted=true", "result=false"))
    run("unknown-control", ["complete", "unknown"], code=1,
        contains=("unknown control name",))
    (results / "results.json").write_text(json.dumps(outcomes, indent=2) + "\n")


if __name__ == "__main__":
    main()
