#!/usr/bin/env python3
"""Measure fresh applications of the proved Sturm–Tarski semantic bridge.

Pair the semantic replay module with its exact import-only baseline in
adjacent alternating AB/BA order. The module includes rational, noncanonical,
and integer/dyadic certificates and audits each result's kernel axioms.
This measures application of the imported foundation, not its initial build.
"""
from __future__ import annotations

import sys
import json
import shutil
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_cli, parse_args, environment, default_output,
    source_hashes,
)

SPEC = SweepSpec(
    description=__doc__ or "Sturm–Tarski semantic replay proof sweep",
    pairs=(ProbePair(
        "semantics",
        # Both imports replay Accepted's visible ordinary-axiom diagnostics.
        ProbeModule("HexSturmMathlib.Replay.SemanticsBaseline",
                    ("propext", "Classical.choice", "Quot.sound")),
        ProbeModule("HexSturmMathlib.Replay.Semantics",
                    ("propext", "Classical.choice", "Quot.sound")),
        {"family": "literal-query-semantics", "degree": 2,
         "scope": "kernel replay and mathematical root-sum interpretation"},
    ),),
    probe_target="HexConformance",
    src_dir=Path("conformance"),
    schema="hex-sturm-mathlib-semantic-probes-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sturm-semantics",
    required_samples=4,
    retain_compiler_output=True,
)

def main() -> int:
    args = parse_args(SPEC.description, default_samples=SPEC.required_samples or 4)
    env = environment()
    output = args.output or default_output(env, SPEC.output_stem)
    if not output.is_absolute():
        output = ROOT / output
    sidecar = Path(str(output) + ".samples.jsonl")
    if output.exists() or sidecar.exists():
        raise RuntimeError("measurement output exists; choose a fresh path")
    # Persist completed samples before pair validation, including failed runs.
    with tempfile.NamedTemporaryFile(mode="w", prefix="hex-sturm-semantics-",
                                     suffix=".jsonl", delete=False) as log:
        retained = Path(log.name)
        print(f"Incremental samples: {retained}", flush=True)
        log.write(json.dumps({"type": "metadata", "environment": env,
                              "source_sha256": source_hashes(SPEC, Path(__file__))}) + "\n")
        log.flush()

        def observe(module, sample):
            log.write(json.dumps({"type": "sample", "module": module, **sample}) + "\n")
            log.flush()

        try:
            code = run_cli(SPEC, Path(__file__), sample_observer=observe)
        except BaseException:
            print(f"Retained partial samples: {retained}", file=sys.stderr)
            raise
    sidecar.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(retained, sidecar)
    return code


if __name__ == "__main__":
    sys.exit(main())
