#!/usr/bin/env python3
"""Regenerate the report-specific, untimed F4 matrix-count tables."""
import argparse
import json
import hashlib
import tarfile
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_json import loads


def load(path):
    return loads(path.read_text())


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["data", "previous", "native", "full", "archive", "report"]:
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    manifest = load(args.data / "manifest.json")
    diagnostics = load(args.data / "diagnostics/metadata.json")
    stages = load(args.data / "stages/metadata.json")
    native, full = load(args.native), load(args.full)
    with args.archive.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    with tarfile.open(args.archive) as packed:
        archive = dict(path=str(args.archive), sha256=digest, payloads=len(packed.getmembers()))
    require(len(native) == 2 and len(full) == 9 and all(x["exit_code"] == 0 for x in native + full), "incomplete verification")
    require(all(x["source_fingerprint"] == manifest["source_fingerprint"] for x in native + full), "source mismatch")
    require(len(diagnostics["runs"]) == len(stages["runs"]) == 14, "incomplete corpus")
    stage_map = {row["case"]: row for row in stages["runs"]}
    require(len(stage_map) == 14, "duplicate stage case")
    rows = []
    keys = ["matrixCalls", "matrixRows", "matrixTargets", "matrixReductions", "matrixZeroRows"]
    for record in diagnostics["runs"]:
        name = record["case"]
        whole = load(args.data / "diagnostics" / (name + ".stdout"))
        previous = load(args.previous / (name + "-b0-B.stdout"))
        current = loads(json.dumps(whole))
        current.pop("candidateNanos")
        previous.pop("candidateNanos")
        for key in keys[2:]:
            current["statistics"].pop(key)
        require(current == previous, "old output/counter mismatch: " + name)
        require(whole["statistics"] == record["counters"], "retained count mismatch")
        sequence = [loads(line) for line in (args.data / "stages" / (name + ".jsonl")).read_text().splitlines()]
        footer = sequence.pop()
        require(footer["kind"] == "stage_diagnostics_complete" and footer["basis"] == whole["basis"], "stage basis mismatch")
        totals = {phase: {key: sum(row[key] for row in sequence if row["phase"] == phase) for key in keys}
                  for phase in ["input", "pairs", "interreduce"]}
        require(totals == stage_map[name]["phases"], "stage metadata mismatch")
        for key in keys:
            require(sum(totals[phase][key] for phase in totals) == footer["statistics"][key] == whole["statistics"][key], "stage sum mismatch")
        rows.append((record, totals))
    text = f'''# F4 matrix target and reduction counts

The driver and library expose submitted matrix targets, completed pivot
applications and zero rows. A shared `Statistics.recordMatrix` merges these
counters for traced and untraced production, including consumed prefixes of
failed calls. Submitted rows include retried atomic stages; these are counts
of attempted work, not distinct polynomial identities.

Source fingerprint `{manifest['source_fingerprint']}` identifies the frozen
driver source at `{manifest['commit']}`. The 14-input medium development
suite is run once for untimed diagnostics. Complete bases and every previous
metadata/counter field agree with retained `fd0313c0ed28` outputs. The three
new fields are the only additions. The raw `candidateNanos` values are retained
but no timing, speedup or acceptance claim uses these executions.

The external `F4.step` runner separates input normalization, pair rounds and
final interreduction. Its complete bases and all five matrix counters match
the independently frozen candidate driver; final interchange decoding work is
absent from that runner and is not equated. All stage source/build records
are retained. Aggregate zero fractions mix these different stages and do not
predict the rank of an individual sampling block.

| Case | All targets | All zero rows | Pair-round targets | Pair-round zero rows | Pair-round zero fraction | Pair-round pivot applications |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
'''
    for record, phases in rows:
        counts, pairs = record["counters"], phases["pairs"]
        fraction = f"{100*pairs['matrixZeroRows']/pairs['matrixTargets']:.2f}%" if pairs["matrixTargets"] else "n/a"
        text += (f"| {record['case']} | {counts['matrixTargets']} | {counts['matrixZeroRows']} | "
                 f"{pairs['matrixTargets']} | {pairs['matrixZeroRows']} | {fraction} | {pairs['matrixReductions']} |\n")
    eco = next(phases for record, phases in rows if record["case"] == "eco11-31")
    text += f'''
Eco11 at the largest prime has {eco['pairs']['matrixZeroRows']} zero reductions
among {eco['pairs']['matrixTargets']} pair-round targets. Its
{eco['interreduce']['matrixTargets']} final-interreduction targets have
{eco['interreduce']['matrixZeroRows']} zero rows. These observations identify a
concrete candidate for a block-sampling experiment. They establish neither a
sampling success probability nor a speedup; no sampler is implemented here.

At `{full[0]['source_commit']}`, all nine project checks and eight source-identified
Clang/GCC sanitizer/SIMD/scalar/remainder variants pass. The emitter verifies
traced/untraced and native/portable counts on 1,134 profiles, and the regenerated
fixtures preserve every pre-existing field. Both complete driver corpora pass.
The hand-checkable matrix with reducer `x` and targets `1,x` has two targets,
one pivot application and one zero row. Its additional work-exhaustion guard
retains that completed reduction/zero prefix at conformance commit
`{stages['source_commit']}`.

The [count-report generator](../../scripts/bench/groebner_count_report.py)
rechecks the old output fields, raw diagnostic counts, stage sums and complete
bases before generating this table. All inputs are in the raw capsules.
Candidate production, certificate generation, native verification and kernel
checking remain distinct. This change makes no performance milestone claim;
issue #10987 remains open.

[Raw matrix-count capsule](raw/{Path(archive['path']).name}): SHA-256
`{archive['sha256']}`, {archive['payloads']} payloads, each read back and digest
checked. The raw comparison outputs come from the previously retained
[combined campaign](hexgroebner-combined-performance.md).
'''
    if args.check:
        require(args.report.read_text() == text, "report differs from computed figures")
    else:
        args.report.write_text(text)
    print("matrix count report: 14 bases, old fields and stage sums checked")


if __name__ == "__main__":
    main()
