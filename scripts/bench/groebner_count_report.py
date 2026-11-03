#!/usr/bin/env python3
"""Regenerate the report-specific, untimed F4 matrix-count tables."""
import argparse
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_json import loads
from scripts.bench.groebner_capsule import Capsule


def load(path):
    return loads(path.read_text())


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["data", "previous", "native", "full", "archive", "previous-archive", "guards", "report"]:
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    packed = Capsule(args.archive)
    previous_packed = Capsule(args.previous_archive)
    guard_packed = Capsule(args.guards)
    def current_input(path, relative):
        packed.bind(path, relative)
        return packed.json(relative)
    manifest = current_input(args.data / "manifest.json", "measurement/manifest.json")
    diagnostics = current_input(args.data / "diagnostics/metadata.json", "measurement/diagnostics/metadata.json")
    stages = current_input(args.data / "stages/metadata.json", "measurement/stages/metadata.json")
    native = current_input(args.native, "reproduction/matrix-counts-native-status.json")
    full = current_input(args.full, "reproduction/matrix-counts-full-status.json")
    previous_packed.bind(args.previous / "metadata.json", "measurement/before-after-selected/metadata.json")
    previous_metadata = previous_packed.json("measurement/before-after-selected/metadata.json")
    guard = guard_packed.json("record.json")
    reviewed_full = guard_packed.json("full-status.json")
    reviewed_fixture = guard_packed.json("fixture-audit.json")
    require(guard["exit_code"] == 0, "guard command failed")
    require("Build completed successfully" in guard_packed.text(guard["log"]), "guard build is incomplete")
    identity = guard_packed.json("binary-identity.json")
    require(identity["byte_identical"] and identity["old_binaries"] == identity["new_binaries"] == manifest["binary_sha256"], "reviewed binary mismatch")
    require(identity["review_commit"] == guard["source_commit"], "guard identity mismatch")
    archive = dict(path=str(args.archive), sha256=packed.sha256, payloads=packed.count)
    expected_checks = {"build", "oracles", "driver", "bench", "dag", "phase4", "manifest", "headers", "lines"}
    require({x["name"] for x in full} == expected_checks and len(full) == len(expected_checks), "incomplete project checks")
    require(len(reviewed_full) == len(expected_checks) and {x["name"] for x in reviewed_full} == expected_checks, "incomplete reviewed project checks")
    require(all(x["exit_code"] == 0 and x["source_commit"] == guard["source_commit"] and
                x["source_fingerprint"] == identity["reviewed_source"] for x in reviewed_full), "reviewed project check mismatch")
    require(reviewed_fixture["exit_code"] == 0 and reviewed_fixture["fixture_bytes_unchanged"] and
            reviewed_fixture["traced_matrix_fields"] == 8 and reviewed_fixture["zero_rows_bounded_by_targets"], "reviewed fixture audit failed")
    require(stages["runtime_source_fingerprint"] == manifest["source_fingerprint"], "stage runtime source mismatch")
    require(set(identity["old_binaries"]) == {"compute", "compute-reference"}, "driver identity is incomplete")
    require(len(native) == 2 and {x["name"] for x in native} == {"clang", "gcc"}, "missing compiler")
    require(all(len(x["variants"]) == 4 and set(x["variants"]) == {"Native", "Scalar", "Remainder", "ScalarRemainder"} for x in native), "missing native variant")
    require(all(x["exit_code"] == 0 for x in native + full), "incomplete verification")
    require({x["source_commit"] for x in native + full} == {manifest["commit"]}, "verification commit mismatch")
    require(all(x["source_fingerprint"] == manifest["source_fingerprint"] for x in native + full), "source mismatch")
    fixture = packed.json("reproduction/matrix-counts-fixture-audit.json")
    corpus_size = fixture["records"]
    require(reviewed_fixture["records"] == corpus_size, "reviewed fixture size mismatch")
    require(fixture["unchanged_existing_fields"] and fixture["checked_traced_counts"], "fixture audit failed")
    driver_sizes = list(map(int, re.findall(r"candidate driver: (\d+) complete corpus outputs/counters", packed.text("reproduction/matrix-counts-full-driver.log"))))
    require(driver_sizes == [corpus_size, corpus_size], "driver corpus mismatch")
    require(len(diagnostics["runs"]) == len(stages["runs"]) == 14, "incomplete corpus")
    stage_map = {row["case"]: row for row in stages["runs"]}
    require(len(stage_map) == 14, "duplicate stage case")
    rows = []
    keys = ["matrixCalls", "matrixRows", "matrixTargets", "matrixReductions", "matrixZeroRows"]
    for record in diagnostics["runs"]:
        name = record["case"]
        whole = current_input(args.data / "diagnostics" / (name + ".stdout"), "measurement/diagnostics/" + name + ".stdout")
        previous_relative = "measurement/before-after-selected/" + name + "-b0-B.stdout"
        previous_packed.bind(args.previous / (name + "-b0-B.stdout"), previous_relative)
        previous = previous_packed.json(previous_relative)
        current = loads(json.dumps(whole))
        current.pop("candidateNanos")
        previous.pop("candidateNanos")
        for key in keys[2:]:
            current["statistics"].pop(key)
        require(current == previous, "old output/counter mismatch: " + name)
        require(whole["statistics"] == record["counters"], "retained count mismatch")
        stage_relative = "measurement/stages/" + name + ".jsonl"
        packed.bind(args.data / "stages" / (name + ".jsonl"), stage_relative)
        sequence = [loads(line) for line in packed.text(stage_relative).splitlines()]
        footer = sequence.pop()
        require(footer["kind"] == "stage_diagnostics_complete" and footer["basis"] == whole["basis"], "stage basis mismatch")
        totals = {phase: {key: sum(row[key] for row in sequence if row["phase"] == phase) for key in keys}
                  for phase in ["input", "pairs", "interreduce"]}
        require(totals == stage_map[name]["phases"], "stage metadata mismatch")
        require(all(values["matrixZeroRows"] <= values["matrixTargets"] for values in totals.values()), "F4 zero rows exceed targets")
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
metadata/counter field agree with retained `{previous_metadata['source_fingerprint']}` outputs. The three
new fields are the only additions. The raw `candidateNanos` values are retained
but no timing, speedup or acceptance claim uses these executions.

The external `F4.step` runner separates input normalization, pair rounds and
final interreduction. Its complete bases and all five matrix counters match
the separately built candidate driver from the same runtime source; final interchange decoding work is
absent from that runner and is not equated. All stage source/build records
are retained. Eco11 M31 stage data has collector-level binary/source identity,
without a separate per-run binary attestation. Aggregate zero fractions mix these different stages and do not
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

All {len(reviewed_full)} project checks pass at `{guard['source_commit']}`. At
`{manifest['commit']}`, all {len(full)} project checks and {sum(len(x['variants']) for x in native)} source-identified
Clang/GCC sanitizer/SIMD/scalar/remainder variants also pass. The reviewed emitter verifies
traced/untraced and native/portable counts on {corpus_size:,} profiles, and the regenerated
fixtures preserve every pre-existing field. All {len(driver_sizes)} complete driver corpora pass.
The hand-checkable matrix with reducer `x` and targets `1,x` has two targets,
one pivot application and one zero row. Its additional work-exhaustion guard
retains that completed reduction/zero prefix at conformance commit
`{guard['source_commit']}`, command `{guard['command']}` (exit {guard['exit_code']}).
Four additional traced guards retain consumed reduction/zero prefixes when trace
capacity is exhausted, across joint/independent and native/portable calls. A fresh
build at reviewed runtime fingerprint `{identity['reviewed_source']}` produces
both driver executables byte-identically to the frozen diagnostic drivers.

The [count-report generator](../../scripts/bench/groebner_count_report.py)
rechecks the old output fields, raw diagnostic counts, stage sums and complete
bases before generating this table. Every input consumed from unpacked paths is byte-bound to a capsule member,
and every payload digest is verified before analysis. The guard command and
its complete log are read from a separate verified capsule. The historical
source identifiers are bound through the retained source patch, tree hashes
and blob manifest.
Candidate production, certificate generation, native verification and kernel
checking remain distinct. This change makes no performance milestone claim;
issue #10987 remains open.

[Raw matrix-count capsule](raw/{Path(archive['path']).name}): SHA-256
`{archive['sha256']}`, {archive['payloads']} data payloads, each read back and digest
checked, plus the digest manifest. The raw comparison outputs come from the previously retained
[combined campaign](hexgroebner-combined-performance.md), SHA-256
`{previous_packed.sha256}`. The separate guard capsule is
[guard validation](raw/{args.guards.name}), SHA-256 `{guard_packed.sha256}`.
'''
    if args.check:
        require(args.report.read_text() == text, "report differs from computed figures")
    else:
        args.report.write_text(text)
    print("matrix count report: 14 bases, old fields and stage sums checked")


if __name__ == "__main__":
    main()
