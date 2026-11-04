#!/usr/bin/env python3
"""Regenerate the report for the restored F4 vector/inline experiments."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_performance_audit import campaign
from scripts.bench.groebner_capsule import Capsule


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = args.state
    packed = Capsule(args.archive)
    archive = dict(path=str(args.archive), sha256=packed.sha256, payloads=packed.count)
    vector_manifest = packed.json("avx512-production/manifest.json")
    inline_manifest = packed.json("geometry-inline-production/manifest.json")
    inline_patch = packed.text("geometry-inline.patch")
    additions = [line[1:] for line in inline_patch.splitlines() if line.startswith("+") and not line.startswith("+++")]
    deletions = [line[1:] for line in inline_patch.splitlines() if line.startswith("-") and not line.startswith("---")]
    if additions != ["__attribute__((always_inline))"] or deletions or inline_patch.count("diff --git ") != 1 or "diff --git a/HexGroebner/ffi/matrix_scan.c b/HexGroebner/ffi/matrix_scan.c" not in inline_patch:
        raise ValueError("inline experiment differs from one attribute")
    native = packed.json("reproduction/avx512-native-status.json")
    if len(native) != 2 or {x["name"] for x in native} != {"clang", "gcc"} or any(x["exit_code"] != 0 or len(x["variants"]) != 4 or set(x["variants"]) != {"Native", "Scalar", "Remainder", "ScalarRemainder"} or
                              x["source_fingerprint"] != vector_manifest["source_fingerprint"] for x in native):
        raise ValueError("incomplete vector native checks")
    baseline = packed.json("avx512-production/before-after/metadata.json")["baseline_source_fingerprint"]
    text = f'''# Restored matrix row-update experiments

Neither a sixteen-lane AVX-512 update nor forced geometry inlining establishes
an improvement on the matched medium development suite. Both variants are
restored; neither is part of the production row kernel. The canonical row
representation, bounded native calls, malformed-input checks and output
contracts remain unchanged.

The AVX-512 variant has source fingerprint `{vector_manifest['source_fingerprint']}`. It uses sixteen
four-byte coefficients per vector, exact Montgomery/Mersenne products,
contiguous stores or scatter, runtime CPU/OS feature detection and the existing
eight-lane/scalar tails. All {sum(len(x['variants']) for x in native)} source-identified Clang/GCC sanitizer
variants pass, including guarded buffers, malformed lanes, aliasing, resumed
prefixes and instrumented complete F4 calls on both vector layouts. The separate
one-line `always_inline` variant (`{inline_manifest['source_fingerprint']}`) changes only geometry helper compilation;
its fresh CLI build and complete before/after output comparisons pass.

All campaigns compare against frozen source `{baseline}`, with adjacent
AB pairs followed by BA pairs, one automatically leased CPU and identical
resource/output contracts. The AVX-512 repeat is the one unchanged repeat after
an inconclusive first observation. The inlining source has one campaign.
Every completed sample is retained, with failures, RSS, variability, CPU and
host context. Sources are never pooled across campaigns.

| Variant/campaign | Process ratio new/baseline | Internal candidate ratio | Median process ratio | Process range | CPU | Peak RSS baseline/new KiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
'''
    for label, directory in [("AVX-512 first", source / "avx512-production/before-after"),
                             ("AVX-512 repeat", source / "avx512-production/before-after-repeat"),
                             ("Forced inline", source / "geometry-inline-production/before-after")]:
        relative = str(directory.relative_to(source))
        for name in ["metadata.json", "analysis.json", "candidate-analysis.json"]:
            packed.bind(directory / name, relative + "/" + name)
        metadata = packed.json(relative + "/metadata.json")
        expected = inline_manifest if label == "Forced inline" else vector_manifest
        if metadata["source_fingerprint"] != expected["source_fingerprint"] or metadata["source_fingerprint_after"] != expected["source_fingerprint"] or not metadata["source_unchanged"] or metadata["manifest_binary_sha256"] != expected["binary_sha256"] or metadata["binary_sha256"]["B"] != expected["binary_sha256"]["compute"] or metadata["binary_sha256"]["A"] != metadata["baseline_manifest"]["binary_sha256"]["compute"]:
            raise ValueError("vector campaign source mismatch")
        if metadata["baseline_source_fingerprint"] != baseline:
            raise ValueError("vector baseline mismatch")
        for sample in metadata["samples"]:
            filename = f"{sample['case']}-b{sample['block']}-{sample['arm']}.stdout"
            packed.bind(directory / filename, relative + "/" + filename)
        result = campaign(directory)
        text += (f"| {label} | {result['family_balanced_geomean']:.4f} | {result['candidate_geomean']:.4f} | "
                 f"{result['median']:.4f} | {result['minimum']:.4f}–{result['maximum']:.4f} | {result['cpu']} | "
                 f"{result['peak_rss_kib']['A']}/{result['peak_rss_kib']['B']} |\n")
    text += f'''
Each campaign retains 56 processes and 28 complete-basis comparisons, all
successful with identical output/counter/scheduling fields except internal
candidate time. The process metric weights the seven development families
equally. Candidate production and process intervals are distinct; certificate
generation, independent native verification and kernel checking are excluded.
These inputs are not held out and cannot establish acceptance or leadership.

The diagnostic Eco11 M31 profiles report no lost samples. Their instruction
annotations place substantial samples near gather/scatter dependency boundaries.
This is cost attribution for one input, including startup/output, rather than
a causal proof of a memory bottleneck or a scientific timing comparison.
The observations justify retaining the existing production kernel while
pursuing less repeated algebraic work. They establish no language limitation.

The [report generator](../../scripts/bench/groebner_vector_report.py) reruns the
complete JSON comparisons and recomputes all displayed figures from raw sample
metadata. It verifies every payload digest and binds all unpacked analysis
inputs to the corresponding capsule members before consuming them. Fixed schedules and all completed observations remain available;
there is no retry-until-faster selection. Issue #10987 remains open.

[Raw restored-experiment capsule](raw/{Path(archive['path']).name}): SHA-256
`{archive['sha256']}`, {archive['payloads']} data payloads, each read back and digest
checked, plus the digest manifest. It contains source patches/manifests, compiler/build/native logs,
all three campaigns, independent analyses and raw profiles/annotations.
'''
    if args.check:
        if args.report.read_text() != text:
            raise ValueError("vector report differs from computed figures")
    else:
        args.report.write_text(text)
    print("restored vector report: all 168 processes and 84 paired outputs checked")


if __name__ == "__main__":
    main()
