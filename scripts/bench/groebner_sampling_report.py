#!/usr/bin/env python3
"""Regenerate sampled-F4 development results from digest-verified raw evidence."""
import argparse
import hashlib
import math
import json
import statistics
import subprocess
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_measure import FAMILY
from scripts.bench.sweep_freshness import index_listing, tree_listing


def require(value, message):
    if not value:
        raise ValueError(message)


def mean(values):
    return math.exp(sum(map(math.log, values))/len(values))


def campaign(capsule, name):
    metadata = capsule.json(name+'/metadata.json')
    analysis = capsule.json(name+'/analysis.json')
    samples = metadata['samples']
    require(len(samples) == 56, 'incomplete campaign: '+name)
    require(metadata['source_unchanged'] and metadata['threads'] == 1, 'changed source/thread contract')
    require(metadata['binary_sha256'] == metadata['binary_sha256_after'], 'changed binary')
    if metadata['sampled']:
        require(metadata['sampling_controls'] == {'seed': 10987, 'block_rows': 32, 'total_zero_tests': 3}, 'different sampling controls')
    require(metadata['requested_scheduling'] == {'A': 'degree', 'B': 'degree'}, 'scheduling contract mismatch')
    require(metadata['cpu'] == analysis['cpu'] and isinstance(metadata['cpu'], int) and metadata['cpu'] >= 0, 'CPU record mismatch')
    for filename, digest in metadata['input_sha256'].items():
        require(hashlib.sha256(capsule.read(name+'/inputs/'+filename)).hexdigest() == digest, 'input digest mismatch')
    indexed = {(s['case'], s['block'], s['arm']): s for s in samples}
    require(len(indexed) == 56, 'duplicate sample')
    ratios, candidates, families = [], [], {}
    for case in sorted({s['case'] for s in samples}):
        for block in [0, 1]:
            a, b = [indexed[case, block, arm] for arm in ['A', 'B']]
            outputs = []
            for sample in [a, b]:
                require(sample['status'] == 'ok' and sample['returncode'] == 0 and sample['complete_basis_equal'], 'failed sample')
                label = f"{case}-b{block}-{sample['arm']}"
                output = capsule.json(name+'/'+label+'.stdout')
                require(output['kind'] == 'unchecked_candidate', 'incorrect result tier')
                require(output['p'] == sample['p'] and output['order'] == 'grevlex', 'field/order mismatch')
                require(output['scheduling'] == sample['scheduling'] == 'degree', 'sample scheduling mismatch')
                require(int(capsule.text(name+'/'+label+'.rss').strip()) == sample['peak_rss_kib'], 'RSS record mismatch')
                require(output['candidateNanos'] == sample['statistics']['candidate_nanos'], 'candidate timing mismatch')
                if output.get('algorithm') == 'f4-sampled':
                    require(output['randomState'] == (10987+output['sampling']['randomWords']*0x9e3779b97f4a7c15) % 2**64, 'advanced state mismatch')
                outputs.append(output)
            require(outputs[0]['basis'] == outputs[1]['basis'], 'complete output mismatch')
            if metadata.get('baseline_sampled', False) or not metadata['sampled']:
                for output in outputs:
                    output.pop('candidateNanos')
                require(outputs[0] == outputs[1], 'sampled counter/state mismatch')
            ratio = b['wall_nanos']/a['wall_nanos']
            ratios.append(ratio)
            candidates.append(b['statistics']['candidate_nanos']/a['statistics']['candidate_nanos'])
            families.setdefault(a['family'], []).append(ratio)
    require(math.isclose(mean(ratios), analysis['geomean'], rel_tol=1e-12), 'analysis ratio mismatch')
    require(analysis['complete_bases_equal'] == 28 and not analysis['failed_processes'], 'analysis coverage mismatch')
    require(all(math.isclose(mean(values), analysis['per_family'][family], rel_tol=1e-12) for family, values in families.items()), 'family ratio mismatch')
    require(math.isclose(mean([mean(v) for v in families.values()]), analysis['family_balanced_geomean'], rel_tol=1e-12), 'balanced ratio mismatch')
    require(math.isclose(min(ratios), analysis['minimum'], rel_tol=1e-12) and
            math.isclose(max(ratios), analysis['maximum'], rel_tol=1e-12) and
            math.isclose(statistics.median(ratios), analysis['median'], rel_tol=1e-12), 'range/median mismatch')
    require(analysis['peak_rss_kib'] == {arm: max(s['peak_rss_kib'] for s in samples if s['arm'] == arm) for arm in ['A', 'B']}, 'peak RSS mismatch')
    baseline = metadata['baseline_manifest']
    require(hashlib.sha256((json.dumps(baseline, indent=2)+'\n').encode()).hexdigest() == metadata['baseline_manifest_sha256'], 'baseline manifest digest mismatch')
    require(baseline['source_fingerprint'] == metadata['baseline_source_fingerprint'], 'baseline source mismatch')
    key = 'sample' if metadata.get('baseline_sampled', False) else 'compute'
    require(baseline['binary_sha256'][key] == metadata['binary_sha256']['A'], 'baseline binary mismatch')
    return metadata, analysis, mean(candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--reviewed', type=Path, required=True)
    parser.add_argument('--guards', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data, reviewed, guards = Capsule(args.archive), Capsule(args.reviewed), Capsule(args.guards)
    native, full = guards.json('native-status.json'), guards.json('full-status.json')
    expected = {'build', 'oracles', 'driver', 'bench', 'dag', 'phase4', 'manifest', 'headers', 'lines'}
    require(len(full) == 9 and {x['name'] for x in full} == expected, 'incomplete project checks')
    require(len(native) == 2 and {x['name'] for x in native} == {'clang', 'gcc'}, 'missing compiler')
    require(all(x['exit_code'] == 0 for x in native+full), 'failed verification')
    final_listing = guards.text('final-source.manifest')
    final_fingerprint = hashlib.sha256(final_listing.encode()).hexdigest()[:12]
    require(all(x['source_fingerprint'] == final_fingerprint for x in native+full), 'verification runtime differs')
    dirty = subprocess.check_output(['git', 'diff', '--name-only'], cwd=ROOT, text=True).splitlines()
    dirty += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=ROOT, text=True).splitlines()
    require(not any(FAMILY.matches(path) for path in dirty), 'unstaged runtime sources')
    require(index_listing(FAMILY) == tree_listing(FAMILY, 'HEAD') == final_listing, 'current runtime differs from verified source')
    require(reviewed.json('sampled-reviewed/manifest.json')['source_manifest'] == final_listing, 'measured runtime differs')
    require(all(x['variants'] == ['Native', 'Scalar', 'Remainder', 'ScalarRemainder'] for x in native), 'missing native variant')
    for compiler in ['clang', 'gcc']:
        log = guards.text(compiler+'.log')
        require(log.count('sampling pivot pushes=256, shared=1, existing shared entries=0') == 4, 'ownership regression missing')
        require(len(re.findall(r'^check(?:Native|Scalar|Remainder|ScalarRemainder) ASan/UBSan$', log, re.M)) == 4, 'sanitizer mode missing')
        require(log.count('sampling target pivot pushes=256, shared=1, existing shared entries=0') == 4, 'target ownership regression missing')
        require(log.count('1124 certified bases, 10 independently rejected misses') == 4, 'certification coverage missing')
    sources = [(data, label) for label in ['sampled', 'sampled-owned', 'sampled-frame', 'sampled-install', 'sampled-abi']] + [(reviewed, 'sampled-reviewed')]
    manifests = {}
    for capsule, label in sources:
        manifest = capsule.json(label+'/manifest.json')
        manifests[manifest['source_fingerprint']] = manifest
        listing = manifest['source_manifest']
        require(hashlib.sha256(listing.encode()).hexdigest()[:12] == manifest['source_fingerprint'], 'runtime fingerprint mismatch')
        for line in listing.splitlines():
            _, oid, rest = line.split(' ', 2)
            _, path = rest.split('\t')
            blob = capsule.read(label+'/root-sources/'+path)
            require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest() == oid, 'frozen source mismatch')
    names = ['sampled/before-after', 'sampled-owned/before-after', 'sampled-frame/before-after',
             'sampled-frame/before-after-repeat', 'sampled-frame/deterministic',
             'sampled-abi/before-after', 'sampled-abi/deterministic']
    historical = [(data, name) for name in names]
    current = [(reviewed, 'sampled-reviewed/deterministic'), (reviewed, 'sampled-reviewed/refactor')]
    for capsule, expected_names in [(data, set(names)), (reviewed, {name for _, name in current})]:
        actual_names = {path.removesuffix('/metadata.json') for path in capsule.payloads
                        if path.endswith('/metadata.json') and 'samples' in capsule.json(path)}
        require(actual_names == expected_names, 'unlisted or missing timing campaign')
    all_campaigns = historical+current
    names = [name for _, name in all_campaigns]
    results = [campaign(capsule, name) for capsule, name in all_campaigns]
    for metadata, _, _ in results:
        if metadata['baseline_source_fingerprint'] in manifests:
            require(metadata['baseline_manifest'] == manifests[metadata['baseline_source_fingerprint']], 'unbound baseline source')
        require(metadata['source_manifest'] == manifests[metadata['source_fingerprint']]['source_manifest'], 'campaign source is unbound')
        key = 'sample' if metadata['sampled'] else 'compute'
        require(metadata['binary_sha256']['B'] == manifests[metadata['source_fingerprint']]['binary_sha256'][key], 'candidate binary is unbound')
    require(results[5][0]['baseline_manifest'] == data.json('sampled-install/manifest.json'), 'install baseline is unexplained')
    text = '''# Sampled F4 and owned phase transitions

`Sampled.computeWith` is an opt-in unchecked candidate producer. It samples full-field
linear combinations of fixed row blocks with explicit advanced SplitMix64 rejection
state and stops each block after a configured total number of zero reductions.
Rows remain in the input row space, but rank can be missed. No independence,
uniform-sampling error bound, checked-computation speedup or leadership is claimed.
An independent complete-basis certificate is required. Automatic checked retry,
fallback and sampled trace reuse remain outstanding.

The current measured runtime fingerprint is `58952f05cd8c`. Source commits,
compiler revisions, fresh build logs and
binary hashes are in the capsule. Frozen sources rebuild through `lake build`;
executables are identified but not bundled. The sampler leaves deterministic
production as the default.

All campaigns use the same 14 medium development inputs: cyclic7, Katsura8, Eco11,
Noon5, Reimer6, MinRank and dense quadratic6, each over 32003 and 2147483647,
grevlex and degree scheduling. One automatically leased CPU and one algorithm
thread run adjacent AB then BA per input. Seed 10987, blocks of 32 and three total
zero tests are fixed for sampled arms. All 504 processes and 252 complete-basis comparisons are
retained, including regressions; none failed or timed out. Each campaign stands
alone. There are no held-out inputs or performance acceptance results here.

Candidate time covers normalization, F4 and interreduction. Process time also
includes startup, parsing and complete output under identical GNU-time wrappers.
Neither includes certificate generation, independent verification
or kernel checking. Values below are candidate/baseline ratios; smaller is faster.
The balanced suite gives equal weight to each family. Small differences remain
inconclusive under shared-host variability. The frame change has one unchanged
repeat; no campaigns are pooled or selected as best runs.

| Campaign | Baseline → candidate runtime | CPU | Process geometric mean | Candidate geometric mean | Process pair range | Peak RSS A/B (KiB) | Observation |
| --- | --- | ---: | ---: | ---: | --- | --- | --- |
'''
    observations = ['regression', 'inconclusive', 'inconclusive', 'inconclusive', 'regression',
                    'lower in this run', 'regression', 'regression', 'inconclusive']
    for name, (metadata, analysis, candidate), observation in zip(names, results, observations):
        rss = analysis['peak_rss_kib']
        text += f"| `{name}` | `{metadata['baseline_source_fingerprint']}` → `{metadata['source_fingerprint']}` | {metadata['cpu']} | {analysis['geomean']:.4f} | {candidate:.4f} | {analysis['minimum']:.3f}–{analysis['maximum']:.3f} | {rss['A']}/{rss['B']} | {observation} |\n"
    text += '\n`3476217e65f8` identifies `sampled-install`, the isolated reducer-install helper and registered-kernel baseline before owned ABI controls. The seven earlier campaigns retain their original sources. The current two campaigns use bounded scan ranges, atomic inverse admission, shared F4 stages and retained candidate provenance. The current `deterministic` campaign compares sampler B with current deterministic A; `refactor` compares current deterministic B with retained deterministic A. The deterministic refactor observation is inconclusive; the current sampler still regresses overall. CPU values are recorded collection context, not per-process placement attestations.\n'
    final = results[-2][1]
    text += '\nThe final sampler remains slower overall than deterministic F4. Its direct per-family process ratios are:\n\n'
    text += '| Family | Ratio |\n| --- | ---: |\n'
    for family, ratio in final['per_family'].items():
        text += f'| {family} | {ratio:.4f} |\n'
    before = data.json('sampled-install/kernels/result.json')['results'][0]
    after = data.json('sampled-abi/kernels/result.json')['results'][0]
    ladder = [128, 256, 512, 1024, 2048, 4096, 8192]
    for kernel in [before, after, reviewed.json('sampled-reviewed/kernels/result.json')['results'][0]]:
        require(len(kernel['points']) == 21 and len(kernel['trial_summaries']) == 7 and
                [(p['trial_index'], p['param']) for p in kernel['points']] == [(t, n) for t in range(3) for n in ladder] and
                all(p['status'] == 'ok' for p in kernel['points']), 'incomplete kernel campaign')
        require([row['param'] for row in kernel['trial_summaries']] == ladder, 'kernel summary order mismatch')
        for row in kernel['trial_summaries']:
            values = [p['per_call_nanos'] for p in kernel['points'] if p['param'] == row['param']]
            require(row['ok_count'] == 3 and math.isclose(row['median_per_call_nanos'], statistics.median(values), rel_tol=1e-12, abs_tol=1e-6), 'kernel median mismatch')
        require(all(math.isclose(p['total_nanos']/p['inner_repeats'], p['per_call_nanos'], rel_tol=1e-12, abs_tol=1e-6) for p in kernel['points']), 'kernel normalization mismatch')
    require([(p['trial_index'], p['param'], p['result_hash']) for p in before['points']] == [(p['trial_index'], p['param'], p['result_hash']) for p in after['points']], 'kernel result hashes differ')
    text += '''
Known-pivot installation uses a fixed trial-major lean-bench schedule, three outer
trials at every declared input from 128 to 8192. Preparation is excluded; full
pivot decoding, hashing and counters are included. These are separate complexity
runs, not a matched AB/BA speedup experiment. The two historical ABI campaigns
have 21 equal result hashes; the current bounded-range implementation has different
work counters and its hashes are not equated with those historical values.

| Known reducers | Historical borrowed ABI (ms) | Historical owned ABI (ms) | Current owned ABI (ms) |
| ---: | ---: | ---: | ---: |
'''
    latest = reviewed.json('sampled-reviewed/kernels/result.json')['results'][0]
    for a, b, c in zip(before['trial_summaries'], after['trial_summaries'], latest['trial_summaries']):
        require(a['param'] == b['param'] == c['param'] and a['ok_count'] == b['ok_count'] == c['ok_count'] == 3, 'incomplete kernel schedule')
        text += f"| {a['param']} | {a['median_per_call_nanos']/1e6:.4f} | {b['median_per_call_nanos']/1e6:.4f} | {c['median_per_call_nanos']/1e6:.4f} |\n"
    text += f"\nLean-bench reports `{before['verdict']}` before and `{after['verdict']}` after. The normalized log slopes are {before['slope']:.6f} and {after['slope']:.6f}.\n"
    text += f"\nThe current kernel reports `{latest['verdict']}` with normalized slope {latest['slope']:.6f}.\n"
    old = data.json('owners/results.json')['rows']
    new = data.json('owners/owned-results.json')
    require(len(old) == len(new) == 6 and [v['n'] for v in old] == [128, 512, 1024, 2048, 4096, 8192], 'incomplete ownership diagnostic')
    for a, b in zip(old, new):
        require(a['n'] == b['n'] and a['stdout'].splitlines()[0] == b['stdout'].splitlines()[0], 'ownership digest differs')
        n = a['n']
        require(a['stdout'].splitlines()[1] == f'({n}, ({n}, {n*(n-1)//2}))', 'unexpected borrowed copy count')
        require(b['stdout'].splitlines()[1] == f'({n}, (1, 0))', 'unexpected owned copy count')
    text += '''
The untimed array-push diagnostic counts exactly n(n−1)/2 existing pivot-array
elements exposed to shared pushes before the ABI control, and zero afterward,
at all six retained sizes. The final runtime uses Lean's available exported owned
ABI for consuming phase functions, releases buffers before extending them and
removes the outer driver's extra matrix owner. Real caller snapshots retain
immutable contents. This is an implemented workaround using the current compiler,
not evidence that the performance goal requires a language change.

The retained Eco11 M31 cycle profiles report array copying and reference-count
cleanup in the initial sampler; subtract arithmetic is a small fraction. Profile
reports and hashes of the original binary perf traces are bundled; the traces
remain in the measurement workspace. The ownership interposer supplies direct
copy-count evidence independently of that sampled profile.

Native/scalar/resumption comparisons cover 1,134 systems. Independent complete-basis
certification accepts 1,124 and rejects ten sampled misses; the forced F2 miss is
also rejected. Ordinary F2 polynomials retain ordinary exponents. All eight native
compiler/sanitizer variants pass, including fresh pivot ownership and bounded native
composition checks. Fresh known-reducer and generated-target pivot arrays copy
zero existing elements; these counters do not measure every ByteArray copy.
Retained scan/gather snapshots separately check immutability. Parent-budget tests
cover every resource plus ten interruptions in matrix and atomic F4 stages.
Both driver initializers agree on the corpus and continue cooperative suspensions. The full project
checks cover independent oracles, kernel replay/axiom audit, bench verification,
dependency DAG, phase, release manifest, headers and file lengths. Kernel agreement
theorems compare the portable Lean definitions; native-provider agreement is tested.
The current staged runtime is byte-bound to the measured source manifest and
the source identifiers in the verification records. Historical snapshots and
verification remain separate from the current implementation.
'''
    text += f"\nRaw evidence: `{args.archive.name}`, SHA-256 `{data.sha256}`, {data.count} payloads plus manifest. Current measurements: `{args.reviewed.name}`, SHA-256 `{reviewed.sha256}`, {reviewed.count} payloads plus manifest. Verification: `{args.guards.name}`, SHA-256 `{guards.sha256}`, {guards.count} payloads plus manifest.\n"
    text += f"\nRegenerate with `python3 scripts/bench/groebner_sampling_report.py --archive {args.archive.as_posix()} --reviewed {args.reviewed.as_posix()} --guards {args.guards.as_posix()} --report {args.report.as_posix()} --check`. Every consumed payload is verified against its capsule manifest; ratios, complete outputs and runtime source blobs are independently recomputed or checked.\n"
    if args.check:
        require(args.report.read_text() == text, 'report differs from verified evidence')
    else:
        args.report.write_text(text)
    print('sampled F4 report verified' if args.check else 'sampled F4 report generated')


if __name__ == '__main__':
    main()
