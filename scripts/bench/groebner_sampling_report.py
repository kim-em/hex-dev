#!/usr/bin/env python3
"""Regenerate sampled-F4 development results from digest-verified raw evidence."""
import argparse
import hashlib
import math
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule


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
    require(metadata['sampling_controls'] == {'seed': 10987, 'block_rows': 32, 'total_zero_tests': 3}, 'different sampling controls')
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
                require(output['candidateNanos'] == sample['statistics']['candidate_nanos'], 'candidate timing mismatch')
                if output.get('algorithm') == 'f4-sampled':
                    require(output['randomState'] == (10987+output['sampling']['randomWords']*0x9e3779b97f4a7c15) % 2**64, 'advanced state mismatch')
                outputs.append(output)
            require(outputs[0]['basis'] == outputs[1]['basis'], 'complete output mismatch')
            if metadata.get('baseline_sampled', False):
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
    return metadata, analysis, mean(candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--guards', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data, guards = Capsule(args.archive), Capsule(args.guards)
    native, full = guards.json('native-status.json'), guards.json('full-status.json')
    expected = {'build', 'oracles', 'driver', 'bench', 'dag', 'phase4', 'manifest', 'headers', 'lines'}
    require(len(full) == 9 and {x['name'] for x in full} == expected, 'incomplete project checks')
    require(len(native) == 2 and {x['name'] for x in native} == {'clang', 'gcc'}, 'missing compiler')
    require(all(x['exit_code'] == 0 for x in native+full), 'failed verification')
    final_listing = guards.text('final-source.manifest')
    final_fingerprint = hashlib.sha256(final_listing.encode()).hexdigest()[:12]
    require(all(x['source_fingerprint'] in {'b865a5399fec', final_fingerprint} for x in native+full), 'verification runtime differs')
    measured = data.json('sampled-abi/manifest.json')
    path = 'bench/HexGroebner/Bench/Sampling.lean'
    old = data.read('sampled-abi/root-sources/'+path)
    comment = (b'-- Scalar primitives visit the same two entries per reducer, 2*n workspace\n'
               b'-- columns, three fixed target trials and all n decoded pivots: linear in n.\n')
    changed = old.replace(b'setup_benchmark samplingKnownPortable', comment+b'setup_benchmark samplingKnownPortable')
    require(guards.read('Sampling.lean') == changed, 'non-comment benchmark change')
    old_oid = hashlib.sha1(b'blob '+str(len(old)).encode()+b'\0'+old).hexdigest()
    new_oid = hashlib.sha1(b'blob '+str(len(changed)).encode()+b'\0'+changed).hexdigest()
    require(final_listing == measured['source_manifest'].replace(old_oid, new_oid), 'other runtime source changed')
    identity = guards.json('comment-binary-identity.json')
    require(identity['identical_binary'] and identity['final_bench_sha256'] == identity['measured_bench_sha256'] == measured['binary_sha256']['bench'], 'benchmark binary changed')
    require(all(x['variants'] == ['Native', 'Scalar', 'Remainder', 'ScalarRemainder'] for x in native), 'missing native variant')
    for compiler in ['clang', 'gcc']:
        log = guards.text(compiler+'.log')
        require(log.count('sampling pivot pushes=256, shared=1, existing shared entries=0') == 4, 'ownership regression missing')
        require(log.count('1124 certified bases, 10 independently rejected misses') == 4, 'certification coverage missing')
    for label in ['sampled', 'sampled-owned', 'sampled-frame', 'sampled-install', 'sampled-abi']:
        manifest = data.json(label+'/manifest.json')
        listing = manifest['source_manifest']
        require(hashlib.sha256(listing.encode()).hexdigest()[:12] == manifest['source_fingerprint'], 'runtime fingerprint mismatch')
        for line in listing.splitlines():
            _, oid, rest = line.split(' ', 2)
            _, path = rest.split('\t')
            blob = data.read(label+'/root-sources/'+path)
            require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest() == oid, 'frozen source mismatch')
    names = ['sampled/before-after', 'sampled-owned/before-after', 'sampled-frame/before-after',
             'sampled-frame/before-after-repeat', 'sampled-frame/deterministic',
             'sampled-abi/before-after', 'sampled-abi/deterministic']
    results = [campaign(data, name) for name in names]
    text = '''# Sampled F4 and owned phase transitions

`Sampled.computeWith` is an opt-in unchecked candidate producer. It samples full-field
linear combinations of fixed row blocks with explicit advanced SplitMix64 rejection
state and stops each block after a configured total number of zero reductions.
Rows remain in the input row space, but rank can be missed. No independence,
uniform-sampling error bound, checked-computation speedup or leadership is claimed.
An independent complete-basis certificate is required. Automatic checked retry,
fallback and sampled trace reuse remain outstanding.

The final measured runtime fingerprint is `b865a5399fec`. Its original source commit,
rebased byte-identical source identity, compiler revision, fresh build logs and
binary hashes are in the capsule. Frozen sources rebuild through `lake build`;
executables are identified but not bundled. The sampler leaves deterministic
production as the default.

All campaigns use the same 14 medium development inputs: cyclic7, Katsura8, Eco11,
Noon5, Reimer6, MinRank and dense quadratic6, each over 32003 and 2147483647,
grevlex and degree scheduling. One automatically leased CPU and one algorithm
thread run adjacent AB then BA per input. Seed 10987, blocks of 32 and three total
zero tests are fixed. All 392 processes and 196 complete-basis comparisons are
retained, including regressions; none failed or timed out. Each campaign stands
alone. There are no held-out inputs or performance acceptance results here.

Candidate time covers normalization, F4 and interreduction. Process time also
includes startup, parsing and complete output under identical GNU-time wrappers.
Neither includes certificate generation, independent verification
or kernel checking. Values below are candidate/baseline ratios; smaller is faster.
The balanced suite gives equal weight to each family. Small differences remain
inconclusive under shared-host variability. The frame change has one unchanged
repeat; no campaigns are pooled or selected as best runs.

| Campaign | Baseline → candidate runtime | CPU | Process geometric mean | Candidate geometric mean | Process pair range | Peak RSS A/B (KiB) |
| --- | --- | ---: | ---: | ---: | --- | --- |
'''
    for name, (metadata, analysis, candidate) in zip(names, results):
        rss = analysis['peak_rss_kib']
        text += f"| `{name}` | `{metadata['baseline_source_fingerprint']}` → `{metadata['source_fingerprint']}` | {metadata['cpu']} | {analysis['geomean']:.4f} | {candidate:.4f} | {analysis['minimum']:.3f}–{analysis['maximum']:.3f} | {rss['A']}/{rss['B']} |\n"
    final = results[-1][1]
    text += '\nThe final sampler remains slower overall than deterministic F4. Its direct per-family process ratios are:\n\n'
    text += '| Family | Ratio |\n| --- | ---: |\n'
    for family, ratio in final['per_family'].items():
        text += f'| {family} | {ratio:.4f} |\n'
    before = data.json('sampled-install/kernels/result.json')['results'][0]
    after = data.json('sampled-abi/kernels/result.json')['results'][0]
    require([(p['trial_index'], p['param'], p['result_hash']) for p in before['points']] == [(p['trial_index'], p['param'], p['result_hash']) for p in after['points']], 'kernel result hashes differ')
    text += '''
Known-pivot installation uses a fixed trial-major lean-bench schedule, three outer
trials at every declared input from 128 to 8192. Preparation is excluded; full
pivot decoding, hashing and counters are included. These are separate complexity
runs, not a matched AB/BA speedup experiment. All 21 result hashes agree.

| Known reducers | Borrowed ABI median (ms) | Owned ABI median (ms) |
| ---: | ---: | ---: |
'''
    for a, b in zip(before['trial_summaries'], after['trial_summaries']):
        require(a['param'] == b['param'] and a['ok_count'] == b['ok_count'] == 3, 'incomplete kernel schedule')
        text += f"| {a['param']} | {a['median_per_call_nanos']/1e6:.4f} | {b['median_per_call_nanos']/1e6:.4f} |\n"
    text += f"\nLean-bench reports `{before['verdict']}` before and `{after['verdict']}` after. The normalized log slopes are {before['slope']:.6f} and {after['slope']:.6f}.\n"
    old = data.json('owners/results.json')['rows']
    new = data.json('owners/owned-results.json')
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
composition checks. Both driver initializers agree on the corpus. The full project
checks cover independent oracles, kernel replay/axiom audit, bench verification,
dependency DAG, phase, release manifest, headers and file lengths. Kernel agreement
theorems compare the portable Lean definitions; native-provider agreement is tested.
The final source differs from the measured runtime snapshot by two adjacent portable
cost-model comment lines. Its rebuilt benchmark is byte-identical. The exact source
delta, build identity and project-check records are retained in the verification capsule.
'''
    text += f"\nRaw evidence: `{args.archive.name}`, SHA-256 `{data.sha256}`, {data.count} payloads plus manifest. Verification: `{args.guards.name}`, SHA-256 `{guards.sha256}`, {guards.count} payloads plus manifest.\n"
    text += f"\nRegenerate with `python3 scripts/bench/groebner_sampling_report.py --archive {args.archive.as_posix()} --guards {args.guards.as_posix()} --report {args.report.as_posix()} --check`. Every consumed payload is verified against its capsule manifest; ratios, complete outputs and runtime source blobs are independently recomputed or checked.\n"
    if args.check:
        require(args.report.read_text() == text, 'report differs from verified evidence')
    else:
        args.report.write_text(text)
    print('sampled F4 report verified' if args.check else 'sampled F4 report generated')


if __name__ == '__main__':
    main()
