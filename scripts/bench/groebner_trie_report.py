#!/usr/bin/env python3
"""Regenerate reducer-priority lookup observations from verified capsules."""
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_json import loads


def require(value, message):
    if not value:
        raise ValueError(message)


def mean(values):
    return math.exp(statistics.mean(map(math.log, values)))


def source(capsule, label):
    manifest = capsule.json(label+'/manifest.json')
    listing = manifest['source_manifest']
    require(hashlib.sha256(listing.encode()).hexdigest()[:12] == manifest['source_fingerprint'], 'source fingerprint mismatch')
    for line in listing.splitlines():
        _, oid, rest = line.split(' ', 2)
        _, path = rest.split('\t')
        blob = capsule.read(label+'/root-sources/'+path)
        require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest() == oid, 'source blob mismatch')
    return manifest


def campaign(capsule, label, manifests):
    metadata = capsule.json(label+'/metadata.json')
    recorded = capsule.json(label+'/analysis.json')
    require(metadata['source_unchanged'] and metadata['threads'] == 1 and
            metadata['requested_scheduling'] == {'A': 'degree', 'B': 'degree'}, 'source/thread/scheduling mismatch')
    require(metadata['binary_sha256'] == metadata['binary_sha256_after'], 'binary changed')
    baseline = metadata['baseline_manifest']
    require(baseline == manifests[metadata['baseline_source_fingerprint']], 'baseline source mismatch')
    require(hashlib.sha256((json.dumps(baseline, indent=2)+'\n').encode()).hexdigest() == metadata['baseline_manifest_sha256'], 'baseline manifest digest mismatch')
    current = manifests[metadata['source_fingerprint']]
    require(metadata['source_manifest'] == current['source_manifest'] and
            metadata['binary_sha256'] == {'A': baseline['binary_sha256']['compute'], 'B': current['binary_sha256']['compute']}, 'source/binary binding mismatch')
    for name, digest in metadata['input_sha256'].items():
        require(hashlib.sha256(capsule.read(label+'/inputs/'+name)).hexdigest() == digest, 'input digest mismatch')
    indexed = {(s['case'],s['block'],s['arm']): s for s in metadata['samples']}
    require(len(indexed) == len(metadata['samples']) == 56, 'incomplete or duplicate campaign')
    order = [v['case'] for v in metadata['samples'] if v['block'] == 0 and v['arm'] == 'A']
    require(len(order) == len(set(order)) == 14, 'incomplete first block')
    require([(v['case'],v['block'],v['arm']) for v in metadata['samples']] ==
            [(case,block,arm) for block in [0,1] for case in order for arm in (['A','B'] if block == 0 else ['B','A'])], 'AB/BA adjacency mismatch')
    families, candidate, work, ratios, allocations = {}, [], [], [], []
    for case in sorted({s['case'] for s in metadata['samples']}):
        for block in [0,1]:
            a,b = [indexed[case,block,arm] for arm in ['A','B']]
            require(a['family'] == b['family'], 'family mismatch')
            outputs = []
            for arm, sample in [('A',a),('B',b)]:
                require(sample['status'] == 'ok' and sample['returncode'] == 0 and sample['complete_basis_equal'], 'failed sample')
                output = capsule.json(f'{label}/{case}-b{block}-{arm}.stdout')
                require(output['kind'] == 'unchecked_candidate' and output['order'] == 'grevlex' and
                        output['scheduling'] == sample['scheduling'] == 'degree' and output['p'] == sample['p'], 'output contract mismatch')
                stats = dict(sample['statistics'])
                require(stats.pop('candidate_nanos') == output['candidateNanos'] and stats == output['statistics'], 'output counters differ from metadata')
                require(int(capsule.text(f'{label}/{case}-b{block}-{arm}.rss').strip()) == sample['peak_rss_kib'], 'RSS record mismatch')
                outputs.append(output)
            candidate.append(outputs[1]['candidateNanos']/outputs[0]['candidateNanos'])
            work.append(outputs[1]['statistics']['work']/outputs[0]['statistics']['work'])
            allocations.append(outputs[1]['statistics']['allocatedBytes']-outputs[0]['statistics']['allocatedBytes'])
            for output in outputs:
                output.pop('candidateNanos')
                output['statistics'].pop('work')
                output['statistics'].pop('allocatedBytes')
            require(outputs[0] == outputs[1], 'basis or non-work/allocation metadata mismatch')
            ratio = b['wall_nanos']/a['wall_nanos']
            ratios.append(ratio)
            families.setdefault(a['family'], []).append(ratio)
    require(len(families) == 7 and all(len(v) == 4 for v in families.values()), 'unbalanced suite')
    require(recorded['complete_bases_equal'] == 28 and recorded['failed_processes'] == 0 and
            recorded['timeouts'] == 0 and recorded['samples'] == 56 and recorded['cpu'] == metadata['cpu'], 'coverage/CPU mismatch')
    for key, value in [('geomean',mean(ratios)),('family_balanced_geomean',mean([mean(v) for v in families.values()])),
                       ('minimum',min(ratios)),('maximum',max(ratios)),('median',statistics.median(ratios))]:
        require(math.isclose(recorded[key], value, rel_tol=1e-12), 'recorded '+key+' differs')
    for family, values in families.items():
        require(math.isclose(recorded['per_family'][family], mean(values), rel_tol=1e-12), 'family ratio differs')
    require(recorded['peak_rss_kib'] == {arm:max(s['peak_rss_kib'] for s in metadata['samples'] if s['arm'] == arm) for arm in ['A','B']}, 'peak RSS differs')
    require(all(value == 0 for value in allocations), 'allocation counters changed')
    require(all(value <= 1 for value in work), 'charged work increased')
    if label in {'trie-direct/control','trie-bounded/control'}:
        require(all(value == 1 for value in work), 'control transformation changed charged work')
    return metadata,recorded,mean(candidate),mean(work),min(allocations),max(allocations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['archive','format','intermediate-baseline','final-baseline','fixture-baseline','guards','report']:
        parser.add_argument('--'+name, type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--current', action='store_true')
    args = parser.parse_args()
    data, intermediate, baseline, guards = map(Capsule, [args.archive,args.intermediate_baseline,args.final_baseline,args.guards])
    format_data, fixture_baseline = Capsule(args.format), Capsule(args.fixture_baseline)
    manifests = {}
    for capsule,label in [(data,'trie-bound'),(data,'trie-wide'),(data,'trie-global'),(data,'trie-direct'),(data,'trie-bounded'),(data,'trie-selected'),
                          (intermediate,'sampled-reviewed'),(baseline,'sampled-final'),(format_data,'trie-format')]:
        manifest = source(capsule,label)
        manifests[manifest['source_fingerprint']] = manifest
    latest = data.json('trie-selected/manifest.json')
    measured = data.json('trie-bounded/manifest.json')
    require(latest['binary_sha256'] == measured['binary_sha256'], 'selected executables differ from measured bytes')
    old_lines = measured['source_manifest'].splitlines()
    new_lines = latest['source_manifest'].splitlines()
    changed = [a.split('\t')[1] for a,b in zip(old_lines,new_lines) if a != b]
    require(len(old_lines) == len(new_lines) and changed == ['bench/HexGroebner/Bench/Trie.lean'], 'selected source delta is not confined to the benchmark comment')
    comment = '-- O(n): the portable traversal scans n root edges and the first preferred\n-- branch, edge and leaf, then returns at the root bound: n+4 charged work.\n'
    path = '/root-sources/bench/HexGroebner/Bench/Trie.lean'
    require(data.text('trie-selected'+path).replace(comment,'') == data.text('trie-bounded'+path), 'selected source comment delta differs')
    latest = format_data.json('trie-format/manifest.json')
    measured = latest
    fixture_path = 'checks-sources/conformance-fixtures/HexGroebner/f4.jsonl'
    old_fixture = [loads(line) for line in fixture_baseline.text(fixture_path).splitlines()]
    new_fixture = [loads(line) for line in guards.text(fixture_path).splitlines()]
    require(len(old_fixture) == len(new_fixture) == 1134, 'fixture record count differs')
    fixture_counts = Counter()
    fixture_records = 0
    for old,new in zip(old_fixture,new_fixture):
        before,after = old.pop('value'),new.pop('value')
        require(old == new and before.keys() == after.keys(), 'fixture metadata differs')
        changed = [key for key in before if before[key] != after[key]]
        fixture_records += bool(changed)
        for key in changed:
            require(key in {'work','serialWork','referenceWork'} and after[key] <= before[key], 'non-work fixture change')
            fixture_counts[key] += 1
    runtime, checks = guards.text('runtime.manifest'), guards.text('checks.manifest')
    require(runtime == latest['source_manifest'], 'verification runtime differs from measurement')
    for listing,prefix in [(runtime,'runtime-sources/'),(checks,'checks-sources/')]:
        for line in listing.splitlines():
            _,oid,rest=line.split(' ',2)
            _,path=rest.split('\t')
            blob=guards.read(prefix+path)
            require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest() == oid, 'verification source blob mismatch')
    runtime_sha, checks_sha = [hashlib.sha256(v.encode()).hexdigest() for v in [runtime,checks]]
    native,full = guards.json('native-status.json'),guards.json('full-status.json')
    require(len(native) == 2 and {v['name'] for v in native} == {'clang','gcc'} and
            all(v['variants'] == ['Native','Scalar','Remainder','ScalarRemainder'] for v in native), 'incomplete native checks')
    require(len(full) == 9 and {v['name'] for v in full} == {'build','oracles','driver','bench','dag','phase4','manifest','headers','lines'}, 'incomplete project checks')
    require(all(v['exit_code'] == 0 and v['source_manifest_sha256'] == runtime_sha and v['checks_manifest_sha256'] == checks_sha and
                v['source_fingerprint'] == runtime_sha[:12] and v['checks_fingerprint'] == checks_sha[:12] for v in native+full), 'verification identity/result mismatch')
    for compiler in ['clang','gcc']:
        log = guards.text(compiler+'.log')
        require(len(re.findall(r'^check(?:Native|Scalar|Remainder|ScalarRemainder) ASan/UBSan$', log, re.M)) == 4, 'sanitizer observations missing')
        require(log.count('trie_selftest: maximum tree/stack, read-only guard pages and exact budgets passed') == 1, 'guarded trie probe missing')
    if args.current:
        identity = source_identity()
        require(identity['source_manifest_sha256'] == runtime_sha and identity['checks_manifest_sha256'] == checks_sha, 'current sources differ')
    campaigns = ['trie-bound/before-after','trie-wide/before-after','trie-wide/before-after-repeat',
                 'trie-global/combined','trie-global/combined-repeat','trie-global/early-stop','trie-direct/combined','trie-direct/control','trie-bounded/combined','trie-bounded/control']
    historical = list(campaigns)
    final_campaigns = ['trie-format/combined','trie-format/control']
    for capsule,names in [(data,historical),(format_data,final_campaigns)]:
        actual = {p.removesuffix('/metadata.json') for p in capsule.payloads if p.endswith('/metadata.json') and 'samples' in capsule.json(p)}
        require(actual == set(names), 'missing or unlisted campaign')
    campaigns = [(data,label) for label in historical] + [(format_data,label) for label in final_campaigns]
    results = [campaign(capsule,label,manifests) for capsule,label in campaigns]
    inputs = results[0][0]['input_sha256']
    cases = {(v['case'],v['family'],v['p']) for v in results[0][0]['samples']}
    require(all(r[0]['input_sha256'] == inputs and {(v['case'],v['family'],v['p']) for v in r[0]['samples']} == cases for r in results), 'campaign input suites differ')
    text = f'''# Reducer priority bounds and bounded native lookup

Reducer tries cache the minimum descendant-leaf priority in their existing
packed records. Validation checks each cache against its children. Lookup
skips a subtree that cannot improve the selected divisor and finishes when a
divisor attains the root bound. Zero retains the legacy unknown-bound meaning.
The independent unpruned traversal checks the selected reducer policy.
The final revision tests the global bound only on divisor selection, avoiding
an extra conditional on every node visit.

Validated views admit at most 16384 nodes and 16383 edges. Validation and a
complete query each inspect at most 32767 node/edge records. Native queries
use a fixed 16384-entry stack and 32768-unit bound, covering every admitted
view without discarded speculative work. Larger formats decline before traversal.
Earlier 4096-unit experiments and the conservative 2048-node dispatch stage
are superseded; all their completed observations remain available.

The final measured and verified runtime fingerprint is `{runtime_sha[:12]}`.
Final verification binds runtime and test-source blobs to recorded manifests.
All eight Clang/GCC sanitizer, SIMD/scalar and remainder variants and all nine
project checks pass. Earlier failed stale-cost/fixture-freshness gates are
retained separately. The fixture audit finds {fixture_counts['work']} changed
`work` values, {fixture_counts['serialWork']} `serialWork` values and
{fixture_counts['referenceWork']} `referenceWork` values, among {fixture_records} of 1134 records.
Every other field and basis agrees, and all changed work values decrease.
Verification collectors and their host-specific commands are bundled.

All sweeps use the same fourteen medium development inputs, seven families
at 32003 and 2147483647, grevlex and degree scheduling. Every run uses one
automatically leased CPU and one algorithm thread, with adjacent AB then BA.
All {sum(len(r[0]['samples']) for r in results)} processes and {28*len(results)} complete-basis comparisons are retained;
none failed or timed out. Campaigns are separate observations. The wide-view
stage and the superseded global-bound comparison each have one unchanged repeat;
none is pooled with its first observation.
Candidate time includes canonicalization, F4 and interreduction. Process time
also includes startup, parsing and full output under identical wrappers.
Certificate generation, independent verification and kernel checking are
outside timing. These inputs are not held out and establish no leadership.

| Campaign | Baseline → candidate | Process ratio | Candidate ratio | Charged work ratio | Process range | CPU | Peak RSS A/B KiB |
| --- | --- | ---: | ---: | ---: | --- | ---: | --- |
'''
    for (_,label),(metadata,analysis,candidate,work,_,_) in zip(campaigns,results):
        rss=analysis['peak_rss_kib']
        text += f"| `{label}` | `{metadata['baseline_source_fingerprint']}` → `{metadata['source_fingerprint']}` | {analysis['family_balanced_geomean']:.4f} | {candidate:.4f} | {work:.6f} | {analysis['minimum']:.3f}–{analysis['maximum']:.3f} | {metadata['cpu']} | {rss['A']}/{rss['B']} |\n"
    text += '\nThe medium sweeps did not encode any newly admitted 2049–16384-node views: allocation counters match the original 2048-node-format baseline under the ample measurement allowances. Their timing observations therefore do not measure full-F4 widening costs or benefits. Larger-format coverage comes from synthetic lookup kernels and representation/budget conformance tests. No real-system widening speedup is established.\n'
    text += '\nSmaller ratios mean less observed time or charged work. All non-work JSON fields and complete bases agree, including allocation counters. Shared-host variability remains in every observation; no significance threshold or causal attribution is inferred from these finite sweeps.\n'
    text += '\n| Final combined family | Process ratio |\n| --- | ---: |\n'
    for family,value in results[-2][1]['per_family'].items():
        text += f'| {family} | {value:.4f} |\n'
    text += '\nThe antichain kernel prepares n two-variable monomial reducers outside timing. The dispatch kernel uses native lookup at every declared size; the other kernel always uses the node traversal. The query admits every reducer; scanning the root edges and the first preferred branch takes n+4 charged units. It hashes the actual selected leading monomial and work. Native and portable traversals use separate fixed trial-major schedules, three trials at each declared size. All completed samples, including signal-floor flags, remain available. The table takes medians over every completed trial; the engine verdict omits samples flagged below its signal floor.\n\n| Reducers | Dispatch ms | Portable ms |\n| ---: | ---: | ---: |\n'
    kernels=[]
    ladder=[16,32,64,128,256,512,1024,2048]
    for label in ['native','portable']:
        prefix='trie-format/kernels/'+label
        metadata=format_data.json(prefix+'/metadata.json')
        require(metadata['exit_code'] == 0 and metadata['manifest'] == measured and metadata['binary_sha256'] == metadata['binary_sha256_after'] == latest['binary_sha256']['bench'], 'kernel source/binary mismatch')
        kernel=format_data.json(prefix+'/result.json')['results'][0]
        require([(p['trial_index'],p['param']) for p in kernel['points']] == [(t,n) for t in range(3) for n in ladder] and all(p['status']=='ok' for p in kernel['points']), 'incomplete kernel schedule')
        require(all(math.isclose(p['total_nanos']/p['inner_repeats'],p['per_call_nanos'],rel_tol=1e-12,abs_tol=1e-6) for p in kernel['points']), 'kernel normalization differs')
        kernels.append(kernel)
    require([(p['trial_index'],p['param'],p['result_hash']) for p in kernels[0]['points']] == [(p['trial_index'],p['param'],p['result_hash']) for p in kernels[1]['points']], 'kernel outputs differ')
    for n in ladder:
        values=[statistics.median(p['per_call_nanos'] for p in k['points'] if p['param']==n)/1e6 for k in kernels]
        text += f'| {n} | {values[0]:.6f} | {values[1]:.6f} |\n'
    text += '\nThese independent complexity runs are not a matched native/portable speedup experiment. '
    for label,kernel in zip(['Dispatch','Portable'],kernels):
        text += f"{label} lean-bench verdict: `{kernel['verdict']}`, normalized slope {kernel['slope']:.6f}, {sum(p['below_signal_floor'] for p in kernel['points'])} of 24 completed samples marked below the signal floor. "
    text = text.rstrip()
    text += '\n\nThe fastest-open-source milestone remains unestablished. These changes use available compiler/runtime facilities and establish no language impossibility. Issue #10987 remains open.\n'
    for label,path,capsule in [('Campaigns',args.archive,data),('Intermediate baseline',args.intermediate_baseline,intermediate),('Final baseline',args.final_baseline,baseline),('Final format measurements',args.format,format_data),('Fixture baseline',args.fixture_baseline,fixture_baseline),('Final verification',args.guards,guards)]:
        text += f'\n{label}: [{path.name}](raw/{path.name}), SHA-256 `{capsule.sha256}`, {capsule.count} payloads plus manifest.\n'
    text += f'\nRegenerate with `python3 scripts/bench/groebner_trie_report.py --archive {args.archive} --format {args.format} --fixture-baseline {args.fixture_baseline} --intermediate-baseline {args.intermediate_baseline} --final-baseline {args.final_baseline} --guards {args.guards} --report {args.report} --check`. Historical checks use archived blobs; add `--current` to require current runtime/test identity.\n'
    text += '\nThe earlier [verification capsule](raw/f4-trie-priority-checks-7affce133f75.tar.xz) is retained for the conservative dispatch snapshot.\n'
    if args.check:
        require(args.report.read_text() == text, 'report differs from verified data')
    else:
        args.report.write_text(text)
    print('trie-priority report verified' if args.check else 'trie-priority report generated')


if __name__ == '__main__':
    main()
