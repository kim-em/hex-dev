#!/usr/bin/env python3
"""Replay exact wide-prime F4 source, conformance and adjacent comparisons."""
import argparse
import gc
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_parts import load_capsule
from scripts.bench.groebner_sparse_report import verification,fixed_inputs,systems,comparator,mean
from scripts.bench.groebner_trie_report import source,require


def digest(data):return hashlib.sha256(data).hexdigest()


def functional(cap,candidate,baseline):
    status=cap.json('functional/reimer/status.json')
    require(status['exit_code']==0 and status['sources_unchanged'] and
            status['source_bindings']==status['source_bindings_after'] and
            status['complete_basis_equal'] and status['all_statistics_equal'],
            'complete functional check failed')
    for path,value in status['source_bindings'].items():
        if path.endswith('/binaries/compute'):
            expected=candidate['binary_sha256']['compute']
        elif path.endswith('/manifest.json'):
            expected=digest(cap.read('candidate/manifest.json'))
        elif '/root-sources/' in path:
            expected=digest(cap.read('candidate/root-sources/'+path.split('/root-sources/',1)[1]))
        else:expected=digest(cap.read('functional/collector.py'))
        require(value==expected,'functional input binding differs')
    raw=cap.read('functional/reimer/run.stdout');old=cap.read('functional/reference/run.stdout')
    require(digest(raw)==status['actual_stdout_sha256'] and
            digest(old)==status['expected_stdout_sha256'],'functional output hash differs')
    a=json.loads(raw);b=json.loads(old)
    require(a['kind']=='unchecked_candidate' and a['p']==2147483647,'functional field differs')
    a.pop('candidateNanos');b.pop('candidateNanos')
    require(a==b,'functional outputs/counters differ')
    profile=cap.json('functional/reference/metadata.json')
    require(profile['manifest']==baseline and profile['run']['exit_code']==0 and
            profile['binary_sha256']==baseline['binary_sha256']['compute'],
            'functional baseline producer differs')
    require(cap.text('functional/driver.log').count(
        'candidate driver: 1134 complete corpus outputs/counters and input/resource boundaries passed')==2,
        'both complete driver checks missing')
    for compiler in ['clang','gcc']:
        require(cap.text('checks/regular/'+compiler+'.log').count(
            'PASS direct AVX512F guard-page wide-prime cases: 108')>=2,
            'direct eight-lane protected-boundary coverage missing')
    for i,(name,value)in enumerate(candidate['compiler_inputs'].items()):
        require(digest(cap.read('candidate/compiler-inputs/'+str(i)+'-'+Path(name).name))==value,
                'compiler input payload differs')
    require(len(candidate['compiler_inputs'])==2,'compiler wrapper/configuration inputs missing')


def kernels(cap,candidate,baseline):
    prefix='measurements/kernels';meta=cap.json(prefix+'/metadata.json')
    require(meta['manifests']==dict(A=baseline,B=candidate) and meta['threads']==1 and
            meta['sources_unchanged'] and meta['source_bindings']==meta['source_bindings_after'],
            'kernel source bindings differ')
    expected=[(block,f,n,arm)for block in [0,1]for f in ['bulkDelayedWord','bulkDelayedShort']
              for n in [128,256,512]for arm in (['A','B']if block==0 else['B','A'])]
    require([(r['block'],r['function'],r['param'],r['arm'])for r in meta['samples']]==expected,
            'kernel adjacent schedule differs')
    outputs={};indexed={}
    for row in meta['samples']:
        block,f,n,arm=row['block'],row['function'],row['param'],row['arm']
        require(row['exit_code']in [0,2] and meta['source_bindings'][row['command'][0]]==
                (baseline if arm=='A'else candidate)['binary_sha256']['bench'],
                'kernel executable or exit status differs')
        result=cap.json(prefix+f'/{f}-{n}-b{block}-{arm}/result.json')['results']
        require(len(result)==1 and len(result[0]['points'])==1,'kernel point missing')
        result=result[0];point=result['points'][0];config=result['config']
        require(point==row['point'] and point['status']=='ok' and point['param']==n and
                config['outer_trials']==1 and config['signal_floor_multiplier']==10 and
                config['target_inner_nanos']==4000000000 and config['max_seconds_per_call']==32,
                'kernel raw point/configuration differs')
        require(outputs.setdefault((f,n),point['result_hash'])==point['result_hash'],
                'complete kernel output hash differs')
        indexed[block,f,n,arm]=point
    lines=['','| Kernel | n | B/A pair ratios | Flagged samples |','|---|---:|---|---:|']
    for f in ['bulkDelayedWord','bulkDelayedShort']:
        for n in [128,256,512]:
            ratios=[];flags=0
            for block in [0,1]:
                a=indexed[block,f,n,'A'];b=indexed[block,f,n,'B']
                flags+=a['below_signal_floor']+b['below_signal_floor']
                ratios.append(b['per_call_nanos']/a['per_call_nanos'])
            lines.append(f"| {f} | {n} | "+', '.join(f'{v:.4f}'for v in ratios)+f' | {flags}/4 |')
    return lines+['','Kernel comparisons use existing input schedules, one leased CPU, four-second batches, a 32-second batch cap and the unchanged ten-times-spawn signal floor. Complete output/counter hashes agree. Flagged observations are retained and do not support a speed claim. These matched samples do not establish empirical complexity acceptance.','']


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['archive','heldout','report']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--check',action='store_true');parser.add_argument('--current',action='store_true')
    args=parser.parse_args();cap=load_capsule(args.archive)
    candidate=source(cap,'candidate');baseline=source(cap,'baseline')
    checks=verification(cap,candidate);fixed=fixed_inputs(cap);functional(cap,candidate,baseline)
    ratios,samples=systems(cap,candidate,baseline,fixed)
    lines=['# Eight-lane wide-prime delayed updates','',
        f"Frozen source `{candidate['source_fingerprint']}` is compared directly with `{baseline['source_fingerprint']}`. Four-byte coefficient updates use eight exact AVX-512F lanes only after CPU/OS capability checks and when a complete packet exists. Consecutive columns use unaligned vector loads/stores; other columns use gathers/scatters. AVX2 and portable fallbacks remain available. Each lane stays below p² after one correction because its sum is below 2p² < 2⁶³. Admission limits, row order, sugar labels and logical counters are preserved.",'',
        'All 128 system processes and 64 adjacent AB/BA pairs have identical complete outputs and counters. The fixed selection covers the first primary size of ten families in all three fields, plus Eco-14/Eco-15 over F₂.','',
        '| Field | Candidate B/A | Process B/A | Candidate pair range | Peak RSS A/B, KiB |',
        '|---|---:|---:|---:|---:|']
    for p in [2,32003,2147483647]:
        selected=[r for r in ratios if r['p']==p and r['case']not in ['eco14-2','eco15-2']]
        require(len(selected)==20,'field/family coverage differs')
        values=[r['candidate_ratio']for r in selected]
        rss={arm:max(r['peak_rss_kib']for r in samples if r['p']==p and r['arm']==arm and
                 r['case']not in ['eco14-2','eco15-2'])for arm in ['A','B']}
        lines.append(f"| {p} | {mean(values):.4f} | {mean([r['process_ratio']for r in selected]):.4f} | {min(values):.4f}–{max(values):.4f} | {rss['A']}/{rss['B']} |")
    lines+=['','These are descriptive point estimates on the shared AMD EPYC 9455 host. Unchanged F₂ and smaller-prime controls, every completed observation, outlier and failure are retained. No control-adjusted or multiplied-stage improvement is inferred. Runs use one leased CPU, one thread, degree scheduling, batch size 1024, binary pivots and delayed reduction enabled, and dense pivots disabled. Limits are 300 seconds, 8 GiB address space and 256 MiB output per process, with the fixed corpus’s explicit parent allowances. Native code uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0 with Lean 4.35.0-rc3.','',
        'All nine project checks and 36 strict Clang/GCC sanitizer configurations are source-bound. Protected-page tests call the actual eight-lane kernel on three wide primes, contiguous/strided columns and packet/tail lengths. Both complete 1,134-case drivers, independent oracles, downstream replay and axiom audits remain distinct from candidate timings. The collector journals exact samples and publishes atomic checkpoints before its final analysis.','']
    lines+=kernels(cap,candidate,baseline)
    lines += [f'Production stream SHA-256: `{cap.sha256}`.','']
    text='\n'.join(lines);del cap;gc.collect()
    held=load_capsule(args.heldout);result=comparator(held,candidate,[c for c in fixed if c['split']=='heldout'])
    lines=['','| Held-out family | Hex/msolve process ratio |','|---|---:|']
    for family,value in result['per_family'].items():lines.append(f'| {family} | {value:.4f} |')
    lines+=['',f"The 27 held-out inputs have 108 successful processes and 54 equal complete bases. The family-balanced Hex/msolve process ratio is {result['family_balanced_geomean']:.4f}×; peak RSS is {result['peak_rss_kib']['A']}/{result['peak_rss_kib']['B']} KiB.",'',
        'The comparator is msolve 3672113ee2c696a2ac9c637636e0f7214f500ba1, Clang 23.1.3, -O3 -march=native, full reduced output, linear algebra mode 2 and one thread. Candidate production excludes certificate generation, independent native certification and kernel checking. Full balanced solved coverage, equal-thread parallel comparisons, finite extensions, producer correctness/termination and fastest-open-source acceptance remain required by issue #10987. These data establish no language/runtime limitation. Scientific claims never rely on CI timing.','',f'Held-out stream SHA-256: `{held.sha256}`.','']
    text+='\n'.join(lines)
    if args.current:
        from scripts.bench.groebner_checks import CHECKS,source_identity
        from scripts.bench.groebner_measure import FAMILY
        from scripts.bench.sweep_freshness import index_listing
        source_identity();require(index_listing(FAMILY)==candidate['source_manifest'] and
            index_listing(CHECKS)==checks,'current runtime/verification sources differ')
    if args.check:require(args.report.read_text()==text,'report differs from retained evidence')
    else:args.report.write_text(text)
    print('PASS wide-prime source, full-output, kernel and comparator evidence replay')

if __name__=='__main__':main()
