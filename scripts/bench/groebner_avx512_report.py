#!/usr/bin/env python3
"""Verify retained F4 packet experiments and regenerate their observations."""
import argparse
import hashlib
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import campaign, mean, require, source


def listing(text):
    return {line.split('\t',1)[1]:line.split(' ',2)[1] for line in text.splitlines()}


def kernels(capsule, baseline, prototype, shapes):
    meta = capsule.json(prototype+'/kernel-status.json')
    manifests = {arm:source(capsule,label) for arm,label in [('A',baseline),('B',prototype)]}
    require(meta['manifest']==manifests and meta['threads']==1, 'kernel provenance differs')
    require(meta['binary_sha256']==meta['binary_sha256_after']==
            {arm:m['binary_sha256']['bench'] for arm,m in manifests.items()}, 'kernel binary differs')
    expected = [f'complexity/{shape}/{arm}' for shape,_,_ in shapes for arm in ['A','B']]
    expected += [f'matched/{shape}/b{block}-{n}-{arm}' for block in [0,1]
                 for shape,_,sizes in shapes for n in sizes for arm in (['A','B'] if block==0 else ['B','A'])]
    samples = meta['samples']
    require([s['label'] for s in samples]==expected, 'kernel schedule differs')
    require(all(a['finished_ns']<=b['started_ns'] for a,b in zip(samples,samples[1:])), 'kernel calls overlap')
    points = {}
    for sample in samples:
        require(sample['exit_code'] in [0,2] and sample['cpu']==meta['samples'][0]['cpu'], 'kernel failure/CPU differs')
        record = capsule.json(prototype+'/kernels/'+sample['label']+'/result.json')['results'][0]
        shape = next(v for v in shapes if v[0]==sample['label'].split('/')[1])
        require(record['function']=='Hex.Groebner.Bench.'+shape[1], 'kernel function differs')
        p = record['points'];points[sample['label']] = p
        if sample['label'].startswith('complexity/'):
            require([(v['trial_index'],v['param']) for v in p]==[(t,n) for t in range(3) for n in shape[2]], 'trial-major ladder differs')
        else:
            require(len(p)==1 and p[0]['param']==int(sample['label'].split('-')[-2]), 'matched size differs')
        require(all(v['status']=='ok' and v['inner_repeats']>0 and
                    math.isclose(v['per_call_nanos'],v['total_nanos']/v['inner_repeats'],rel_tol=1e-8)
                    for v in p), 'kernel result/normalization differs')
    ratios = {}
    for shape,_,sizes in shapes:
        values=[];flags=0
        for block in [0,1]:
            for n in sizes:
                a,b = [points[f'matched/{shape}/b{block}-{n}-{arm}'][0] for arm in ['A','B']]
                require(a['result_hash']==b['result_hash'], 'complete kernel outputs differ')
                values.append(b['per_call_nanos']/a['per_call_nanos'])
                flags += a['below_signal_floor']+b['below_signal_floor']
        # Check all complexity hashes too, including every retained trial.
        for a,b in zip(points[f'complexity/{shape}/A'],points[f'complexity/{shape}/B']):
            require(a['result_hash']==b['result_hash'], 'complexity outputs differ')
        ratios[shape]=(mean(values),min(values),max(values),flags)
    return meta,ratios


def sweeps(capsule, baseline, prototype):
    manifests={m['source_fingerprint']:m for m in [source(capsule,baseline),source(capsule,prototype)]}
    results=[]
    for name in ['f4','f4-repeat']:
        label=prototype+'/'+name
        meta,analysis,candidate,work,lo,hi=campaign(capsule,label,manifests)
        require(work==1 and lo==hi==0, 'logical work or allocations changed')
        require(meta['requested_dense_pivots']=={'A':None,'B':None}, 'unexpected dense option')
        for case in {s['case'] for s in meta['samples']}:
            for block in [0,1]:
                outputs=[capsule.json(f'{label}/{case}-b{block}-{arm}.stdout') for arm in ['A','B']]
                for output in outputs:output.pop('candidateNanos')
                require(outputs[0]==outputs[1], 'complete non-time output differs')
        results.append((name,meta,analysis,candidate))
    return results


def guards(capsule, measured, current):
    for prefix in ['runtime','checks']:
        text=capsule.text(prefix+'.manifest')
        require(hashlib.sha256(text.encode()).hexdigest()[:12]==current['source_fingerprint' if prefix=='runtime' else 'checks_fingerprint'], 'guard manifest differs')
        for path,oid in listing(text).items():
            blob=capsule.read(prefix+'-sources/'+path)
            require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()==oid, 'guard source differs')
    a,b=listing(measured['source_manifest']),listing(capsule.text('runtime.manifest'))
    require(set(a)==set(b) and {p for p in a if a[p]!=b[p]}=={'HexGroebner/ffi/matrix_avx512_selftest.c'}, 'measured production sources changed')
    native,full=capsule.json('native-status.json'),capsule.json('full-status.json')
    require(len(native)==2 and len(full)==9 and {n['name'] for n in native}=={'clang','gcc'}, 'guard coverage differs')
    for row in native+full:
        require(row['exit_code']==0 and all(row[k]==v for k,v in current.items()), 'failed/stale guard')
    expected={'Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder'}
    require(all(set(row['variants'])==expected and set(row['sanitize'])=={'address','undefined'} for row in native), 'native variants differ')


def usage(capsule, prototype, metadata):
    records=capsule.json(prototype+'/usage/metadata.json')
    cases=sorted({sample['case'] for sample in metadata['samples']})
    require([record['case'] for record in records]==cases, 'usage coverage differs')
    counts=[]
    for record in records:
        case=record['case'];prefix=prototype+'/usage/'+case
        require(record['exit_code']==0, 'usage run failed')
        require(record['input_sha256']==metadata['input_sha256'][case+'.json'], 'usage input differs')
        actual=capsule.json(prefix+'.stdout');expected=capsule.json(prototype+'/f4/'+case+'-b0-B.stdout')
        actual.pop('candidateNanos');expected.pop('candidateNanos')
        require(actual==expected, 'untimed usage output differs')
        counters=capsule.json(prefix+'.stderr')
        require(counters==record['counters'], 'usage counters differ')
        count=int(counters['avx512Packets']);require(count>0, 'F4 input missed AVX-512')
        counts.append(count)
    return min(counts),max(counts)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['archive','report']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--current',action='store_true');p.add_argument('--check',action='store_true')
    args=p.parse_args();c=Capsule(args.archive)
    a,b='avx512-baseline','avx512-prototype'
    shapes=[('u16-dense','cauchy16',[64,128,256,512]),('u16-strided','cauchy16Strided',[64,128,256,512]),
            ('m31-dense','cauchy31',[64,128,256,512]),('m31-strided','cauchy31Strided',[64,128,256,512])]
    meta,ratios=kernels(c,a,b,shapes);runs=sweeps(c,a,b)
    require('AMD EPYC 9455' in c.text(b+'/hardware.txt'),'CPU model differs')
    profiles=c.json(b+'/profiles/metadata.json')
    require([(r['case'],r['arm']) for r in profiles['records']]==[(case,arm) for case in ['eco11-15','cyclic7-31'] for arm in ['A','B','B','A']], 'profile schedule differs')
    require(all(r['exit_code']==0 and r['binary_sha256']==source(c,a if r['arm']=='A' else b)['binary_sha256']['compute'] for r in profiles['records']), 'profile binary/failure differs')
    identity=c.json('identity.json');guards(c,source(c,b),identity)
    low_usage,high_usage=usage(c,b,runs[0][1])
    if args.current:
        current=source_identity()
        require(all(current[k]==v for k,v in identity.items() if k!='source_commit'),'current tree differs from verification')
    lines=['# Exact AVX-512 F4 row packets','',
           'Sixteen-lane canonical updates reduce the measured row-kernel times on this host. '
           'The two full-system campaigns do not establish an overall F4 speedup or the fastest-open-source milestone.','',
           'The native transition selects AVX-512 only after CPU and OS state checks. AVX2 and scalar fallbacks remain available. '
           'All packet validation precedes writes; a refused sixteen-lane packet falls back to eight-lane and scalar processing in order. '
           'Logical work, budgets, resumable state and complete non-time outputs agree.','',
           '## Retained kernel measurements','',
           f"Host `{meta['host']}` (AMD EPYC 9455); one algorithm thread, automatically leased CPU {meta['samples'][0]['cpu']}. "
           'Lean 4.35.0-rc3; Clang 23.1.3. Preparation is excluded; validation, allocation, elimination, decoding and full-output hashing are included. '
           'The registered cubic Cauchy families use fixed trial-major ladders and adjacent AB/BA comparisons, with a one-second batch target.','',
           '| Kernel | B/A geometric mean | Pair range | Below-signal flags |','|---|---:|---:|---:|']
    for name,(ratio,lo,hi,flags) in ratios.items():lines.append(f'| {name} | {ratio:.6f} | {lo:.6f}–{hi:.6f} | {flags} |')
    lines += ['', 'All 72 invocations, including 32 matched pairs and every complexity trial, are retained with equal complete-output hashes. No kernel repeat was needed.','',
              '## Full F4 candidate production','',
              'Both campaigns use the fixed seven-family, fourteen-input suite over 32003 and 2147483647, grevlex, degree scheduling, and one thread. '
              'Each campaign retains 56 processes in adjacent AB/BA order. The second is the single unchanged repeat after the first was inconclusive; '
              'the campaigns are reported separately. These are unchecked candidates. Certificate generation, independent native verification and kernel checking are excluded.','',
              '| Campaign | Process B/A | Candidate B/A | Process pair range | Peak RSS A/B (KiB) |','|---|---:|---:|---:|---:|']
    for name,_,analysis,candidate in runs:
        rss=analysis['peak_rss_kib'];lines.append(f"| {name} | {analysis['geomean']:.6f} | {candidate:.6f} | {analysis['minimum']:.6f}–{analysis['maximum']:.6f} | {rss['A']}/{rss['B']} |")
    lines += ['', 'All 112 completed processes (56 pairs) agree on complete bases and every non-time counter. There are no failures or timeouts. '
              'The small aggregate changes and broad pair ranges do not support an overall speed claim. '
              'Eight diagnostic cycle profiles retain fixed ABBA runs of Eco11 and Cyclic7, including raw perf data and outputs. '
              'They investigate the limited full-system effect, remain outside the timing ratios, and identify continuing row-scan work without establishing a language limitation.','',
              '## Verification and provenance','',
              'Clang and GCC each pass ASan/UBSan with AVX-512, forced AVX2, and scalar dispatch, with and without wide-integer reduction: twelve variants. '
              'The nine project gates include the executable/theory build, independent oracles, driver checks, benchmark verification, dependency/phase/manifest checks and source checks. '
              'Guarded standalone buffers cover all sixteen invalid lanes, source endpoints, strided/contiguous targets and narrow-gather refusal at the final cell. '
              'Instrumented full F4 tests require actual AVX-512 execution when supported. '
              f'An untimed instrumented replay of all fourteen sweep inputs records {low_usage}–{high_usage} sixteen-lane packets per input and agrees with every timed non-time output.','',
              f"Baseline runtime `{source(c,a)['source_fingerprint']}`; timed prototype `{source(c,b)['source_fingerprint']}`; "
              f"verified runtime `{identity['source_fingerprint']}`, checks `{identity['checks_fingerprint']}`. "
              'The sole runtime-manifest difference after timing expands the standalone selftest; production sources are identical. '
              'The capsule includes exact source blobs, compiler commands, build logs, toolchain pins, raw samples, RSS, failures and verification logs. '
              'An initial generated harness exceeded Lean’s recursion-depth limit; that failed build is retained under diagnostics. The isolated coverage helper resolves it.','',
              f'Capsule: `{args.archive.name}`; SHA-256 `{c.sha256}`.', '',
              'Regenerate with `python3 scripts/bench/groebner_avx512_report.py --archive '+str(args.archive)+' --report '+str(args.report)+' --check`.', '']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report is stale')
    else:args.report.write_text(text)


if __name__=='__main__':main()
