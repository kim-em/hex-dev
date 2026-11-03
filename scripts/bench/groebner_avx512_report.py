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
        require(record['config']['target_inner_nanos']==1000000000,'kernel batch target differs')
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
        per_size={n:mean([points[f'matched/{shape}/b{block}-{n}-B'][0]['per_call_nanos']/points[f'matched/{shape}/b{block}-{n}-A'][0]['per_call_nanos'] for block in [0,1]]) for n in sizes}
        ratios[shape]=(mean(values),min(values),max(values),flags,per_size)
    return meta,ratios


def sweeps(capsule, baseline, prototype):
    a,b=source(capsule,baseline),source(capsule,prototype)
    manifests={m['source_fingerprint']:m for m in [a,b]}
    results=[]
    for name in ['f4','f4-repeat']:
        label=prototype+'/'+name
        meta,analysis,candidate,work,lo,hi=campaign(capsule,label,manifests,baseline=a,current=b)
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
    require(set(a)==set(b) and {p for p in a if a[p]!=b[p]} in [set(),{'HexGroebner/ffi/matrix_avx512_selftest.c'}], 'measured production sources changed')
    native,full=capsule.json('native-status.json'),capsule.json('full-status.json')
    require(len(native)==2 and len(full)==9 and {n['name'] for n in native}=={'clang','gcc'}, 'guard coverage differs')
    for row in native+full:
        require(row['exit_code']==0 and all(row[k]==v for k,v in current.items()), 'failed/stale guard')
    expected={'Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder'}
    require(all(set(row['variants'])==expected and set(row['sanitize'])=={'address','undefined'} for row in native), 'native variants differ')


def usage(capsule, prototype, metadata):
    records=capsule.json(prototype+'/usage/metadata.json')
    cases=sorted({sample['case'] for sample in metadata['samples']})
    compilers=['clang','gcc'] if 'compiler' in records[0] else ['']
    require(sorted((record['case'],record.get('compiler','')) for record in records)==
            [(case,cc) for case in cases for cc in compilers], 'usage coverage differs')
    counts=[];indexed={}
    for record in records:
        case=record['case'];cc=record.get('compiler','')
        prefix=prototype+'/usage/'+(cc+'/' if cc else '')+case
        require(record['exit_code']==0, 'usage run failed')
        require(record['input_sha256']==metadata['input_sha256'][case+'.json'], 'usage input differs')
        actual=capsule.json(prefix+'.stdout');expected=capsule.json(prototype+'/f4/'+case+'-b0-B.stdout')
        actual.pop('candidateNanos');expected.pop('candidateNanos')
        require(actual==expected, 'untimed usage output differs')
        counters=capsule.json(prefix+'.stderr')
        require(counters==record['counters'], 'usage counters differ')
        count=int(counters['avx512Packets']);require(count>0, 'F4 input missed AVX-512')
        counts.append(count);indexed[case,cc]=counters
    if len(compilers)==2:
        require(all(indexed[case,'clang']==indexed[case,'gcc'] for case in cases),'compiler packet counts differ')
    return min(counts),max(counts)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['archive','review','report']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--current',action='store_true');p.add_argument('--check',action='store_true')
    args=p.parse_args();initial,review=Capsule(args.archive),Capsule(args.review)
    shapes=[('u16-dense','cauchy16',[64,128,256,512]),('u16-strided','cauchy16Strided',[64,128,256,512]),
            ('m31-dense','cauchy31',[64,128,256,512]),('m31-strided','cauchy31Strided',[64,128,256,512])]
    data=[]
    for title,c,a,b in [('Original source',initial,'avx512-baseline','avx512-prototype'),
                        ('Opt-in source',review,'avx512-default','avx512-optin')]:
        meta,ratios=kernels(c,a,b,shapes);runs=sweeps(c,a,b)
        data.append((title,c,a,b,meta,ratios,runs))
    current=review.json('identity.json');guards(review,source(review,'avx512-optin'),current)
    if args.current:
        identity=source_identity()
        require(all(identity[k]==v for k,v in current.items() if k!='source_commit'),'current tree differs from verification')
    default,enabled=[source(review,label) for label in ['avx512-default','avx512-optin']]
    require(default['native_options']=={'hexGroebnerAVX512':False} and
            enabled['native_options']=={'hexGroebnerAVX512':True},'build option differs')
    require(default['source_manifest']==enabled['source_manifest'] and default['compilers']==enabled['compilers'], 'source/compiler arms differ')
    require(default['binary_sha256']==source(initial,'avx512-baseline')['binary_sha256'], 'default binaries changed')
    for label,m in [('avx512-default',default),('avx512-optin',enabled)]:
        for i,(path,digest) in enumerate(m['compiler_inputs'].items()):
            require(hashlib.sha256(review.read(label+f'/compiler-inputs/{i}-'+Path(path).name)).hexdigest()==digest,'external compiler input differs')
    for compiler in ['clang','gcc']:
        log=review.text(compiler+'.log')
        require(log.count('available=true; width/layout bits=63')==2 and
                log.count('available=false; width/layout bits=0')==4,'dispatch coverage differs')
    mutations=review.json('mutations/status.json')
    require(len(mutations)==6 and all(row['exit_code']!=0 for row in mutations),'boundary mutation escaped')
    header=review.text('runtime-sources/HexGroebner/ffi/matrix_avx512.h')
    test=review.read('runtime-sources/HexGroebner/ffi/matrix_avx512_selftest.c')
    for row in mutations:
        require(row['source_header_sha256']==hashlib.sha256(header.encode()).hexdigest() and
                row['test_sha256']==hashlib.sha256(test).hexdigest(),'mutation source differs')
        require(review.text('mutations/'+row['name']+'/matrix_avx512.h')==header.replace(row['old'],row['new']), 'mutant transformation differs')
    cache=review.json('cache-status.json')
    require([row['label'] for row in cache]==['unchanged','header-change','restored'] and
            cache[0]['mtime_before']==cache[0]['mtime_after'] and
            all(row['mtime_before']!=row['mtime_after'] for row in cache[1:]) and
            cache[0]['object_sha256']==cache[-1]['object_sha256'],'cache invalidation differs')
    dispatch=review.json('avx512-optin/dispatch-status.json')
    require([len(row['symbols']) for row in dispatch]==[0,4] and
            all(row['binary_sha256']==source(review,row['label'])['binary_sha256']['compute'] for row in dispatch),'build-option dispatch differs')
    profiles=initial.json('avx512-prototype/profiles/metadata.json')
    require([(r['case'],r['arm']) for r in profiles['records']]==[(case,arm) for case in ['eco11-15','cyclic7-31'] for arm in ['A','B','B','A']], 'profile schedule differs')
    require(all(r['exit_code']==0 and r['binary_sha256']==source(initial,'avx512-baseline' if r['arm']=='A' else 'avx512-prototype')['binary_sha256']['compute'] for r in profiles['records']), 'profile binary/failure differs')
    for label,record in review.json('avx512-optin/historical-binary-compilers.json').items():
        require(record['binary_sha256']==source(initial,label)['binary_sha256']['compute'] and
                'clang version 21.1.8' in record['comments'] and 'clang version 23.1.0' in record['comments'],'historical ELF compiler record differs')
    cpu=next(line.split(':',1)[1].strip() for line in review.text('avx512-optin/hardware.txt').splitlines() if line.startswith('Model name:'))
    versions={kind:value['version'].splitlines()[0] for kind,value in enabled['compilers'].items()}
    lines=['# Exact AVX-512 F4 row packets','',
           'Sixteen-lane updates are opt-in. The measured row kernels improve on this host; the full-system campaigns do not establish an overall F4 speedup or the fastest-open-source milestone.','',
           'Enable with `lake -R -KhexGroebnerAVX512=true build`; restore the default with `lake -R build`. '
           'CPU/OS checks additionally require AVX-512F/DQ/BW/VL and enabled YMM/ZMM state. AVX2 and scalar fallbacks remain available. '
           'Every packet validates before writing; refusal preserves the eight-lane/scalar failure prefix, work, budgets and resumable state. '
           'The optional dense-pivot cache retains its AVX2 path.','',
           f"Host `{data[-1][4]['host']}` ({cpu}); one algorithm thread, automatically leased CPUs recorded per campaign. "
           f"Toolchain `{enabled['toolchain']}`. Native C: {versions['native']}; Lean-generated C: {versions['lean']}. "
           'Sanitizer checks separately use Clang 23.1.3 and GCC 16.2.0. The original ELF compiler records also contain native Clang 21.1.8 and SDK Clang 23.1.0; '
           'the sanitizer compiler version must not be treated as the production compiler.','',
           '## Retained kernel measurements','',
           'Preparation is excluded; validation, allocation, elimination, decoding and complete-output hashing are included. '
           'The cubic Cauchy families use fixed trial-major ladders and adjacent AB/BA pairs, with one-second batches. '
           'Each source retains 72 invocations and 32 matched pairs, including all signal flags and every complexity trial. '
           'Exit code 2 is retained as a benchmark verdict, never treated as a successful operation by itself: every individual result must have status `ok`.','',
           '| Source / kernel | B/A mean | Pair range | Flags | n=64 | 128 | 256 | 512 |',
           '|---|---:|---:|---:|---:|---:|---:|---:|']
    for title,_,_,_,_,ratios,_ in data:
        for name,(ratio,lo,hi,flags,sizes) in ratios.items():
            lines.append(f'| {title} / {name} | {ratio:.6f} | {lo:.6f}–{hi:.6f} | {flags} | '+' | '.join(f'{sizes[n]:.6f}' for n in [64,128,256,512])+' |')
    lines += ['', 'All complete-output hashes agree. The original source used automatic sixteen-lane dispatch; the revised source uses the explicit build option. '
              'No timings are pooled across sources or campaigns. '
              f"The {sum(value[3] for *_,ratios,_ in data for value in ratios.values())} matched samples carrying below-signal flags remain in the ratios; those observations have that limitation. "
              'Performance on other microarchitectures, one-byte coefficients and generic four-byte Montgomery kernels remains unevaluated.','',
              '## Full F4 candidate production','',
              'Each campaign uses the fixed seven-family, fourteen-input suite over 32003 and 2147483647, grevlex, degree scheduling, and one thread. '
              'Each source has one first campaign and exactly one unchanged repeat after an inconclusive result, retaining all 56 processes per campaign in adjacent AB/BA order. '
              'These are unchecked candidates; certificate generation, independent native verification and kernel checking are excluded from timing.','',
              '| Source / campaign | Process B/A | Candidate B/A | Process pair range | Peak RSS A/B (KiB) |',
              '|---|---:|---:|---:|---:|']
    for title,_,_,_,_,_,runs in data:
        for name,_,analysis,candidate in runs:
            rss=analysis['peak_rss_kib'];lines.append(f"| {title} / {name} | {analysis['geomean']:.6f} | {candidate:.6f} | {analysis['minimum']:.6f}–{analysis['maximum']:.6f} | {rss['A']}/{rss['B']} |")
    lines += ['', 'All 224 completed processes (112 pairs) agree on complete bases and every non-time counter, with no failures or timeouts. '
              'The small aggregate changes and broad pair ranges do not establish an overall speed claim. '
              'The revised default executables, including the benchmark executable, are byte-for-byte identical to the original baseline. '
              'The original capsule also retains eight fixed ABBA diagnostic cycle profiles of Eco11 and Cyclic7; these remain outside timing ratios and do not establish a language limitation.','',
              '## Verification and provenance','',
              'Clang and GCC each pass ASan/UBSan for opt-in AVX-512, forced AVX2 and scalar dispatch, with and without wide-integer reduction: twelve variants. '
              'The nine project gates cover the executable/theory build, independent oracles, drivers, benchmark verification, dependency/phase/manifest checks and source checks. '
              'The expanded standalone test exhausts one-byte arithmetic and checks deterministic factors, random odd moduli, all sixteen invalid lanes, exact gather-padding boundaries, out-of-range columns, cross-packet ordering and mode admission. '
              'Six deliberately broken guards each fail that test. The compiled harness checks all six sixteen-lane width/layout paths and full F4 execution. '
              '`HEX_GROEBNER_REQUIRE_AVX512=1` requires hardware coverage in manual runs; hosted CI does not promise that ISA.','']
    for title,c,a,b,_,_,runs in data:
        lo,hi=usage(c,b,runs[0][1]);lines.append(f"{title}: baseline `{source(c,a)['source_fingerprint']}`, candidate `{source(c,b)['source_fingerprint']}`; instrumented sweep replays record {lo}–{hi} sixteen-lane packets per input and equal non-time output.")
        lines.append('')
    lines += [f"Verified runtime `{current['source_fingerprint']}`, checks `{current['checks_fingerprint']}`. "
              'The revised packet-count driver is generated by committed code and replayed under both compilers. '
              'Both the production object and retained probe objects track the new header; an unchanged probe is cached, a header edit rebuilds it, and restoring the header rebuilds the identical original object. '
              'Capsules include exact source blobs, native build options, external compiler inputs, raw samples, RSS and verification logs. '
              'The original capsule retains the failed recursion-depth build under diagnostics; its test driver was split into a smaller helper.','',
              f'Original capsule: `{args.archive.name}`, SHA-256 `{initial.sha256}`.',
              f'Revised capsule: `{args.review.name}`, SHA-256 `{review.sha256}`.','',
              f'Regenerate with `python3 scripts/bench/groebner_avx512_report.py --archive {args.archive} --review {args.review} --report {args.report} --check --current`.', '']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report is stale')
    else:args.report.write_text(text)


if __name__=='__main__':main()
