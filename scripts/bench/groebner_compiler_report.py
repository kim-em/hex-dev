#!/usr/bin/env python3
"""Verify retained compiler comparisons and regenerate their scoped report."""
import argparse
import hashlib
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import require,source,mean
from scripts.bench.groebner_avx512_report import kernels,sweeps,listing
from scripts.oracle.groebner_singular import polynomial,canonical

SHAPES=[('u16-dense','cauchy16',[64,128,256,512]),('u16-strided','cauchy16Strided',[64,128,256,512]),
        ('m31-dense','cauchy31',[64,128,256,512]),('m31-strided','cauchy31Strided',[64,128,256,512])]


def verify_guards(guards,science):
    identity=guards.json('identity.json')
    for label,key in [('runtime','source_fingerprint'),('checks','checks_fingerprint')]:
        text=guards.text(label+'.manifest')
        require(hashlib.sha256(text.encode()).hexdigest()[:12]==identity[key],'guard manifest differs')
        for name,oid in listing(text).items():
            data=guards.read(label+'-sources/'+name)
            require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,'guard source differs')
    native,full=guards.json('native-status.json'),guards.json('full-status.json')
    require(len(native)==2 and len(full)==9,'guard coverage differs')
    variants={'Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder'}
    for row in native+full:
        require(row['exit_code']==0 and all(row[k]==v for k,v in identity.items()),'failed/stale guard')
    require(all(set(row['variants'])==variants and set(row['sanitize'])=={'address','undefined'} for row in native),'native variants differ')
    cache=guards.json('native-compiler-option-cache-status.json')
    require([r['label']for r in cache]==['default','clang','cached','gcc','restored'],'compiler switch coverage differs')
    require(all(r['exit_code']==0 for r in cache),'compiler switch failed')
    for row in cache:
        if row['label']=='cached':require(row['mtime_before']==row['mtime_after'],'unchanged compiler rebuilt')
        elif row['label']!='default':require(all(row['mtime_before'][k]!=row['mtime_after'][k]for k in row['mtime_before']),'compiler switch was cached')
        version='16.2.0' if row['label']=='gcc' else 'clang version 23.1.3' if row['label']in ['clang','cached']else 'clang version 21.1.8'
        require(all(version in comment for comment in row['compiler_comments'].values()),'object compiler differs')
    require(cache[0]['object_sha256']==cache[-1]['object_sha256'],'restored compiler objects differ')
    measured=source(science,'native-cc-option')
    latest=source(guards,'native-cc-reviewed')
    default=source(guards,'native-cc-default')
    require(latest['source_manifest']==default['source_manifest']==guards.text('runtime.manifest'),'verified runtime differs')
    require(measured['binary_sha256']==latest['binary_sha256'] and
            source(science,'avx512-default')['binary_sha256']==default['binary_sha256'],'verified executables differ from timings')
    before,after=listing(measured['source_manifest']),listing(latest['source_manifest'])
    require(set(before)==set(after) and {p for p in before if before[p]!=after[p]}=={'scripts/bench/groebner_freeze.py'},'production code changed after timing')
    require(default['native_options']=={'hexGroebnerAVX512':False,'hexGroebnerCC':None},'default option differs')
    require(latest['native_options']['hexGroebnerCC']==latest['compilers']['native']['command'] and
            latest['native_options']['hexGroebnerAVX512'] is False,'override option differs')
    return identity,latest


def msolve(capsule):
    label='native-compiler23/msolve';meta=capsule.json(label+'/metadata.json');recorded=capsule.json(label+'/analysis.json')
    manifest=source(capsule,'native-compiler23')
    require(meta['source_fingerprint']==manifest['source_fingerprint'] and
            meta['source_manifest']==manifest['source_manifest'] and meta['source_unchanged'],'msolve source differs')
    require(meta['threads']==1 and meta['msolve_mode']==2 and meta['msolve_commit']=='3672113ee2c696a2ac9c637636e0f7214f500ba1','comparator configuration differs')
    require(meta['binary_sha256']==meta['binary_sha256_after'] and
            meta['msolve_engine_sha256']==meta['msolve_engine_sha256_after'] and meta['msolve_build']==meta['msolve_build_after'],'comparator build changed')
    for name,digest in meta['input_sha256'].items():
        require(hashlib.sha256(capsule.read(label+'/inputs/'+name)).hexdigest()==digest,'comparator input differs')
    samples=meta['samples'];index={(s['case'],s['block'],s['arm']):s for s in samples}
    order=[s['case']for s in samples if s['block']==0 and s['arm']=='A']
    require(len(index)==len(samples)==56 and len(set(order))==14,'comparator coverage differs')
    require([(s['case'],s['block'],s['arm'])for s in samples]==[(case,block,arm)for block in [0,1]for case in order for arm in (['A','B']if block==0 else ['B','A'])],'comparator adjacency differs')
    families={}
    for case in order:
        input_data=capsule.json(label+'/inputs/'+case+'.json')
        for block in [0,1]:
            a,b=[index[case,block,arm]for arm in ['A','B']]
            require(all(s['status']=='ok'and s['returncode']==0 and s['complete_basis_equal']for s in [a,b]),'comparator failed')
            command=b['command']
            require(all(command[command.index(flag)+1]==value for flag,value in [('-g','2'),('-t','1'),('-l','2')]),'msolve command differs')
            text=''.join(line for line in capsule.text(f'{label}/{case}-b{block}-B.basis').splitlines()if not line.startswith('#')).strip()
            require(text.startswith('[')and text.endswith(']:'),'invalid msolve output')
            body=text[1:-2].strip();basis=sorted(polynomial(p,input_data['variables'],input_data['p'])for p in body.split(','))if body else []
            output=capsule.json(f'{label}/{case}-b{block}-A.stdout')
            require(output['kind']=='unchecked_candidate'and canonical(output['basis'])==basis,'complete comparator bases differ')
            families.setdefault(a['family'],[]).append(a['wall_nanos']/b['wall_nanos'])
    ratio=mean([mean(v)for v in families.values()])
    require(len(families)==7 and all(len(v)==4 for v in families.values())and
            recorded['ratio_direction']=='Hex/msolve process'and math.isclose(ratio,recorded['family_balanced_geomean'],rel_tol=1e-12),'comparator ratio differs')
    return recorded,meta


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['science','guards','global-compiler','report']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--current',action='store_true');p.add_argument('--check',action='store_true');args=p.parse_args()
    science,guards,global_data=map(Capsule,[args.science,args.guards,args.global_compiler])
    meta,ratios=kernels(science,'avx512-default','native-cc-option',SHAPES)
    runs=sweeps(science,'avx512-default','native-cc-option')
    identity,latest=verify_guards(guards,science)
    a,b=[source(science,label)for label in ['avx512-default','native-cc-option']]
    require(a['compilers']['native']==b['compilers']['other_native'] and
            a['compilers']['lean']==b['compilers']['lean'],'override affected other compilers')
    if args.current:
        current=source_identity();require(all(current[k]==v for k,v in identity.items()if k!='source_commit'),'current sources differ')
    global_runs=sweeps(global_data,'avx512-default','native-compiler23')
    global_meta,global_ratios=kernels(global_data,'avx512-default','native-compiler23',SHAPES)
    comparison,comparison_meta=msolve(global_data)
    versions={key:value['version'].splitlines()[0]for key,value in b['compilers'].items()}
    lines=['# Groebner native compiler selection','',
           'The optional `hexGroebnerCC` Lake setting selects the compiler for the five Groebner native objects. '
           'The default remains `cc`; other libraries and Lean-generated C retain their existing compiler choices. '
           'The compiler path and flags participate in each object’s build trace.','',
           'Use `lake -R -KhexGroebnerCC=/absolute/path/to/clang build HexGroebner` and restore defaults with `lake -R build`. '
           'Lake retains configured options across later plain builds; reconfiguration resets other `-K` settings, which must be supplied again when needed. '
           'The freeze tool resolves compiler names before creating detached builds and records compiler versions, executable hashes, build options and supplied wrapper/config inputs.','',
           '## Scoped compiler comparison','',
           f"Host `{meta['host']}`; one algorithm thread and automatically leased CPUs recorded per campaign. "
           f"Groebner C: {versions['native']}; other native sources: {versions['other_native']}; Lean-generated C: {versions['lean']}. "
           'Both arms use identical inputs, grevlex, degree scheduling and complete unchecked-candidate output. '
           'Certificate generation, independent native verification and kernel replay are excluded from timing.','',
           '| Kernel | Override/default B/A | Pair range | Signal flags |','|---|---:|---:|---:|']
    for name,(ratio,lo,hi,flags,_)in ratios.items():lines.append(f'| {name} | {ratio:.6f} | {lo:.6f}–{hi:.6f} | {flags} |')
    lines+=['','All 72 kernel invocations (32 matched pairs plus complexity ladders) are retained, with equal complete-output hashes. '
            'The fixed trial-major ladders and adjacent AB/BA pairs use one-second batches; preparation is excluded and validation, allocation, elimination, decoding and complete-output hashing are included. '
            'Signal flags remain included and limit interpretation.','',
            '| Full F4 campaign | Process B/A | Candidate B/A | Process pair range | Peak RSS A/B (KiB) |','|---|---:|---:|---:|---:|']
    for name,_,analysis,candidate in runs:
        rss=analysis['peak_rss_kib'];lines.append(f"| {name} | {analysis['geomean']:.6f} | {candidate:.6f} | {analysis['minimum']:.6f}–{analysis['maximum']:.6f} | {rss['A']}/{rss['B']} |")
    lines+=['','Each campaign retains all 56 processes across fourteen inputs from seven families at 32003 and 2147483647. '
            'The second is the single unchanged repeat after an inconclusive first campaign. All 112 processes (56 pairs) agree on complete outputs and every non-time counter. '
            'There are no failures or timeouts. Broad pair ranges and the differing aggregate results do not establish an overall F4 speedup. '
            'The compiler control is optional and makes no fastest-open-source claim.','',
            '## Broader compiler experiment and remaining gap','',
            'A separate source-identical experiment changed the host `cc` for all native libraries to Clang 23.1.3, with the SDK compiler fixed. '
            'This is a different comparison from the Groebner-only option above; its samples are not pooled with it.','',
            '| Global-compiler campaign | Process B/A | Candidate B/A |','|---|---:|---:|']
    for name,_,analysis,candidate in global_runs:lines.append(f"| {name} | {analysis['geomean']:.6f} | {candidate:.6f} |")
    lines += ['',f"That broader build remains {comparison['family_balanced_geomean']:.6f}× slower than msolve in matched process time on this seven-family suite. "
              f"All {comparison['samples']} processes complete with {comparison['complete_bases_equal']} equal complete-basis pairs. "
              f"msolve revision `{comparison_meta['msolve_commit']}` uses Clang 23.1.3, native CPU tuning, deterministic elimination (`-l 2`), full reduced output (`-g 2`) and one thread. "
              'This comparator observation is not the Groebner-only build, does not cover held-out/hard acceptance families, and does not establish the full SPEC milestone.','',
              '## Verification and provenance','',
              'Clang/GCC ASan+UBSan pass twelve opt-in-AVX512/forced-AVX2/scalar and wide-reduction/remainder variants. '
              'All nine project gates pass, including the 2,264-target executable/theory build, independent oracles, driver checks, benchmark verification, DAG, phase, release manifest and source checks. '
              'The cache test switches default Clang 21 → Clang 23 → unchanged Clang 23 → GCC 16 → default Clang 21. '
              'Each changed selection rebuilds all five objects with matching ELF compiler records; the unchanged selection reuses them; restoring the default reproduces the original hashes.','',
              'Fresh final-source builds reproduce all measured executable hashes. The default executables match the earlier default baseline byte for byte. '
              'The post-measurement source difference only resolves compiler commands before detached builds; production algorithms and native C sources are unchanged. '
              'No additional timing samples were collected for that tool fix. Failed SDK-header and concurrent Git-index-lock setup attempts are retained as diagnostics and contribute no timing samples.','',
              f"Measured override runtime `{b['source_fingerprint']}`; verified runtime `{identity['source_fingerprint']}`, checks `{identity['checks_fingerprint']}`. "
              'The capsules retain exact source blobs, source manifests, compiler/wrapper inputs, raw samples, outputs, memory, host activity and verification logs. '
              'Collection scripts retain their recorded host paths; rerunning them elsewhere requires adapting those paths.','']
    for path,capsule in [(args.science,science),(args.guards,guards),(args.global_compiler,global_data)]:lines.append(f'`{path.name}`: SHA-256 `{capsule.sha256}`.')
    lines+=['',f'Regenerate with `python3 scripts/bench/groebner_compiler_report.py --science {args.science} --guards {args.guards} --global-compiler {args.global_compiler} --report {args.report} --check --current`.','']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report is stale')
    else:args.report.write_text(text)


if __name__=='__main__':main()
