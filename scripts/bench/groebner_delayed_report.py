"""Replay complete outputs and source bindings for exact delayed F4 elimination."""
from __future__ import annotations
import argparse
import hashlib
import math
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_json import loads


def require(condition,message):
    if not condition:raise ValueError(message)


def gm(values):
    require(bool(values) and all(x>0 for x in values),'invalid geometric-mean samples')
    return math.exp(sum(map(math.log,values))/len(values))


def bind_sources(cap,stage):
    manifest=cap.json(stage+'/freeze/manifest.json')
    listing=manifest['source_manifest']
    require(hashlib.sha256(listing.encode()).hexdigest().startswith(manifest['source_fingerprint']),
            'source family fingerprint differs')
    for line in listing.splitlines():
        geometry,name=line.split('\t',1);mode,digest,index=geometry.split()
        require(mode in ['100644','100755']and index=='0','unsupported source entry')
        data=cap.read(stage+'/sources/'+name)
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(actual==digest,'source blob differs: '+name)
    status=cap.json(stage+'/checks/native-status.json')
    require(len(status)==2 and {r['name']for r in status}=={'clang','gcc'},'missing compiler profiles')
    for row in status:
        require(row['exit_code']==0 and row['source_commit']==manifest['commit'],
                'native check identity or result differs')
        require(row['source_fingerprint']==manifest['source_fingerprint'],'native runtime differs')
        require(len(row['variants'])==6 and row['sanitize']==['address','undefined'],
                'missing native variants/sanitizers')
    checks=cap.text(stage+'/checks/source-manifest.txt')
    require(all(hashlib.sha256(checks.encode()).hexdigest().startswith(r['checks_fingerprint'])
                for r in status),'verification fingerprint differs')
    for line in checks.splitlines():
        geometry,name=line.split('\t',1);_,digest,index=geometry.split()
        data=cap.read(stage+'/check-sources/'+name)
        require(index=='0'and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==digest,
                'verification source differs: '+name)
    return manifest


def payload(cap,prefix,row):
    name=row['case']+f"-b{row['block']}-{row['arm']}.stdout"
    return cap.json(prefix+'/'+name)


def systems(cap,prefix,manifest):
    meta=cap.json(prefix+'/metadata.json');rows=meta['samples'];cases=meta['cases']
    require(len(cases)==30 and len(rows)==120,'incomplete fixed first-size coverage')
    require(len({c['family']for c in cases})==10,'family coverage differs')
    require(meta['source_bindings']==meta['source_bindings_after'],'measured bindings changed')
    require(meta['manifest']['binary_sha256']['compute']==manifest['binary_sha256']['compute'],
            'measured executable differs')
    seen=set();ratios=[];outputs={}
    for case in cases:
        for block in [0,1]:
            pair={r['arm']:r for r in rows if r['case']==case['name']and r['block']==block}
            require(set(pair)=={'A','B'},'missing pair')
            values={}
            for arm,row in pair.items():
                key=case['name'],block,arm;require(key not in seen,'duplicate sample');seen.add(key)
                require(row['status']=='ok'and row['returncode']==0 and
                        row['complete_output_and_counters_equal'],'failed or unequal process')
                command=row['command'];require(command[command.index('--delayed-reduction')+1]==
                                              ('true'if arm=='B'else'false'),'option ignored')
                value=payload(cap,prefix,row);require(value['kind']=='unchecked_candidate','wrong candidate kind')
                for option,expected in [('--batch-size','1024'),('--scheduling','degree'),
                                        ('--binary-pivots','true'),('--dense-pivots','false')]:
                    require(command[command.index(option)+1]==expected,'recorded control differs: '+option)
                require(value['batchSize']==1024 and value['scheduling']=='degree'and
                        value['binaryPivots']is True and value['order']=='grevlex'and
                        value['variables']==case['variables']and value['randomState']==0,
                        'candidate output contract differs')
                require(value['p']==case['p']and value['delayedReduction']==(arm=='B'),
                        'field or requested policy differs')
                require(value['candidateNanos']==row['candidate_nanos'],'candidate timing differs')
                require(value['candidateNanos']>0 and row['wall_nanos']>0,'invalid timing')
                values[arm]=value
                outputs[key]={k:v for k,v in value.items()if k not in ['candidateNanos','delayedReduction']}
            require(outputs[case['name'],block,'A']==outputs[case['name'],block,'B'],
                    'complete output or logical counters differ')
            ratios.append(dict(case=case['name'],family=case['family'],p=case['p'],
                               process=pair['B']['wall_nanos']/pair['A']['wall_nanos'],
                               candidate=values['B']['candidateNanos']/values['A']['candidateNanos']))
    require(len(seen)==120,'unexpected sample positions')
    return ratios,outputs


def kernels(cap,prefix,manifest,signal,sizes=(128,256,512)):
    meta=cap.json(prefix+'/metadata.json')
    require(meta['manifest']['binary_sha256']['bench']==manifest['binary_sha256']['bench'],
            'kernel executable differs')
    require(meta['source_bindings']==meta['source_bindings_after'],'kernel sources changed')
    require(len(meta['samples'])==42,'incomplete kernel schedule')
    result=[]
    for shape in ['Byte','Short','Word']:
        for arm in ['A','B']:
            item=cap.json(prefix+f'/complexity/{shape}/{arm}/result.json')['results'][0]
            require(len(item['points'])==9,'complexity trials missing')
            if signal:require(all(not p['below_signal_floor']for p in item['points']),
                              'complexity point below signal floor')
        for n in sizes:
            hashes=set();values={a:[]for a in ['A','B']}
            for block in [0,1]:
                for arm in ['A','B']:
                    item=cap.json(prefix+f'/matched/{shape}/b{block}-{n}-{arm}/result.json')['results'][0]
                    require(len(item['points'])==1,'unexpected matched points');point=item['points'][0]
                    require(point['status']=='ok','kernel failed')
                    if signal:require(not point['below_signal_floor'],'matched point below signal floor')
                    hashes.add(point['result_hash']);values[arm].append(point['per_call_nanos'])
            require(len(hashes)==1,'complete output digest differs')
            result.append((shape,n,gm(values['B'])/gm(values['A'])))
    return result



def giac(cap,prefix,outputs):
    meta=cap.json(prefix+'/metadata.json');rows=meta['samples']
    require(len(rows)==120 and meta['sources_unchanged'],'incomplete or changed comparator campaign')
    require(meta['source_bindings']==meta['source_bindings_after'],'comparator sources changed')
    def canonical(basis):
        return sorted(sorted((tuple(e),int(c))for e,c in f)for f in basis if f)
    for case in meta['cases']:
        for block in [0,1]:
            pair={r['arm']:r for r in rows if r['case']==case['name']and r['block']==block}
            require(set(pair)=={'A','B'},'missing independent comparator pair')
            values={}
            for arm,row in pair.items():
                require(row['status']=='ok'and row['returncode']==0 and row['complete_basis_equal'],
                        'failed or unequal comparator result')
                values[arm]=payload(cap,prefix,row)
            require(canonical(values['A']['basis'])==canonical(values['B']['basis']),
                    'independent complete basis differs')
            current=outputs[case['name'],block,'B']
            require({k:v for k,v in values['A'].items()if k not in ['candidateNanos','delayedReduction']}==current,
                    'independently compared candidate differs from final logical output')



HEADER_OLD = '''target hexgroebnerEliminationO pkg : FilePath := do
  let source ← inputTextFile <| pkg.dir / "HexGroebner" / "ffi" / "matrix_eliminate.c"
  let header ← inputTextFile <| pkg.dir / "HexGroebner" / "ffi" / "matrix_runtime.h"
  let inputs := source.zipWith (fun source _ => source) header'''
HEADER_NEW = '''target hexgroebnerEliminationO pkg : FilePath := do
  let source ← inputTextFile <| pkg.dir / "HexGroebner" / "ffi" / "matrix_eliminate.c"
  let header ← inputTextFile <| pkg.dir / "HexGroebner" / "ffi" / "matrix_runtime.h"
  let simd ← inputTextFile <| pkg.dir / "HexGroebner" / "ffi" / "matrix_simd.h"
  let inputs := (source.zipWith (fun source _ => source) header).zipWith
    (fun source _ => source) simd'''


def configuration(cap,original,audit_path):
    audit=Capsule(audit_path);manifest=audit.json('manifest.json')
    require(manifest['binary_sha256']==original['binary_sha256'],'audited executable bytes differ')
    require(manifest['compilers']==original['compilers']and manifest['native_options']==original['native_options'],
            'audited compiler or ISA controls differ')
    old={line.split('\t',1)[1]:line.split()[1]for line in original['source_manifest'].splitlines()}
    new={line.split('\t',1)[1]:line.split()[1]for line in manifest['source_manifest'].splitlines()}
    require(set(old)==set(new),'audited source set differs')
    require({name for name in old if old[name]!=new[name]}=={'lakefile.lean'},'unexpected audited source change')
    for name,digest in new.items():
        data=audit.read('sources/'+name)
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==digest,
                'audited source blob differs')
    old_lake=cap.text('reviewed/sources/lakefile.lean')
    require(HEADER_OLD in old_lake and old_lake.replace(HEADER_OLD,HEADER_NEW)==audit.text('sources/lakefile.lean'),
            'header dependency change differs')
    require(audit.text('checks/source-manifest.txt')==cap.text('reviewed/checks/source-manifest.txt'),
            'verification sources changed')
    status=audit.json('checks/status.json')
    require([r['name']for r in status]==['dag','phase4','manifest','headers','lines']and
            all(r['exit_code']==0 and r['source_fingerprint']==manifest['source_fingerprint']for r in status),
            'audited project checks failed or used different sources')
    return manifest,audit


def render(path,replay_path,audit_path):
    cap=Capsule(path);replay=Capsule(replay_path)
    manifests={s:bind_sources(cap,s)for s in ['initial','packets','reviewed']}
    require(manifests['initial']['binary_sha256']['compute']==manifests['packets']['binary_sha256']['compute'],
            'initial/packet F4 code differs')
    current,audit=configuration(cap,manifests['reviewed'],audit_path)
    first,first_outputs=systems(cap,'measurements/initial-system',manifests['initial'])
    final,outputs=systems(cap,'measurements/reviewed-system',manifests['reviewed'])
    require(first_outputs==outputs,'logical behavior changed between production stages')
    giac(cap,'measurements/giac-process-diagnostic',outputs)
    kernels(cap,'measurements/inconclusive-kernels',manifests['packets'],False)
    kernels(cap,'measurements/packet-kernels',manifests['packets'],True)
    matrix=kernels(cap,'measurements/reviewed-kernels',manifests['reviewed'],True)
    full=cap.json('reviewed/full/status.json')
    require([r['name']for r in full]==['build','oracles','driver','bench','dag','phase4','manifest','headers','lines'],
            'missing project gates')
    require(all(r['exit_code']==0 and r['source_fingerprint']==manifests['reviewed']['source_fingerprint']
                for r in full),'project gate failed or used different runtime')
    diagnostic=cap.json('measurements/refusals/metadata.json')
    require(diagnostic['complete_output_and_counters_equal']and diagnostic['exit_code']==0,
            'instrumented producer differs')
    require({k:int(v)for k,v in diagnostic['native'].items()}['delayedRefusedWork']==0,
            'native charged work was discarded')
    require(int(diagnostic['native']['bulkAccepted'])==61 and int(diagnostic['native']['bulkDeclined'])==0,
            'instrumented matrix coverage differs')
    replay_ratios={}
    for stage in ['v1','v2']:
        rows=replay.json('measurements/'+stage+'/samples.json')
        require(len(rows)==4 and all(r['exit_code']==0 and r['result']['completeOutputAndCountersEqual']
                                    for r in rows),'experimental replay incomplete or unequal')
        replay_ratios[stage]=gm([r['result']['candidateNanos']for r in rows if r['arm']=='B'])/gm(
            [r['result']['candidateNanos']for r in rows if r['arm']=='A'])
    lines=['# Small-prime elimination: measured snapshot','',
           'This historical campaign describes an earlier implementation over primes below `2^16`. The current option covers every prime below `2^31`; see [the prime-field measured snapshot](hexgroebner-prime.md). Field coverage and controls below describe only the frozen snapshots identified here.','',
           f"The measured production snapshot is `{manifests['reviewed']['source_fingerprint']}`; the audited configuration is `{current['source_fingerprint']}` with byte-identical executables. At that snapshot, `delayedReduction` was opt-in and defaulted to false. It applied to primes `3 ≤ p < 2^16`; ordinary F₂ and wider-prime polynomial routes retained their existing arithmetic. The accumulator bound is `(p-1)+columns*(p-1)^2 < 2^50`.",'',
           'All 120 final full-system processes succeeded. All 60 off/on pairs have identical complete reduced bases, metadata and logical counters. The suite contains the first primary size from each of ten fixed families over three prime fields; it does not cover the complete fixed suite or held-out acceptance. Both arms use the same frozen executable, one leased CPU, grevlex order, degree scheduling, batch size 1024, binary pivots enabled and dense pivots disabled. Adjacent arms alternate AB/BA. Every completed sample, failure and outlier is retained.','',
           '| Field | Candidate B/A geometric mean | Process B/A geometric mean | Pair candidate ratio range | Peak RSS A/B, KiB |','|---|---:|---:|---:|---:|']
    records=cap.json('measurements/reviewed-system/metadata.json')['samples']
    for p in [2,32003,2147483647]:
        rows=[r for r in final if r['p']==p];require(len(rows)==20,'field coverage differs')
        rss={arm:max(r['peak_rss_kib']for r in records if r['p']==p and r['arm']==arm)
             for arm in ['A','B']}
        lines.append(f"| {p} | {gm([r['candidate']for r in rows]):.4f} | {gm([r['process']for r in rows]):.4f} | {min(r['candidate']for r in rows):.4f}–{max(r['candidate']for r in rows):.4f} | {rss['A']}/{rss['B']} |")
    focused=[r for r in final if r['case']=='KLYZ12-15']
    lines+=['',f"For the in-sample KLYZ-12 motivating case over 32003, candidate B/A is {gm([r['candidate']for r in focused]):.4f}. A separately instrumented full producer accepted all 61 matrices and discarded zero charged native work; its complete output and counters equal the production run. Its two candidate pair ratios span {min(r['candidate']for r in focused):.4f}–{max(r['candidate']for r in focused):.4f}. Raw samples retain per-input variability and RSS; the field table's ratio range also includes differences between families. The parent limits are the fixed corpus protocol's explicit large allowances, with 300-second, 8-GiB address-space and 256-MiB per-file external caps. These measurements do not establish behavior under the library's default work/memory allowances.",'',
            '| Kernel coefficient route | Columns | B/A geometric mean |','|---|---:|---:|']
    for shape,n,ratio in matrix:lines.append(f'| {shape} | {n} | {ratio:.4f} |')
    lines+=['','Kernel inputs use distinct known heads, dense tails and eight shared targets. Preparation is outside timing; validation, elimination and complete output/counter hashing are inside. Byte uses 251, Short uses 32003 and Word is the unchanged M31 control. The final 42-process lean-bench campaign has no point below the signal floor. The recorded host is AMD EPYC 9455; the production native compiler is Clang 21.1.8, the Lean SDK compiler is Clang 23.1.0, and Lean is 4.35.0-rc3. Native dispatch uses guarded AVX2 with scalar fallback; experimental AVX-512 dispatch is disabled. Compiler hashes, flags, exact selected CPU and environment remain in the manifests. Six trial-major quadratic sweeps use three trials and three sizes. Matched observations alternate AB/BA. The earlier short-budget campaign was inconclusive because matched points fell below the signal floor; its sole unchanged repeat used a four-second batch target and twenty-second allowance. Both are retained separately from the final production campaign.','',
            f"Experimental captured-matrix replay rejected a scalar UInt64 design (B/A {replay_ratios['v1']:.4f}); the AVX2 prototype gave {replay_ratios['v2']:.4f}. Each has four initial AB/BA observations with complete row/label/counter comparison outside the C monotonic timing interval. These experimental binaries are distinct from the production implementation. The retained input is frame 33, selected for maximum work among progressive entry-maximum dumps; the absolute maximum-work frame was not dumped.",'',
            'Local verification covers twelve strict Clang/GCC ASan/UBSan variants, scalar/SIMD fallbacks, exact packet guard pages, near-UInt64-limit residues, work/byte boundary cuts, newly admitted reducer/target counts, direct scalar Lean comparisons, producer parity, independent oracles and all nine project gates. A freestanding 32-bit x86 packet compilation checks the portable intrinsic choice. Native calls remain bounded but cancellation occurs between calls; a late work or byte decline may repeat a bounded prefix.','',
            'All timing results concern unchecked candidate production or matrix elimination. Certificate generation, independent native certification, kernel checking and complete checked calls are not included. Giac process diagnostics in the archive retain installed version 2.0.0-19, explicit monic conversion and full output comparisons; CLI startup affects tiny cases, its internal time() clock is not asserted to be wall time, and no current-fastest claim follows. No CI timing is used. The fastest-open-source milestone and overall-fastest gap remain open.','',
            f"Raw production evidence: `{path.name}` (SHA-256 `{cap.sha256}`). Experimental replay: `{replay_path.name}` (SHA-256 `{replay.sha256}`). Every payload is checked against its archive SHA-256 manifest; the report also replays source blobs, complete outputs, counters and measurement coverage.",'']
    lines.insert(-1,f"The configuration audit `{audit_path.name}` (SHA-256 `{audit.sha256}`) adds only the whole-matrix SIMD header dependency. All three fresh executable hashes and compiler/ISA controls are identical, verification sources are unchanged, and the five project linters passed again. The nine-gate results retain their measured source identity.")
    return '\n'.join(lines),current


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--replay',type=Path,required=True);p.add_argument('--report',type=Path,required=True)
    p.add_argument('--audit',type=Path,required=True)
    p.add_argument('--check',action='store_true');p.add_argument('--current',action='store_true');args=p.parse_args()
    text,manifest=render(args.archive,args.replay,args.audit)
    if args.current:
        from scripts.bench.groebner_measure import FAMILY
        from scripts.bench.sweep_freshness import index_listing
        require(index_listing(FAMILY)==manifest['source_manifest'],'current runtime differs')
    if args.check:require(args.report.read_text()==text,'report differs from archived evidence')
    else:args.report.write_text(text)
    print('PASS delayed evidence replay')

if __name__=='__main__':main()
