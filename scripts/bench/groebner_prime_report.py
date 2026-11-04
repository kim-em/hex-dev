"""Replay prime-square F4 measurements, complete outputs and native contracts."""
from __future__ import annotations
import argparse
import hashlib
import io
import json
import lzma
from pathlib import Path
import struct
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_delayed_report import gm,kernels,require,systems


def blobs(cap,prefix,listing):
    for line in listing.splitlines():
        geometry,name=line.split('\t',1);mode,digest,index=geometry.split()
        require(mode in ['100644','100755']and index=='0','unsupported source entry')
        data=cap.read(prefix+'/'+name)
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==digest,
                'source blob differs: '+name)


def sources(cap,stage):
    manifest=cap.json(stage+'/freeze/manifest.json');listing=manifest['source_manifest']
    require(hashlib.sha256(listing.encode()).hexdigest().startswith(manifest['source_fingerprint']),
            'runtime fingerprint differs')
    blobs(cap,stage+'/sources',listing)
    checks=cap.text(stage+'/checks/source-manifest.txt');blobs(cap,stage+'/check-sources',checks)
    status=cap.json(stage+'/checks/native-status.json')
    require(len(status)==2 and {r['name']for r in status}=={'clang','gcc'},'missing compiler profiles')
    for row in status:
        require(row['exit_code']==0 and row['source_fingerprint']==manifest['source_fingerprint'],
                'native check runtime or result differs')
        require(hashlib.sha256(checks.encode()).hexdigest().startswith(row['checks_fingerprint']),
                'verification fingerprint differs')
        require(len(row['variants'])==6 and row['sanitize']==['address','undefined'],
                'native variants or sanitizer controls differ')
    return manifest


def mixed(cap,manifest,final_outputs):
    seen=set();cases={};manifests=[]
    for fragment in ['mixed-focused','mixed-rest']:
        prefix='measurements/'+fragment;meta=cap.json(prefix+'/metadata.json')
        require(meta['source_bindings']==meta['source_bindings_after'],'fragment sources changed')
        manifests.append(meta['manifest'])
        for case in meta['cases']:
            require(case['name']not in cases,'duplicate fragment case');cases[case['name']]=case
        for row in meta['samples']:
            key=row['case'],row['block'],row['arm'];require(key not in seen,'duplicate fragment position')
            seen.add(key)
            require(row['status']=='ok'and row['returncode']==0 and
                    row['complete_output_and_counters_equal'],'fragment failed or differed')
            value=cap.json(prefix+'/'+row['case']+f"-b{row['block']}-{row['arm']}.stdout")
            require({k:v for k,v in value.items()if k not in ['candidateNanos','delayedReduction']}==
                    final_outputs[key],'fragment complete output differs')
    require(manifests[0]==manifests[1]and manifests[0]['binary_sha256']==manifest['binary_sha256'],
            'fragment executable identities differ')
    require(len(cases)==30 and len(seen)==120 and all((name,b,a)in seen for name in cases
            for b in [0,1]for a in ['A','B']),'incomplete joined schedule')


def replay(cap):
    manifest=cap.json('sources/manifest.json')
    for name,digest in manifest['source_sha256'].items():
        require(hashlib.sha256(cap.read('sources/'+name)).hexdigest()==digest,'replay source differs')
    meta=cap.json('measurements/metadata.json');samples=cap.json('measurements/samples.json')
    require(meta['binary_sha256']==manifest['binary_sha256']and meta['samples']==samples,
            'replay measurement identity differs')
    require([r['arm']for r in samples]==['A','B','B','A']and len(samples)==4,
            'replay AB/BA schedule differs')
    selected=cap.json('inputs/selected.json');frames=[json.loads(line)
        for line in cap.text('capture/shapes.jsonl').splitlines()]
    require(len(frames)==61 and selected['id']==max((r for r in frames if r['dump']),
            key=lambda r:r['work'])['id'],'captured-matrix selection differs')
    scope=cap.json('scope.json');digest=hashlib.sha256();size=0;prefix=b''
    with lzma.LZMAFile(io.BytesIO(cap.read('inputs/frame-000033.bin.xz')))as stream:
        while data:=stream.read(1024**2):
            digest.update(data);size+=len(data)
            if not prefix:prefix=data[:64]
    require(size==scope['input_bytes']and digest.hexdigest()==scope['input_sha256']==
            meta['input_sha256'],'retained matrix input differs')
    p,c,nr,nt,ns,independent,entries=struct.unpack('<7Q',prefix[8:64])
    require(prefix[:8]==b'HXF4MAT1'and(p,c,nr,nt,independent,entries)==(
        selected['p'],selected['columns'],selected['reducers'],selected['targets'],
        selected['independent'],selected['entries'])and ns in [0,nr+nt],
        'captured matrix header differs')
    for row in samples:
        require(row['exit_code']==0 and row['result']['completeOutputAndCountersEqual']and
                row['result']['work']==selected['work'],'replay failed or differs')
    for path,count in [('checks/random/status.json',100),('checks/small/status.json',10)]:
        rows=cap.json(path)
        require(len(rows)==count and all(r['exit']==0 and r['result']['completeOutputAndCountersEqual']
                                        for r in rows),'replay coefficient/boundary tests failed')
    return gm([r['result']['candidateNanos']for r in samples if r['arm']=='B'])/gm(
        [r['result']['candidateNanos']for r in samples if r['arm']=='A'])


def inconclusive(cap,prefix,manifest,count):
    meta=cap.json(prefix+'/metadata.json')
    require(meta['manifest']['binary_sha256']['bench']==manifest['binary_sha256']['bench']and
            meta['source_bindings']==meta['source_bindings_after'],'inconclusive kernel identity changed')
    require(len(meta['samples'])==count,'inconclusive completed process count differs')
    low=0
    for row in meta['samples']:
        require(row['exit_code']in [0,2],'inconclusive kernel process failed')
        item=cap.json(prefix+'/'+row['label']+'/result.json')['results'][0]
        for point in item['points']:
            require(point['status']=='ok','inconclusive kernel computation failed')
            low+=int(point['below_signal_floor'])
    require(low==1,'inconclusive signal-floor observation differs')


def render(path,replay_path):
    cap=Capsule(path);experimental=Capsule(replay_path)
    manifests={stage:sources(cap,stage)for stage in ['mixed','split','final']}
    final,outputs=systems(cap,'measurements/final-system',manifests['final'])
    repeated='measurements/final-system-repeat/metadata.json' in cap.payloads
    if repeated:
        more,more_outputs=systems(cap,'measurements/final-system-repeat',manifests['final'])
        require(more_outputs==outputs,'complete outputs differ between fixed repeat sweeps')
        final+=more
    count_per_field=40 if repeated else 20
    kernel_sizes=tuple(cap.json('scope.json')['kernel_sizes']) if 'scope.json' in cap.payloads else (128,256,512)
    if kernel_sizes==(1024,2048,4096):
        inconclusive(cap,'measurements/small-kernels-inconclusive',manifests['final'],11)
        inconclusive(cap,'measurements/small-kernels-repeat-inconclusive',manifests['final'],17)
        require(cap.text('large-input-check/large-kernel-check-run.log').splitlines()==[
            f'PASS {n}: all three widths successful; complete rows and counters equal'
            for n in kernel_sizes],'large-input functional validation differs')
    require(kernel_sizes in [(128,256,512),(1024,2048,4096)],'unexpected kernel suite')
    earlier,earlier_outputs=systems(cap,'measurements/split-system',manifests['split'])
    require(earlier_outputs==outputs,'logical outputs differ between candidate stages')
    mixed(cap,manifests['mixed'],outputs)
    kernels(cap,'measurements/split-kernels',manifests['split'],True)
    matrix=kernels(cap,'measurements/final-kernels',manifests['final'],True,kernel_sizes)
    complexity=[]
    for shape in ['Byte','Short','Word']:
        for arm in ['A','B']:
            result=cap.json(f'measurements/final-kernels/complexity/{shape}/{arm}/result.json')['results'][0]
            require(result['verdict']in ['consistent_with_declared_complexity','inconclusive'],
                    'unexpected final kernel complexity verdict')
            complexity.append(result['verdict'])
    consistent=complexity.count('consistent_with_declared_complexity')
    inconclusive_count=complexity.count('inconclusive')
    complete_gates='final/full/status.json' in cap.payloads
    full=cap.json('final/full/status.json' if complete_gates else 'final/build/status.json')
    expected_gates=['build','oracles','driver','bench','dag','phase4','manifest','headers','lines'] if complete_gates else ['build']
    require([r['name']for r in full]==expected_gates and all(r['exit_code']==0 and
            r['source_fingerprint']==manifests['final']['source_fingerprint']for r in full),
            'project gates incomplete, failed or used different runtime')
    native=cap.json('measurements/refusals/metadata.json')
    require(native['source_bindings']==native['source_bindings_after']and
            native['exit_code']==0 and native['complete_output_and_counters_equal'],
            'instrumented native producer differs')
    counters={k:int(v)for k,v in native['native'].items()}
    require(counters['bulkAccepted']==61 and counters['bulkDeclined']==0 and
            counters['delayedRefusedWork']==0,'motivating-case frame coverage or wasted work differs')
    prototype=replay(experimental);manifest=manifests['final']
    rows=cap.json('measurements/final-system/metadata.json')['samples']
    if repeated:rows+=cap.json('measurements/final-system-repeat/metadata.json')['samples']
    process_count=len(rows);pair_count=len(final)
    lines=['# Exact delayed elimination over prime fields','',
        f"The measured runtime source is `{manifest['source_fingerprint']}`. Opt-in `delayedReduction` covers every prime `3 ≤ p < 2^31`; it defaults to false. Small fields retain the UInt64 accumulator bound below `2^50`. Four-byte coefficients use residues modulo `p²`: a cell and product are each below `p²`, their sum is below `2p² < 2^63`, and one exact correction restores the bound while preserving the residue modulo `p`.",'',
        f'All {process_count} final full-system processes succeeded, and all {pair_count} adjacent off/on pairs have identical complete reduced bases, metadata and logical counters. The fixed selection is the first primary size in ten families over F₂, 32003 and M31, with grevlex order and degree scheduling. Both arms use one frozen executable, one automatically leased CPU, batch size 1024, binary pivots enabled and dense pivots disabled. Arm order alternates AB/BA. These first-size observations do not cover the complete fixed balanced suite or held-out acceptance.','',
        '| Field | Candidate B/A geometric mean | Observed process B/A | Candidate pair range | Peak RSS A/B, KiB |',
        '|---|---:|---:|---:|---:|']
    for p in [2,32003,2147483647]:
        values=[r for r in final if r['p']==p];require(len(values)==count_per_field,'field coverage differs')
        rss={a:max(r['peak_rss_kib']for r in rows if r['p']==p and r['arm']==a)for a in ['A','B']}
        field_label='2 (unchanged-path control)'if p==2 else str(p)
        lines.append(f"| {field_label} | {gm([r['candidate']for r in values]):.4f} | {gm([r['process']for r in values]):.4f} | {min(r['candidate']for r in values):.4f}–{max(r['candidate']for r in values):.4f} | {rss['A']}/{rss['B']} |")
    lines+=['','F₂ is a null control: both arms use the same executable and arithmetic route. Its observed spread measures variability in this campaign, not an algorithmic gain or a calibrated confidence interval. Candidate production and process time are separate observations. Their aggregate ratios are descriptive point estimates: gains comparable to the unchanged-control fluctuation cannot be attributed to this option. No control-adjusted speedup or aggregate causal improvement is claimed. All completed samples and tiny-case outliers remain included; the pair range also includes differences between families. External limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with the fixed corpus protocol’s recorded large parent work/memory allowances. The data do not establish admission or timing under library default budgets.','',
        '| In-sample KLYZ-12 field | Candidate B/A | Pair ratios |','|---|---:|---:|']
    for p in [32003,2147483647]:
        values=[r for r in final if r['family']=='sparse-structured'and r['p']==p]
        field_label='2 (unchanged-path control)'if p==2 else str(p)
        lines.append(f"| {field_label} | {gm([r['candidate']for r in values]):.4f} | "+', '.join(f"{r['candidate']:.4f}"for r in values)+' |')
    lines+=['','| Field excluding in-sample KLYZ | Candidate B/A geometric mean |','|---|---:|']
    for p in [32003,2147483647]:
        values=[r for r in final if r['p']==p and r['family']!='sparse-structured']
        require(len(values)==count_per_field*9//10,'excluding-KLYZ coverage differs')
        lines.append(f"| {p} | {gm([r['candidate']for r in values]):.4f} |")
    lines+=['','Excluding KLYZ leaves nine equally weighted first-size families. Both full and excluding-KLYZ summaries retain every pair; this sensitivity comparison does not replace the fixed balanced suite.','','The independent instrumented M31 producer accepted all 61 matrices, declined none and discarded zero charged native work; its complete output and counters equal production. This is evidence for that motivating system, not a guarantee against late refusals on other inputs. Work and private-payload caps can still trigger bounded refusal and continuation. Cancellation is observed between native calls.','',
        '| Kernel field | Columns | B/A geometric mean |','|---|---:|---:|']
    for shape,n,ratio in matrix:lines.append(f"| {dict(Byte=251,Short=32003,Word=2147483647)[shape]} | {n} | {ratio:.4f} |")
    lines+=['',f'The 42 final lean-bench processes retain all samples and have no point below the signal floor. Kernel sizes are {kernel_sizes[0]}–{kernel_sizes[-1]} columns, below the 131072-column admission ceiling. A quadratic verdict on three sizes is a limited consistency observation, not a proof or evidence of scaling to that ceiling. The reported per-size ratios show whether gains narrow as size increases. The six three-trial, three-size sweeps give {consistent} verdicts consistent with quadratic work and {inconclusive_count} inconclusive verdicts. Both outcomes are retained; no proof of asymptotic behavior follows from this grid. Matched runs alternate AB/BA. Inputs have distinct known heads, dense tails and eight shared targets. Preparation is outside timing; validation, elimination and hashing complete row contents, labels and all eight counters are inside. Every matched digest agrees.','',
        'The host is AMD EPYC 9455. Production native code uses Clang 21.1.8; Lean SDK compilation uses Clang 23.1.0 and Lean 4.35.0-rc3. Guarded AVX2 and scalar fallbacks are enabled; experimental AVX-512 is disabled. Executable/compiler hashes, build flags, selected CPUs and host activity are retained in the manifests. Timing evidence comes from manual shared-host runs, never CI.','',
        f"The earlier isolated prime-square prototype replay has B/A {prototype:.4f} on four initial AB/BA provider observations. Its complete independent matrix comparison is outside the C monotonic timing interval. The retained frame is the highest-work input among progressive entry-maximum dumps, not the absolute maximum-work frame. The prototype executable and production runtime have distinct source and binary identities.",'',
        'The archive also retains the unselected mixed-width and first split-width campaigns, including every outlier, plus a strict non-overlapping join of the initial four focused and 116 remaining processes. Their complete logical outputs agree with the final implementation under their recorded controls. They do not establish the combined dense-pivot option contract: the final implementation adds the missing 65536-column preparation guard and regression tests. A failed GCC test-counter macro build is retained; the final statement macro passes strict warnings on both compilers.','',
        'Final local verification includes twelve Clang/GCC ASan/UBSan variants; exact guard-page loads and per-width four-lane coverage; near-UInt64 and prime-square residue boundaries; direct scalar Lean comparisons; newly admitted reducer/target counts; exact work/byte refusal boundaries; combined M31 dense/delayed flags below and above 65536 columns; independent portable-reference comparisons; and the recorded library/theory build. Full oracle and project-gate receipts are reported below only when present in this capsule. Runtime/check-source identities are preserved separately, including the test-only counter fix.','',
        'These observations measure unchecked candidate production or matrix elimination. Certificate generation, independent native certification, kernel checking and complete checked calls remain separate costs. The fastest-open-source milestone, solved-coverage acceptance, full balanced and held-out comparisons, parallel comparator sweeps and the overall-fastest gap remain open.','',
        f"Production evidence: `{path.name}` (SHA-256 `{cap.sha256}`). Isolated replay evidence: `{replay_path.name}` (SHA-256 `{experimental.sha256}`). Payload manifests, source blobs, complete outputs, counters, controls, unique schedule positions and coverage are replayed by this report generator.",'']
    gate_text='All nine recorded project gates passed, including independent oracles and downstream kernel replay.' if complete_gates else 'The measurement capsule records the core build and twelve native profiles. Full oracle and project-gate receipts are pending; no completion claim is made for those gates here.'
    lines.insert(-1,gate_text)
    if repeated:
        lines.insert(-1,'The first 120-process system sweep was inconclusive because the unchanged-path control varied. Its sole unchanged repeat is combined with it here: all 240 samples contribute, with no filtering and no further unchanged system reruns.')
    if kernel_sizes==(1024,2048,4096):
        lines.insert(-1,'Two earlier current-source small-kernel campaigns are retained as inconclusive: 11 and 17 completed processes, each stopping at a point below the signal floor. No third small-input rerun was taken. The 1024–4096 suite uses different inputs fixed and fully validated before timing. At these larger shapes the ordinary arm can use bounded continuation while the delayed arm admits a whole frame; this comparison measures admission, dispatch, elimination and complete output hashing together.')
    return '\n'.join(lines),manifest


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['archive','replay','report']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--check',action='store_true');parser.add_argument('--current',action='store_true')
    args=parser.parse_args();text,manifest=render(args.archive,args.replay)
    if args.current:
        from scripts.bench.groebner_measure import FAMILY
        from scripts.bench.sweep_freshness import index_listing
        require(index_listing(FAMILY)==manifest['source_manifest'],'current runtime differs')
    if args.check:require(args.report.read_text()==text,'report differs from archived evidence')
    else:args.report.write_text(text)
    print('PASS prime-square evidence replay')

if __name__=='__main__':main()
