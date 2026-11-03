#!/usr/bin/env python3
"""Verify and report dense-pivot development observations without filtering."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import source, require, mean


def sweep(capsule, label, manifests):
    metadata = capsule.json(label+'/metadata.json')
    recorded = capsule.json(label+'/analysis.json')
    require(metadata['source_unchanged'] and metadata['threads'] == 1, 'source/thread mismatch')
    require(metadata['binary_sha256'] == metadata['binary_sha256_after'], 'binary changed')
    a = manifests[metadata['baseline_source_fingerprint']]
    b = manifests[metadata['source_fingerprint']]
    require(metadata['baseline_manifest'] == a and metadata['source_manifest'] == b['source_manifest'], 'source binding mismatch')
    require(metadata['binary_sha256'] == {'A':a['binary_sha256']['compute'],'B':b['binary_sha256']['compute']}, 'ELF binding mismatch')
    require(metadata['requested_scheduling'] == {'A':'degree','B':'degree'}, 'scheduling mismatch')
    campaign=label.rsplit('/',1)[-1]
    expected={'enabled':{'A':'false','B':'true'},'control':{'A':None,'B':'false'},'combined':{'A':None,'B':'true'}}[campaign]
    require(metadata['requested_dense_pivots']==expected, 'dense controls differ')
    for sample in metadata['samples']:
        command=sample['command'];arm=sample['arm'];value=expected[arm]
        require(command.count('--dense-pivots')==(0 if value is None else 1), 'dense command admission differs')
        if value is not None:require(command[command.index('--dense-pivots')+1]==value, 'dense command value differs')
    for name,digest in metadata['input_sha256'].items():
        require(hashlib.sha256(capsule.read(label+'/inputs/'+name)).hexdigest() == digest, 'input digest mismatch')
    samples=metadata['samples']
    indexed={(v['case'],v['block'],v['arm']):v for v in samples}
    order=[v['case']for v in samples if v['block']==0 and v['arm']=='A']
    require(len(samples)==len(indexed)==56 and len(set(order))==14, 'incomplete sweep')
    require([(v['case'],v['block'],v['arm'])for v in samples] ==
            [(case,block,arm)for block in [0,1]for case in order for arm in (['A','B']if block==0 else['B','A'])], 'recorded AB/BA order differs')
    families={};candidate=[];work=[];allocations=[];fields={};process=[]
    for case in order:
        for block in [0,1]:
            a,b=[indexed[case,block,arm]for arm in ['A','B']]
            outputs=[]
            for arm,sample in [('A',a),('B',b)]:
                require(sample['status']=='ok'and sample['returncode']==0 and sample['complete_basis_equal'], 'failed sample')
                output=capsule.json(f'{label}/{case}-b{block}-{arm}.stdout')
                require(output['kind']=='unchecked_candidate'and output['order']=='grevlex'and output['scheduling']=='degree'and output['p']==sample['p'], 'candidate contract differs')
                stats=dict(sample['statistics']);require(stats.pop('candidate_nanos')==output['candidateNanos']and stats==output['statistics'], 'output counters differ')
                require(int(capsule.text(f'{label}/{case}-b{block}-{arm}.rss'))==sample['peak_rss_kib'], 'RSS differs')
                outputs.append(output)
            candidate.append(outputs[1]['candidateNanos']/outputs[0]['candidateNanos'])
            process.append(b['wall_nanos']/a['wall_nanos'])
            field=fields.setdefault(a['p'],{'process':[],'candidate':[]})
            field['process'].append(process[-1]);field['candidate'].append(candidate[-1])
            work.append(outputs[1]['statistics']['work']/outputs[0]['statistics']['work'])
            allocations.append(outputs[1]['statistics']['allocatedBytes']-outputs[0]['statistics']['allocatedBytes'])
            for output in outputs:
                output.pop('candidateNanos');output['statistics'].pop('work');output['statistics'].pop('allocatedBytes')
            require(outputs[0]==outputs[1], 'complete basis or non-work metadata differs')
            families.setdefault(a['family'],[]).append(b['wall_nanos']/a['wall_nanos'])
    require(len(families)==7 and all(len(v)==4 for v in families.values()), 'unbalanced suite')
    balanced=mean([mean(v)for v in families.values()])
    require(math.isclose(balanced,recorded['family_balanced_geomean'],rel_tol=1e-12), 'process ratio differs')
    require(recorded['samples']==56 and recorded['complete_bases_equal']==28 and recorded['failed_processes']==recorded['timeouts']==0, 'coverage differs')
    require(all(math.isclose(mean(v),recorded['per_family'][k],rel_tol=1e-12)for k,v in families.items()), 'family ratios differ')
    return metadata,recorded,mean(candidate),mean(work),min(allocations),max(allocations),dict(process=process,candidate=candidate,fields=fields)


def kernels(capsule, root, shapes):
    metadata=capsule.json(root+'/kernel-status.json');samples=metadata['samples']
    require(metadata['binary_sha256']==metadata['binary_sha256_after']==metadata['manifest']['binary_sha256']['bench'], 'kernel binary changed')
    require(all(a['finished_ns']<=b['started_ns']for a,b in zip(samples,samples[1:])), 'kernel timestamps overlap')
    names=['complexity/'+arm for arm in ['dense','sparse','portable']]if shapes==['single']else [f'complexity/{shape}/{arm}'for shape in shapes for arm in ['dense','sparse']]
    names += [(f'matched/b{block}-{n}-{arm}'if shape=='single'else f'matched/{shape}/b{block}-{n}-{arm}')for block in [0,1]for shape in shapes for n in [128,256,512,1024,2048,4096]for arm in (['sparse','dense']if block==0 else['dense','sparse'])]
    require([v['label']for v in samples]==names and all(v['exit_code']in [0,2]for v in samples), 'kernel schedule/exit differs')
    for sample in samples:
        if not sample['label'].startswith('complexity/'):continue
        record=capsule.json(root+'/kernels/'+sample['label']+'/result.json')['results'][0]
        require([(v['trial_index'],v['param'])for v in record['points']]==[(t,n)for t in range(3)for n in [128,256,512,1024,2048,4096]], 'complexity ladder differs')
        require(all(v['status']=='ok' for v in record['points']), 'failed complexity sample')
        for point in record['points']:
            require(math.isclose(point['per_call_nanos'],point['total_nanos']/point['inner_repeats'],rel_tol=1e-8), 'complexity normalization differs')
    result={}
    for shape in shapes:
        ratios=[];flags=0;rows=[]
        for n in [128,256,512,1024,2048,4096]:
            pair=[]
            for block in [0,1]:
                prefix=f'{root}/kernels/matched/' + (''if shape=='single'else shape+'/')
                functions={'single':{'dense':'densePivot','sparse':'sparsePivot'},'half':{'dense':'denseBatch','sparse':'sparseBatch'},'three-quarters':{'dense':'denseThreeQuarters','sparse':'sparseThreeQuarters'},'full':{'dense':'denseFull','sparse':'sparseFull'},'selected':{'dense':'denseSelected','sparse':'sparseSelected'}}
                records=[capsule.json(prefix+f'b{block}-{n}-{arm}/result.json')['results'][0]for arm in ['sparse','dense']]
                require(all(record['function']=='Hex.Groebner.Bench.'+functions[shape][arm] for record,arm in zip(records,['sparse','dense'])), 'kernel function differs')
                a,b=[record['points'][0]for record in records]
                require(a['status']==b['status']=='ok'and a['result_hash']==b['result_hash']and a['param']==b['param']==n, 'kernel output differs')
                for v in [a,b]:require(math.isclose(v['per_call_nanos'],v['total_nanos']/v['inner_repeats'],rel_tol=1e-8), 'kernel normalization differs')
                pair.append(b['per_call_nanos']/a['per_call_nanos']);flags+=a['below_signal_floor']+b['below_signal_floor']
            ratios.extend(pair);rows.append((n,mean(pair)))
        result[shape]=(mean(ratios),flags,rows)
    return samples,result


def shape_cache(capsule):
    ratios={}
    for kind in ['deterministic','sampled']:
        label='scan-shapes/'+kind
        metadata=capsule.json(label+'/metadata.json')
        samples=metadata['samples'];require(len(samples)==56, 'shape-cache coverage differs')
        values=[]
        index={(v['case'],v['block'],v['arm']):v for v in samples}
        require(len(index)==56 and all(v['status']=='ok'and v['returncode']==0 and v['complete_basis_equal']for v in samples), 'shape-cache failure')
        for case,block,arm in index:
            if arm!='A':continue
            outputs=[capsule.json(f'{label}/{case}-b{block}-{v}.stdout')for v in ['A','B']]
            for output in outputs:output.pop('candidateNanos')
            require(outputs[0]==outputs[1], 'shape-cache complete output differs')
            values.append(index[case,block,'B']['wall_nanos']/index[case,block,'A']['wall_nanos'])
        ratios[kind]=mean(values)
    return ratios


def usage_counts(science, guards, metadata, label="dense-review", preserve_frames=False):
    cases=sorted({sample['case']for sample in metadata['samples']})
    results=[]
    for case in cases:
        input_name=case+'.json'
        require(hashlib.sha256(guards.read('usage-inputs/'+input_name)).hexdigest()==metadata['input_sha256'][input_name],'usage input differs')
        modes=[]
        for enabled,arm in [('false','A'),('true','B')]:
            by_compiler=[]
            for compiler in ['clang','gcc']:
                prefix=f'probes/{compiler}/usage-results/{case}-{enabled}'
                command=guards.json(prefix+'.command.json')
                require(command[command.index('--dense-pivots')+1]==enabled and
                        command[command.index('--scheduling')+1]=='degree' and
                        Path(command[-1]).name==input_name,'usage controls differ')
                counts=guards.json(prefix+'.stderr')
                require(set(counts)=={'prepares','admitted','scans','updates','bulkAccepted','bulkDeclined'}and
                        all(isinstance(v,str)and v.isdecimal()and int(v)<2**64 for v in counts.values()),'invalid usage counters')
                counts={k:int(v)for k,v in counts.items()}
                output=guards.json(prefix+'.stdout')
                expected=science.json(f'{label}/enabled/{case}-b0-{arm}.stdout')
                output.pop('candidateNanos');expected.pop('candidateNanos')
                require(output==expected,'untimed usage output differs from timed candidate')
                if enabled=='false' or output['p']==32003:
                    require(counts['prepares']==counts['admitted']==counts['scans']==counts['updates']==0,'inert path used dense operations')
                require(counts['admitted']<=counts['prepares'],'admission count exceeds calls')
                by_compiler.append(counts)
            require(by_compiler[0]==by_compiler[1],'compiler usage differs')
            modes.append(by_compiler[0])
        if preserve_frames:
            require(all(modes[0][k]==modes[1][k]for k in ['bulkAccepted','bulkDeclined']),'dense option changed observed frame eligibility')
        results.append((case,*modes))
    require(len(results)==14,'usage coverage differs')
    return results


def continuation(capsule, manifests):
    root='dense-bulk/continuation';metadata=capsule.json(root+'/metadata.json')
    require(metadata['threads']==1 and metadata['field']==65537 and metadata['dense_pivots'] is False,'continuation controls differ')
    require(metadata['binary_sha256']==metadata['binary_sha256_after'],'continuation binary changed')
    for arm,manifest in metadata['manifest'].items():
        require(manifest==manifests[manifest['source_fingerprint']] and
                metadata['binary_sha256'][arm]==manifest['binary_sha256']['bench'],'continuation source binding differs')
    samples=metadata['samples'];functions=['matrixFrame','matrixSparse'];sizes=[64,128,256,512,1024]
    expected=[f'b{b}-{f}-{n}-{arm}'for b in [0,1]for f in functions for n in sizes for arm in (['A','B']if b==0 else['B','A'])]
    require([v['label']for v in samples]==expected and all(v['exit_code']in [0,2]for v in samples),'continuation schedule/exit differs')
    require(all(a['finished_ns']<=b['started_ns']for a,b in zip(samples,samples[1:])),'continuation timestamps overlap')
    result={}
    for function in functions:
        ratios=[];flags=0;rows=[]
        for n in sizes:
            values=[]
            for block in [0,1]:
                records=[capsule.json(f'{root}/b{block}-{function}-{n}-{arm}/result.json')['results'][0]for arm in ['A','B']]
                require(all(v['function']=='Hex.Groebner.Bench.'+function for v in records),'continuation function differs')
                a,b=[v['points'][0]for v in records]
                require(a['status']==b['status']=='ok'and a['param']==b['param']==n and a['result_hash']==b['result_hash'],'continuation output differs')
                for v in [a,b]:require(math.isclose(v['per_call_nanos'],v['total_nanos']/v['inner_repeats'],rel_tol=1e-8),'continuation normalization differs')
                values.append(b['per_call_nanos']/a['per_call_nanos']);flags+=a['below_signal_floor']+b['below_signal_floor']
            rows.append((n,mean(values)));ratios.extend(values)
        result[function]=(mean(ratios),min(ratios),max(ratios),flags,rows)
    return result

def verify_guards(guards, current, expanded=False, bulk=False):
    runtime,checks=guards.text('runtime.manifest'),guards.text('checks.manifest')
    require(runtime==current['source_manifest'],'verification runtime differs')
    for listing,prefix in [(runtime,'runtime-sources/'),(checks,'checks-sources/')]:
        for line in listing.splitlines():
            _,oid,rest=line.split(' ',2);_,path=rest.split('\t');blob=guards.read(prefix+path)
            require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()==oid,'verification blob mismatch')
    runtime_sha,checks_sha=[hashlib.sha256(v.encode()).hexdigest()for v in [runtime,checks]]
    native,full=guards.json('native-status.json'),guards.json('full-status.json')
    require(len(native)==2 and {v['name']for v in native}=={'clang','gcc'} and all(v['variants']==['Native','Scalar','Remainder','ScalarRemainder']for v in native),'native coverage differs')
    require(len(full)==9 and {v['name']for v in full}=={'build','oracles','driver','bench','dag','phase4','manifest','headers','lines'},'project coverage differs')
    require(all(v['exit_code']==0 and v['source_manifest_sha256']==runtime_sha and v['checks_manifest_sha256']==checks_sha for v in native+full),'verification result/identity differs')
    for compiler in ['clang','gcc']:
        log=guards.text(compiler+'.log').splitlines()
        require(log.count('dense full-F4 updates: 1')==4,'instrumented full-F4 cache updates missing')
        if expanded:
            require(log.count('shared dense checkpoints: 4 IO byte comparisons')==4 and
                    log.count('small M31 cached-option bulk frame: accepted')==4,'expanded runtime checks missing')
    if bulk:
        for compiler in ['clang','gcc']:
            require(guards.text(compiler+'.log').splitlines().count('public M31 cached-option bulk frames: 12 accepted; exact boundary counters and work cap passed')==4,'bulk-frame boundary coverage missing')
    return runtime_sha,checks_sha

def executable_text(blob, lean):
    """Remove comments while preserving quoted C/Lean strings and all code."""
    data=blob.decode();out=[];i=0
    opening,closing=('/-','-/')if lean else('/*','*/')
    while i<len(data):
        if data[i]=='"'or(not lean and data[i]=="'"):
            quote=data[i];start=i;i+=1
            while i<len(data)and data[i]!=quote:
                i+=2 if data[i]=='\\'else 1
            require(i<len(data),'unterminated quoted source');i+=1;out.append(data[start:i])
        elif data.startswith(opening,i):
            i+=2;depth=1
            while i<len(data)and depth:
                if lean and data.startswith(opening,i):depth+=1;i+=2
                elif data.startswith(closing,i):depth-=1;i+=2
                else:i+=1
            require(depth==0,'unterminated source comment');out.append(' ')
        elif data.startswith('--'if lean else'//',i):
            end=data.find('\n',i);i=len(data)if end<0 else end
        else:out.append(data[i]);i+=1
    return ''.join(out)


def documentation_only(science, guards):
    measured=science.json('dense-bulk/manifest.json')['source_manifest']
    current=guards.text('runtime.manifest')
    def paths(listing):return {line.split('\t',1)[1]for line in listing.splitlines()}
    require(paths(measured)==paths(current),'verification runtime paths differ')
    changed=set()
    for path in paths(measured):
        a=science.read('dense-bulk/root-sources/'+path);b=guards.read('runtime-sources/'+path)
        if a==b:continue
        changed.add(path)
        require(path in {'HexGroebner/EliminationKernel.lean','HexGroebner/ffi/matrix_eliminate.c'}and
                executable_text(a,path.endswith('.lean'))==executable_text(b,path.endswith('.lean')),
                'executable source changed after the timed revision')
    require(changed=={'HexGroebner/EliminationKernel.lean','HexGroebner/ffi/matrix_eliminate.c'},'documentation correction coverage differs')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['experiments','first','final','baseline','old-baseline','guards','report']:
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--reviewed',type=Path);parser.add_argument('--reviewed-guards',type=Path)
    parser.add_argument('--bulk',type=Path);parser.add_argument('--bulk-guards',type=Path)
    parser.add_argument('--verified-guards',type=Path)
    parser.add_argument('--check',action='store_true');parser.add_argument('--current',action='store_true')
    args=parser.parse_args()
    experiments,first,final,baseline,old,guards=map(Capsule,[args.experiments,args.first,args.final,args.baseline,args.old_baseline,args.guards])
    manifests={}
    for capsule,label in [(experiments,'dense-reviewed'),(experiments,'dense-density'),(experiments,'scan-shapes'),(first,'dense-state'),(final,'dense-active'),(baseline,'trie-format'),(old,'sampled-final')]:
        manifest=source(capsule,label);manifests[manifest['source_fingerprint']]=manifest
    current=final.json('dense-active/manifest.json')
    runtime_sha,checks_sha=verify_guards(guards,current)
    reviewed=None;review_guards=None
    if args.reviewed:
        require(args.reviewed_guards is not None,'reviewed verification capsule missing')
        reviewed=Capsule(args.reviewed);review_guards=Capsule(args.reviewed_guards)
        manifest=source(reviewed,'dense-review');manifests[manifest['source_fingerprint']]=manifest
        current=reviewed.json('dense-review/manifest.json')
        runtime_sha,checks_sha=verify_guards(review_guards,current,True)
    bulk=None;bulk_guards=None
    latest_science,latest_guards,latest_label=reviewed,review_guards,'dense-review'
    if args.bulk:
        require(reviewed is not None and args.bulk_guards is not None,'bulk history/verification missing')
        bulk=Capsule(args.bulk);bulk_guards=Capsule(args.bulk_guards)
        manifest=source(bulk,'dense-bulk');manifests[manifest['source_fingerprint']]=manifest
        current=bulk.json('dense-bulk/manifest.json')
        runtime_sha,checks_sha=verify_guards(bulk_guards,current,True,True)
        latest_science,latest_guards,latest_label=bulk,bulk_guards,'dense-bulk'
    verified=None
    if args.verified_guards:
        require(bulk is not None,'final verification requires measured bulk history')
        verified=Capsule(args.verified_guards)
        documentation_only(bulk,verified)
        runtime_sha,checks_sha=verify_guards(verified,{'source_manifest':verified.text('runtime.manifest')},True,True)
        latest_guards=verified
        for compiler in ['clang','gcc']:
            lines=verified.text(compiler+'.log').splitlines()
            require(lines.count('dense normalized/target frames: exact parent refusal and density boundaries passed')==4,'normalized/target native coverage missing')
            counts=[int(line.rsplit(': ',1)[1])for line in lines if line.startswith('dense full-F4 bulk declines: ')]
            require(len(counts)==4 and all(v>0 for v in counts),'complete F4 continuation coverage missing')
    if args.current:
        identity=source_identity();require(identity['source_manifest_sha256']==runtime_sha and identity['checks_manifest_sha256']==checks_sha,'current sources differ')
    campaigns=[(first,'dense-state/'+name)for name in ['enabled','control','combined']]+[(final,'dense-active/'+name)for name in ['enabled','control','combined']]
    if reviewed:campaigns += [(reviewed,'dense-review/'+name)for name in ['enabled','control','combined']]
    if bulk:
        campaigns += [(bulk,'dense-bulk/'+name)for name in ['enabled','control','combined']]
        campaigns += [(bulk,'dense-bulk/repeat/'+name)for name in ['enabled','control','combined']]
    sweeps=[sweep(capsule,label,manifests)for capsule,label in campaigns]
    single,one=kernels(experiments,'dense-reviewed',['single'])
    batch,many=kernels(experiments,'dense-density',['half','three-quarters','full'])
    selected_samples,selected=kernels(reviewed,'dense-review',['selected']) if reviewed else ([],{})
    shape_ratios=shape_cache(experiments)
    require(many['half'][1]==2 and one['single'][1]==many['three-quarters'][1]==many['full'][1]==0, 'reported signal-floor counts differ')
    text=f'''# Checked dense pivots: kernels and complete F4 observations

Dense pivot buffers preserve their exact sparse sources through typed cache
provenance. Preparation reserves its work and packed payload against the parent
allowances. Dense updates preserve zero gaps, invalid-target prefixes, pending
cursors and trace events. The deterministic continuation and whole-eliminator
proofs include preparation charges. Final runtime `{runtime_sha[:12]}` and
verification sources `{checks_sha[:12]}` pass eight Clang/GCC sanitizer variants
and nine project gates. One synthetic {238 if bulk else 174}-variable linear-ideal F4 fixture exercises exactly one native
dense update in each compiler variant. Kernel checking remains separate from native testing.

The experimental option defaults off. Only M31 matrices admit caches; narrower
fields retain their existing kernels. A proved active-cache bit preserves sparse
dispatch when no cache exists. Admission selects non-contiguous spans at least
three-quarter full, 128–4096 nonzero entries and at most 65536 columns. Fully
contiguous rows retain the existing contiguous sparse SIMD path. Certificate
production and sampled computation retain their sparse routes.

The kernel input has 128–4096 nonzero entries over M31. Each output byte is
consumed. The first experiment times one pending update, including full output
hashing. The next experiment performs 64 owned updates and consumes the full
final output once. Preparation is excluded in both. Complexity ladders use three
fixed trial-major trials. Matched comparisons use adjacent sparse/dense then
dense/sparse arms at every declared size, with increasing recorded timestamps.
All {len(single)+len(batch)} benchmark invocations and 48 matched pairs remain available.
No completed sample was rerun or filtered. Two matched half-full samples are
below the signal floor; their commands return an inconclusive status and their
observations remain in the descriptive ratios.

| Kernel | Dense/sparse ratio | Signal-floor samples in matched pairs |
| --- | ---: | ---: |
'''
    for label,(ratio,flags,_) in [('Single, half full',one['single']),('64 updates, half full',many['half']),('64 updates, three-quarter full',many['three-quarters']),('64 updates, full',many['full'])]:
        text+=f'| {label} | {ratio:.4f} | {flags} |\n'
    text+='\n| Nonzero entries | Single half | 64 half | 64 three-quarter | 64 full |\n| ---: | ---: | ---: | ---: | ---: |\n'
    for i,n in enumerate([128,256,512,1024,2048,4096]):
        values=[one['single'][2][i][1],many['half'][2][i][1],many['three-quarters'][2][i][1],many['full'][2][i][1]]
        text+=f'| {n} | '+' | '.join(f'{v:.4f}'for v in values)+' |\n'
    text+='''
The three-quarter-full kernel benefits from contiguous updates. Fully dense rows
already have a contiguous sparse path. The single-update diagnostic profiles
include four fixed AB/BA recordings with no lost samples: output hashing takes
about half the sampled cycles and row updates about 37% on that input. Profiles
explain that experiment; they are not independent timing evidence or a compiler
impossibility claim.

All complete-F4 sweeps use fourteen development inputs in seven families at
15- and 31-bit primes, grevlex, degree scheduling and one algorithm thread.
They compare complete reduced candidates outside timing with matched input,
output and resource contracts. Candidate time includes canonicalization, F4 and
interreduction; process time also includes initialization, parsing and output.
Certificate generation, independent final verification and kernel checking are
excluded. These inputs are not held out and establish no leadership.

The first integration also routed narrow fields and cache-empty matrices through
the dense dispatch. Its negative results are retained. The second integration
restricts dispatch as described above; its control uses the merged trie runtime.
The third integration restores small-matrix bulk frames and bounds dense
updates over partial pending rows.
`enabled` compares caches off/on in the same binary; `control` compares prior
production with caches off; `combined` compares prior production with caches on.
Each campaign independently keeps adjacent AB/BA samples, peak RSS, host context,
all raw outputs and failures. The order audit checks recorded order and the
sequential collector; full-F4 per-process timestamps were not recorded.

| Campaign | Baseline → candidate | Process ratio | Candidate ratio | Work ratio | Charged-payload delta range | Peak RSS A/B KiB |
| --- | --- | ---: | ---: | ---: | --- | --- |
'''
    for (_,label),(metadata,analysis,candidate,work,lo,hi,variation) in zip(campaigns,sweeps):
        rss=analysis['peak_rss_kib'];text+=f"| `{label}` | `{metadata['baseline_source_fingerprint']}` → `{metadata['source_fingerprint']}` | {analysis['family_balanced_geomean']:.4f} | {candidate:.4f} | {work:.6f} | {lo}–{hi} | {rss['A']}/{rss['B']} |\n"
    text+='\nThe following ranges retain all 28 paired process and candidate ratios in each campaign. They describe variation across inputs and AB/BA blocks, not confidence intervals. Each prime has fourteen pairs. The 32003 enabled comparison runs the same arithmetic path on both arms and provides an inert control.\n'
    text+='\n| Campaign | Process pair range | Candidate pair range | p=32003 process / candidate | p=2147483647 process / candidate |\n| --- | --- | --- | ---: | ---: |\n'
    for (_,label),values in zip(campaigns,sweeps):
        variation=values[-1];ratios=variation['process'];times=variation['candidate'];fields=variation['fields']
        text+=f'| `{label}` | {min(ratios):.4f}–{max(ratios):.4f} | {min(times):.4f}–{max(times):.4f} | '+ ' | '.join(f"{mean(fields[p]['process']):.4f} / {mean(fields[p]['candidate']):.4f}"for p in [32003,2147483647])+' |\n'
    composition=sweeps[3][1]['family_balanced_geomean']*sweeps[4][1]['family_balanced_geomean']
    combined=sweeps[5][1]['family_balanced_geomean']
    positive_controls=sum(v[1]['family_balanced_geomean']>1 for v in sweeps[1::3])
    text+=f'\nThe `dense-active` control × enabled process ratios give {composition:.4f}, while its independently collected combined campaign gives {combined:.4f}. This discrepancy exceeds the reported 1–3% point effects. These campaigns cannot attribute a speedup or slowdown to the dense kernel. The default-off process point estimate exceeds 1 in {positive_controls} of {len(sweeps[1::3])} separately collected controls; these observations do not distinguish default-path overhead from host variation and do not establish that the new path is free.\n'
    text+=f'\nAll {56*len(campaigns)} complete-F4 processes / {28*len(campaigns)} matched pairs complete with equal bases. Shared-host variability is retained; these descriptive sweeps establish no overall speedup. The option remains disabled by default. The fastest-open-source milestone and remaining compiler/runtime investigation remain open under #10987.\n'
    if reviewed:
        composition=sweeps[-3][1]['family_balanced_geomean']*sweeps[-2][1]['family_balanced_geomean']
        combined=sweeps[-1][1]['family_balanced_geomean']
        text+=f'\nFor the current integration, control × enabled gives {composition:.4f}, versus {combined:.4f} in the independent combined campaign. Its default-off control also exceeds 1; the attribution limitation remains.\n'
        usage=usage_counts(latest_science,latest_guards,sweeps[-3][0],latest_label,bulk is not None)
        text+='\nSeparate untimed instrumented executions record native usage for every input with the option off and on. Clang and GCC agree exactly, and complete candidate outputs and counters agree with the timed source. These sanitizer executions are coverage observations and are excluded from timings.\n'
        text+='\n| Input | Preparation calls / admitted on | Dense scan calls / packets on | Bulk accepted off / on | Bulk declined off / on |\n| --- | ---: | ---: | --- | --- |\n'
        for case,a,b in usage:text+=f"| {case} | {b['prepares']} / {b['admitted']} | {b['scans']} / {b['updates']} | {a['bulkAccepted']} / {b['bulkAccepted']} | {a['bulkDeclined']} / {b['bulkDeclined']} |\n"
        ratio,flags,rows=selected['selected']
        text+=f'\nThe prefix-update integration preserves bulk-frame eligibility for M31 matrices of at most 128 columns. Dense packets cover bounded pending prefixes after pivot selection or suspension, with a local span bound; rejected packets retain sparse updates. The selected-pivot kernel includes the selection tick in each of 64 updates and resumes the final entry of 4096-entry rows in a second call. Its {len(selected_samples)} invocations / 12 matched pairs give a dense/sparse geometric mean of {ratio:.4f}, with {flags} matched samples below the signal floor. Preparation remains excluded.\n'
        text+='\n| Selected-pivot nonzeros | Dense/sparse ratio |\n| ---: | ---: |\n'
        for n,value in rows:text+=f'| {n} | {value:.4f} |\n'
    if bulk:
        text+='\n| Current combined family | First campaign | Unchanged repeat |\n| --- | ---: | ---: |\n'
        for family,value in sweeps[-1][1]['per_family'].items():text+=f"| {family} | {sweeps[-4][1]['per_family'][family]:.4f} | {value:.4f} |\n"
    else:
        text+='\n| Final combined family | Process ratio |\n| --- | ---: |\n'
        for family,value in sweeps[-1][1]['per_family'].items():text+=f'| {family} | {value:.4f} |\n'
    text+=f'\nAn earlier unselected C-local row-shape cache retains 112 process samples / 56 matched deterministic and sampled comparisons in the experiment capsule. Its process ratios are {shape_ratios["deterministic"]:.4f} (deterministic) and {shape_ratios["sampled"]:.4f} (sampled). Its complete outputs agree and it establishes no benefit; that cache is absent from the implementation. The diagnostic profiles and all native-check snapshots are retained with their exact source manifests.\n'
    for title,path,capsule in [('Kernel and unselected experiments',args.experiments,experiments),('First integration',args.first,first),('Second integration',args.final,final),('Second verification',args.guards,guards),('Trie baseline',args.baseline,baseline),('Earlier production baseline',args.old_baseline,old)]:
        text+=f'\n{title}: [{path.name}](raw/{path.name}), SHA-256 `{capsule.sha256}`, {capsule.count} payloads plus manifest.\n'
    if reviewed:
        for title,path,capsule in [('Prefix-update integration',args.reviewed,reviewed),('Prefix-update verification',args.reviewed_guards,review_guards)]:
            text+=f'\n{title}: [{path.name}](raw/{path.name}), SHA-256 `{capsule.sha256}`, {capsule.count} payloads plus manifest.\n'
    if bulk:
        diagnostic=continuation(bulk,manifests)
        text+='\nA separate default-off diagnostic compares the same continuation drivers in prior production and the current binary over p=65537. Five fixed sizes use adjacent AB then BA; all 40 invocations / 20 pairs are retained, and complete consumed results and counters agree. These kernels exclude parsing and full F4 and cannot by themselves attribute the process-control difference.\n'
        text+='\n| Continuation driver | Current/prior ratio | Paired ratio range | Signal-floor samples |\n| --- | ---: | --- | ---: |\n'
        for name,(ratio,lo,hi,flags,rows)in diagnostic.items():text+=f'| {name} | {ratio:.4f} | {lo:.4f}–{hi:.4f} | {flags} |\n'
        text+='\n| Dimension | Dense Cauchy continuation | Sparse continuation |\n| ---: | ---: | ---: |\n'
        for i,n in enumerate([64,128,256,512,1024]):text+=f"| {n} | {diagnostic['matrixFrame'][4][i][1]:.4f} | {diagnostic['matrixSparse'][4][i][1]:.4f} |\n"
    if bulk:
        first_composition=sweeps[-6][1]['family_balanced_geomean']*sweeps[-5][1]['family_balanced_geomean']
        first_combined=sweeps[-4][1]['family_balanced_geomean']
        text+=f'\nThe first bulk-integration control × enabled ratios give {first_composition:.4f}, versus {first_combined:.4f} in its combined campaign.\n'
        text+='\nThe first bulk-integration campaigns are strongly inconclusive: their process-control ratios do not compose. One unchanged repeat of all three campaigns is retained separately as `dense-bulk/repeat`; neither campaign is filtered or pooled.\n'
        text+='\nBulk elimination now preserves ordinary frame eligibility. Its known canonical monic rows determine the same optional preparation work and packed-payload reservations as the reference; refused preparations charge zero. Unused cache buffers are not materialized. Consequently `allocatedBytes` here records the shared logical packed-payload reservation rather than actual process allocation; peak RSS is recorded separately, and the factory-call counts describe actual materializations. Exact public-dispatch comparisons cover 128/129/174 columns, 127/128 entries, independent targets and parent work/byte boundaries. A separate 512/1024-reducer comparison checks acceptance and rejection when preparation charges cross the fixed bulk work quantum. Out-of-range continuation rows skip the factory call.\n'
        for title,path,capsule in [('Bulk integration',args.bulk,bulk),('Bulk verification',args.bulk_guards,bulk_guards)]:
            text+=f'\n{title}: [{path.name}](raw/{path.name}), SHA-256 `{capsule.sha256}`, {capsule.count} payloads plus manifest.\n'
    if verified:
        text+='\nFinal verification adds native normalization/refusal and continuation checks and corrects the per-frame decline contract. The verifier checks that the measured and final runtime sources differ only in comments in the two contract files; executable text is unchanged. Timings remain attached to their original source manifests, and no further unchanged timing repeat was taken.\n'
        text+=f'\nFinal verification: [{args.verified_guards.name}](raw/{args.verified_guards.name}), SHA-256 `{verified.sha256}`, {verified.count} payloads plus manifest.\n'
    text+='\nRegenerate with `python3 scripts/bench/groebner_dense_report.py '+' '.join('--'+name+' '+str(getattr(args,name.replace('-','_')))for name in ['experiments','first','final','baseline','old-baseline','guards','report'])+ ((' --reviewed '+str(args.reviewed)+' --reviewed-guards '+str(args.reviewed_guards))if reviewed else '')+ ((' --bulk '+str(args.bulk)+' --bulk-guards '+str(args.bulk_guards))if bulk else '')+ ((' --verified-guards '+str(args.verified_guards))if verified else '')+' --check`. Add `--current` to require the present runtime and verification sources. Collectors include host-specific commands and paths; adapt those locations when replaying on another host.\n'
    if args.check:require(args.report.read_text()==text,'report differs from verified data')
    else:args.report.write_text(text)
    print('dense-pivot report verified'if args.check else'dense-pivot report generated')


if __name__=='__main__':
    main()
