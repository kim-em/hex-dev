#!/usr/bin/env python3
"""Verify retained critical-pair retirement experiments and regenerate their report."""
import argparse
import hashlib
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import source,require,mean
from scripts.bench.groebner_avx512_report import listing
from scripts.bench.groebner_comparator_report import msolve


def campaign(capsule,label,name):
    prefix=label+'/'+name
    a,b=source(capsule,'baseline'),source(capsule,label)
    meta=capsule.json(prefix+'/metadata.json');recorded=capsule.json(prefix+'/analysis.json')
    require(meta['source_unchanged'] and meta['threads']==1 and
            meta['source_manifest']==b['source_manifest'] and meta['baseline_manifest']==a,'campaign source/configuration differs')
    require(meta['binary_sha256']==meta['binary_sha256_after']=={'A':a['binary_sha256']['compute'],'B':b['binary_sha256']['compute']},'campaign executable differs')
    require(a['compilers']==b['compilers'] and a['native_options']==b['native_options'],'compiler/native options differ')
    for name,digest in meta['input_sha256'].items():
        require(hashlib.sha256(capsule.read(prefix+'/inputs/'+name)).hexdigest()==digest,'campaign input differs')
    samples=meta['samples'];index={(r['case'],r['block'],r['arm']):r for r in samples}
    order=[r['case']for r in samples if r['block']==0 and r['arm']=='A']
    require(len(index)==len(samples)==56 and len(set(order))==14,'campaign coverage differs')
    require([(r['case'],r['block'],r['arm'])for r in samples]==[(case,block,arm)for block in [0,1]for case in order for arm in (['A','B']if block==0 else ['B','A'])],'campaign adjacency differs')
    process=[];candidate=[];work=[];pairs=[];families={}
    for case in order:
        for block in [0,1]:
            rows=[index[case,block,arm]for arm in ['A','B']];outputs=[]
            require(all(r['status']=='ok' and r['returncode']==0 and r['complete_basis_equal']for r in rows),'campaign failed')
            require(rows[0]['family']==rows[1]['family'] and rows[0]['p']==rows[1]['p'],'paired configuration differs')
            for arm,row in zip(['A','B'],rows):
                value=capsule.json(f'{prefix}/{case}-b{block}-{arm}.stdout')
                require(value['kind']=='unchecked_candidate' and value['order']=='grevlex' and value['scheduling']==row['scheduling']=='degree' and value['p']==row['p'],'output contract differs')
                stats=dict(row['statistics']);require(stats.pop('candidate_nanos')==value['candidateNanos'] and stats==value['statistics'],'output statistics differ')
                require(int(capsule.text(f'{prefix}/{case}-b{block}-{arm}.rss'))==row['peak_rss_kib'],'RSS record differs')
                outputs.append(value)
            process.append(rows[1]['wall_nanos']/rows[0]['wall_nanos'])
            candidate.append(outputs[1]['candidateNanos']/outputs[0]['candidateNanos'])
            for values,key in [(work,'work'),(pairs,'pairs')]:values.append(outputs[1]['statistics'][key]/outputs[0]['statistics'][key])
            for value in outputs:value.pop('candidateNanos');value.pop('statistics')
            require(outputs[0]==outputs[1],'complete basis/metadata differ')
            families.setdefault(rows[0]['family'],[]).append(process[-1])
    require({r['p']for r in samples}=={32003,2147483647} and len(families)==7 and all(len(v)==4 for v in families.values()),'balanced field/family coverage differs')
    require(recorded['samples']==56 and recorded['complete_bases_equal']==28 and recorded['timeouts']==recorded['failed_processes']==0,'recorded coverage differs')
    require(math.isclose(recorded['geomean'],mean(process),rel_tol=1e-12) and
            math.isclose(recorded['family_balanced_geomean'],mean([mean(v)for v in families.values()]),rel_tol=1e-12),'recorded aggregate differs')
    require(all(math.isclose(recorded['per_family'][k],mean(v),rel_tol=1e-12)for k,v in families.items()),'recorded family ratio differs')
    rss={arm:max(r['peak_rss_kib']for r in samples if r['arm']==arm)for arm in ['A','B']}
    require(rss==recorded['peak_rss_kib'],'recorded memory differs')
    return dict(process=mean(process),candidate=mean(candidate),work=mean(work),pairs=mean(pairs),minimum=min(process),maximum=max(process),families=recorded['per_family'],cpu=meta['cpu'],rss=rss)


def code(text):
    """Remove nested Lean comments from this string-free source file."""
    require('"'not in text,'comment comparison requires string-free source')
    result=[];i=0;depth=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif not depth and text.startswith('--',i):
            end=text.find('\n',i);i=len(text)if end<0 else end
        else:
            if not depth:result.append(text[i])
            i+=1
    require(depth==0,'unterminated source comment')
    return ''.join(''.join(result).split())


def verify_guards(guards,science):
    identity=guards.json('identity.json')
    for label,key in [('runtime','source_fingerprint'),('checks','checks_fingerprint')]:
        text=guards.text(label+'.manifest');require(hashlib.sha256(text.encode()).hexdigest()[:12]==identity[key],'verification manifest differs')
        for path,oid in listing(text).items():
            data=guards.read(label+'-sources/'+path)
            require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,'verification source differs')
    native=guards.json('native-status.json');full=guards.json('full-status.json')
    require(len(native)==2 and {r['name']for r in native}=={'clang','gcc'} and len(full)==9,'verification coverage differs')
    for row in native+full:require(row['exit_code']==0 and all(row[k]==v for k,v in identity.items()),'failed/stale verification')
    require(all(set(r['variants'])=={'Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder'} and set(r['sanitize'])=={'address','undefined'}for r in native),'native variants differ')
    require('clang version 23.1.3' in guards.text('native-clang.log') and
            '16.2.0' in guards.text('native-gcc.log'),'sanitizer compiler identity differs')
    before=source(science,'active-list');after=source(guards,'reviewed')
    require(before['source_manifest']==guards.text('runtime.manifest'),'verified algorithm differs from timing')
    a,b=listing(before['source_manifest']),listing(after['source_manifest'])
    require(set(a)==set(b) and {p for p in a if a[p]!=b[p]}=={'HexGroebner/Pairs.lean'},'post-measurement runtime change differs')
    require(code(science.text('active-list/root-sources/HexGroebner/Pairs.lean'))==code(guards.text('reviewed/root-sources/HexGroebner/Pairs.lean')),'executable pair logic changed')
    require(all(after['binary_sha256'][k]==v for k,v in before['binary_sha256'].items()),'reviewed executables differ from timings')
    require('Build completed successfully' in guards.text('review-f4.log'),'targeted guard build failed')
    reviewed=guards.json('review-identity.json');text=guards.text('review-checks.manifest')
    require(hashlib.sha256(text.encode()).hexdigest()==reviewed['checks_manifest_sha256'] and
            hashlib.sha256(text.encode()).hexdigest()[:12]==reviewed['checks_fingerprint'] and
            after['source_fingerprint']==reviewed['source_fingerprint'] and
            hashlib.sha256(after['source_manifest'].encode()).hexdigest()==reviewed['source_manifest_sha256'],'reviewed identities differ')
    for path,oid in listing(text).items():
        data=guards.read('review-checks-sources/'+path)
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,'reviewed test source differs')
    require('retirementPairs\ndid not evaluate' in guards.text('mutations/reverse-guard-build.log'),'reversed-divisibility mutant was not detected')
    reverse=guards.json('mutations/reverse-check/status.json')
    reverse_manifest=source(guards,'mutations/reverse')
    require(not reverse['detected'] and len(reverse['records'])==128 and
            reverse['binary_sha256']==reverse_manifest['binary_sha256']['compute'] and
            reverse['mutant_source_fingerprint']==reverse_manifest['source_fingerprint'],'reversed mutation binding differs')
    for row in reverse['records']:
        case=row['case'];require(row['exit_code']==0 and row['basis_equal'],'reversed mutation changed a fresh basis')
        require(row['input_sha256']==hashlib.sha256(guards.read(f'random/{case}.json')).hexdigest(),'reversed mutation input differs')
        output=guards.json(f'mutations/reverse-check/{case}.stdout')
        require(output['basis']==guards.json(f'random/{case}-degree-compute.stdout')['basis'],'reversed mutation output differs')
    final=guards.json('review-full-status.json')
    require(len(final)==9 and all(r['exit_code']==0 and all(r[k]==v for k,v in reviewed.items())for r in final),'final project checks failed')
    mutant=guards.json('mutations/always-check/status.json');last=mutant['records'][-1];case=last['case']
    require(mutant['detected'] and last['exit_code']==0 and not last['basis_equal'],'over-retirement mutant was not detected')
    require(last['input_sha256']==hashlib.sha256(guards.read('mutations/always-check/counterexample.json')).hexdigest() and
            guards.read('mutations/always-check/counterexample.json')==guards.read(f'random/{case}.json'),'mutation input differs')
    bad=guards.json(f'mutations/always-check/{case}.stdout');good=guards.json(f'random/{case}-degree-compute.stdout')
    require(bad['kind']=='unchecked_candidate' and bad['basis']!=good['basis'],'mutation did not produce a wrong basis')
    require(code(guards.text('mutations/always-Pairs.lean'))==code(science.text('active-list/root-sources/HexGroebner/Pairs.lean')).replace('iflcm==athen','iftruethen',1),'over-retirement mutation differs')
    corpus=guards.json('corpus-status.json')
    require(len(corpus)==4536 and all(r['basis_equal']for r in corpus),'corpus comparison failed')
    require('567 unique reduced bases match SymPy' in guards.text('oracles.log') and
            '567 reduced bases match Singular' in guards.text('oracles.log'),'independent oracle coverage differs')
    verify_random(guards,before)
    return identity,after,reviewed


def verify_random(guards,manifest):
    from scripts.oracle.groebner_sympy import check
    status=guards.json('random/status.json');rows=status['records']
    require(status['seed']==1098726 and status['source_fingerprint']==manifest['source_fingerprint'] and len(rows)==512,'fresh-system coverage differs')
    require({(r['case'],r['scheduling'],r['name'])for r in rows}=={(case,scheduling,name)for case in range(128)for scheduling in ['degree','sugar']for name in ['compute','compute-reference']},'fresh-system profiles differ')
    expected={}
    for row in rows:
        case=row['case'];input_name=f'random/{case}.json'
        require(row['exit_code']==0 and row['basis_equal'] and row['binary_sha256']==manifest['binary_sha256'][row['name']] and
                row['input_sha256']==hashlib.sha256(guards.read(input_name)).hexdigest(),'fresh-system binding differs')
        value=guards.json(f"random/{case}-{row['scheduling']}-{row['name']}.stdout")
        require(value['kind']=='unchecked_candidate' and value['scheduling']==row['scheduling'],'fresh-system output contract differs')
        if case not in expected:expected[case]=check({**guards.json(input_name),'basis':value['basis']})
        require(value['basis']==expected[case],'fresh-system independent basis differs')


def verify_rebase(capsule,before,review_identity):
    after=source(capsule,'current');a,b=listing(before['source_manifest']),listing(after['source_manifest'])
    require(set(a)==set(b) and {p for p in a if a[p]!=b[p]}=={'lakefile.lean','scripts/bench/groebner_freeze.py'},'rebased runtime change differs')
    require(after['binary_sha256']==before['binary_sha256'],'rebased executables differ')
    require(all(after['compilers'][k]==v for k,v in before['compilers'].items()) and
            after['compilers']['other_native']==after['compilers']['native'],'rebased compiler differs')
    require(after['native_options']=={'hexGroebnerAVX512':False,'hexGroebnerCC':None},'rebased defaults differ')
    identity=capsule.json('identity.json')
    require(identity['source_fingerprint']==after['source_fingerprint'] and
            identity['source_manifest_sha256']==hashlib.sha256(after['source_manifest'].encode()).hexdigest() and
            identity['checks_manifest_sha256']==review_identity['checks_manifest_sha256'],'rebased identity differs')
    rows=capsule.json('full-status.json')
    require(len(rows)==9 and all(r['exit_code']==0 and all(r[k]==v for k,v in identity.items())for r in rows),'rebased project checks failed')
    header=capsule.json('header-deps-status.json')
    require([r['label']for r in header]==['initial','changed','restored'] and all(r['exit_code']==0 for r in header),'header dependency probe failed')
    require(all(r['mtime_before']!=r['mtime_after']for r in header[1:]) and
            len({r['object_sha256']for r in header})==1 and
            capsule.json('object-control.json')['monomial_hit.o']==header[0]['object_sha256'],'header rebuild/object control differs')
    return identity,after


def verify_review(capsule,before,guards):
    after=source(capsule,'current');a,b=listing(before['source_manifest']),listing(after['source_manifest'])
    require(set(a)==set(b) and {p for p in a if a[p]!=b[p]}=={'HexGroebner/Pairs.lean'},'final review runtime change differs')
    require(code(capsule.text('current/root-sources/HexGroebner/Pairs.lean'))==code(guards.text('reviewed/root-sources/HexGroebner/Pairs.lean')) and
            after['binary_sha256']==before['binary_sha256'],'final review changed executable logic')
    identity=capsule.json('identity.json');text=capsule.text('checks.manifest')
    require(identity['source_fingerprint']==after['source_fingerprint'] and
            identity['source_manifest_sha256']==hashlib.sha256(after['source_manifest'].encode()).hexdigest() and
            identity['checks_manifest_sha256']==hashlib.sha256(text.encode()).hexdigest(),'final review identity differs')
    for path,oid in listing(text).items():
        data=capsule.read('checks-sources/'+path)
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,'final review check source differs')
    rows=capsule.json('full-status.json')
    require(len(rows)==9 and all(r['exit_code']==0 and all(r[k]==v for k,v in identity.items())for r in rows),'final review project checks failed')
    meta=capsule.json('mutation/metadata.json');inp=capsule.json('mutation/input.json')
    require(inp==guards.json('mutations/always-check/minimal-f2-input.json') and
            meta['good_manifest']['binary_sha256']==before['binary_sha256'],'minimized mutation source differs')
    records=meta['records'];require([r['label']for r in records]==['good','bad'],'minimized mutation coverage differs')
    expected_hashes=[before['binary_sha256']['compute'],guards.json('mutations/always-check/status.json')['binary_sha256']]
    for row,digest in zip(records,expected_hashes):
        require(row['exit_code']==0 and row['binary_sha256_before']==row['binary_sha256_after']==digest and
                row['input_sha256']==hashlib.sha256(capsule.read('mutation/input.json')).hexdigest(),'minimized mutation executable binding differs')
    good,bad=[capsule.json('mutation/'+label+'.stdout')for label in ['good','bad']]
    from scripts.oracle.groebner_sympy import check
    check({**inp,'basis':good['basis']})
    require(good['kind']==bad['kind']=='unchecked_candidate' and [[[1,0,2],1]]in good['basis'] and
            [[[1,0,2],1]]not in bad['basis'],'minimized mutation does not miss xz squared')
    return identity


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['tree','array','guards','rebased','review','report']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--check',action='store_true');p.add_argument('--current',action='store_true');args=p.parse_args()
    tree,array,guards=[Capsule(path)for path in [args.tree,args.array,args.guards]]
    require(source(tree,'baseline')==source(array,'baseline'),'prototype baselines differ')
    inputs=[capsule.json(label+'/'+name+'/metadata.json')['input_sha256']for capsule,label in [(tree,'active-pairs'),(array,'active-list')]for name in ['f4','f4-repeat']]
    require(all(value==inputs[0]for value in inputs),'prototype input suites differ')
    runs=[(label,name,campaign(capsule,label,name))for capsule,label in [(tree,'active-pairs'),(array,'active-list')]for name in ['f4','f4-repeat']]
    identity,reviewed,review_identity=verify_guards(guards,array)
    rebased=Capsule(args.rebased);current_identity,current_manifest=verify_rebase(rebased,reviewed,review_identity)
    review=Capsule(args.review);final_identity=verify_review(review,current_manifest,guards)
    comparison,comparison_meta=msolve(guards,"reviewed")
    engine=guards.json("msolve-engine.json")
    require(engine["engine_sha256"]==comparison_meta["msolve_engine_sha256"] and "clang version 23.1.3" in engine["engine_comment"],"comparator compiler identity differs")
    require(guards.text("msolve-upstream.txt").split()[0]==comparison_meta["msolve_commit"],"comparator upstream revision differs")
    compiled=source(array,'active-list');versions={k:v['version'].splitlines()[0]for k,v in compiled['compilers'].items()}
    host=array.json('active-list/f4/metadata.json')['host']
    if args.current:
        current=source_identity();require(all(current[k]==v for k,v in final_identity.items()if k!='source_commit'),'current source/check identities differ')
    lines=['# Critical-pair retirement','',
           'A basis entry whose leading monomial is divisible by a newer leading monomial retires from future pair generation. '
           'Its polynomial remains a reducer, its stable index and derivations remain valid, and existing queued obligations remain. '
           'Installation considers the connecting pair before retirement. The selected implementation iterates an ascending active-index array, rather than scanning every old basis entry.','',
           'Pair coverage still requires a producer proof. Its dependency order includes LCM, maximum index and a final level accounting for equal-LCM groups and prior retirement-chain depth. '
           'Independent final certification continues to check every required final S-pair and both ideal containments. No correctness-completion or fastest-open-source milestone is claimed.','',
           '## Matched observations','',
           f"Host `{host}`; production native C: {versions['native']}; Lean-generated C: {versions['lean']}; toolchain `{compiled['toolchain']}`. "
           'Both prototypes use the same compilers as their baseline, with AVX-512 disabled and one algorithm thread. '
           'The fourteen fixed grevlex inputs cover seven families at 32003 and 2147483647 with degree scheduling and complete unchecked-candidate output. '
           'Each campaign uses adjacent AB then BA on an automatically leased CPU. Candidate production excludes certification and kernel checking. '
           'Each prototype has exactly one unchanged repeat; campaigns remain separate and all completed samples are retained.','',
           '| Implementation / campaign | CPU | Process B/A | Candidate B/A | Work B/A | Considered pairs B/A | Process pair range | Peak RSS A/B (KiB) |',
           '|---|---:|---:|---:|---:|---:|---:|---:|']
    for label,name,r in runs:lines.append(f"| {label} / {name} | {r['cpu']} | {r['process']:.6f} | {r['candidate']:.6f} | {r['work']:.6f} | {r['pairs']:.6f} | {r['minimum']:.6f}–{r['maximum']:.6f} | {r['rss']['A']}/{r['rss']['B']} |")
    lines+=['','All 224 processes (112 pairs) complete with equal canonical bases and no failures or timeouts. '
            'Statistics can change because pair generation and matrix work change. These campaigns do not establish an overall timing benefit at this resolution. '
            'The array choice rests on deterministic reductions in considered pairs and charged work, rather than a timing ranking against the tree implementation. No comparator leadership is claimed.','',
            '| Family (process B/A) | Tree first | Tree repeat | Array first | Array repeat |','|---|---:|---:|---:|---:|']
    for family in runs[0][2]['families']:lines.append('| '+family+' | '+' | '.join(f"{r['families'][family]:.6f}"for _,_,r in runs)+' |')
    lines+=['','The array route avoids generating retired pairs; its considered-pair count is lower rather than recording those pairs as GM rejections. '
            'Katsura regresses in both array campaigns; the first observation prompted retained ABBA cycle profiles. Those short profiles do not establish a consistent new bottleneck. '
            'Memory, inputs, complete outputs, counters and host activity remain in the raw capsules. No additional unchanged timing repeats were collected.','',
            '## Remaining comparator gap','',
            f"The reviewed array executable remains {comparison['family_balanced_geomean']:.6f}× slower than msolve in family-balanced process time on this suite. "
            'All 56 matched processes complete with 28 equal full-basis pairs; their failures, memory and raw samples are retained. '
            f"msolve revision `{comparison_meta['msolve_commit']}` uses Clang 23.1.3, native CPU tuning, deterministic elimination (`-l 2`), full reduced output (`-g 2`) and one thread. "
            f"Individual process ratios range from {comparison['minimum']:.6f} to {comparison['maximum']:.6f}. "
            'Hex retains the host native compiler and runtime dispatch with AVX-512 off. This separate matched comparison is not pooled with prototype comparisons, and does not cover the full acceptance suite.','',
            '## Verification','',
            f"All twelve Clang 23.1.3/GCC 16.2.0 ASan+UBSan variants and all nine project checks pass at runtime `{identity['source_fingerprint']}`, checks `{identity['checks_fingerprint']}`. "
            'They include the executable/theory build, independent oracles, native/portable drivers, benchmark verification, DAG, phase, release-manifest and source checks. '
            'All 567 unique emitted bases match SymPy and Singular; 4,536 native/portable/default/serial computations match the corpus. '
            'A further fixed seed produces 128 fresh systems, with 512 native/portable and degree/sugar computations matching independently computed SymPy bases.','',
            f"The reviewed runtime `{reviewed['source_fingerprint']}` changes only pair-module documentation after measurement, reproducing both measured executable hashes. "
            'Additional Lean guards check a nonzero omitted S-polynomial, connecting obligations, the required ordinary-F2 term `xz²`, and both retired and Buchberger-to-GM frontier-gap resumptions. '
            'All nine project checks also pass with the final guard sources. Their source and logs are retained separately from the earlier verification snapshot.','',
            f"Rebased runtime `{current_manifest['source_fingerprint']}` incorporates the default-preserving compiler-selection setting, compiler-command provenance changes and the monomial target’s missing trie-header dependency. "
            'Only Lake/freeze metadata differs from the reviewed runtime; all three executables remain byte-identical. '
            'All nine checks pass again after rebasing. Editing and restoring the included header rebuilds the monomial object and preserves its original hash.','',
            f"Final runtime `{final_identity['source_fingerprint']}` makes the UPDATE depth convention explicit, with active depth zero and each removed index one greater than its replacement. "
            'The runtime edit is documentation only, with all three executable hashes preserved. Final guards additionally compare the four-generator system with unpruned Buchberger and exercise repeated installation; all nine checks pass again.','',
            'The reversed-divisibility mutation preserves the tested fresh bases: losing retirement can merely lose pruning. '
            'The targeted queue-obligation guard separately checks the retirement direction. A second mutation retiring unrelated entries produces a wrong basis, independently rejected by SymPy. '
            'Its minimized ordinary-F2 system `yz, xy+xz, y²` misses `xz²`; direct regressions cover both schedules. Mutation attempts and failures are retained.','']
    at=lines.index('## Verification')
    lines[at:at]=['| Comparator family | Hex/msolve process |','|---|---:|',*[f'| {family} | {ratio:.6f} |'for family,ratio in comparison['per_family'].items()],'']
    for path,c in [(args.tree,tree),(args.array,array),(args.guards,guards),(args.rebased,rebased),(args.review,review)]:lines.append(f'`{path.name}`: SHA-256 `{c.sha256}`.')
    lines+=['',f'Regenerate historical evidence with `python3 scripts/bench/groebner_retirement_report.py --tree {args.tree} --array {args.array} --guards {args.guards} --rebased {args.rebased} --review {args.review} --report {args.report} --check`. Add `--current` to require the present checkout to match the final verification sources.','']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report is stale')
    else:args.report.write_text(text)


if __name__=='__main__':main()
